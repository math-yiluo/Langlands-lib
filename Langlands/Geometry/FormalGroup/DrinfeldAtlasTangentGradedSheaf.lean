import Langlands.Geometry.FormalGroup.DeligneAffinePiSheaf
import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentLine
import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentUniformizer

/-! # The graded tangent line datum of a special formal atlas -/

noncomputable section

universe u v s

namespace Langlands.DeligneFormalSpace

open _root_.CategoryTheory _root_.AlgebraicGeometry

variable {A : Type v} [CommRing A] {V : Type v} [AddCommGroup V] [Module A V]
variable {d : ℕ} [NeZero d] (P : ZMod d → Module.End A V)
variable (hDiag : ∀ i, P i * P i = P i) (hOff : ∀ {i k}, k ≠ i → P i * P k = 0)
variable (hSum : (∑ i : ZMod d, P i) = 1)
variable (t : Module.End A V) (a : A) (hPow : t ^ d = algebraMap A (Module.End A V) a)
variable (hStep : ∀ (i : ZMod d) (x : LinearMap.range (P i)), t x.val ∈ LinearMap.range (P (i + 1)))

local notation "R" => CommRingCat.of A
local notation "M" => ModuleCat.of A V
local notation "W" => (fun i : ZMod d => ModuleCat.of A (LinearMap.range (P i)))

private def projectorInclusion (i : ZMod d) : W i ⟶ M :=
  ModuleCat.ofHom (LinearMap.range (P i)).subtype

private def projectorProjection (i : ZMod d) : M ⟶ W i := ModuleCat.ofHom (P i).rangeRestrict

local notation "j" => projectorInclusion P
local notation "q" => projectorProjection P

include hDiag in
omit [NeZero d] in
private theorem projectorInclusion_projection (i : ZMod d) : j i ≫ q i = 𝟙 (W i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change P i y = x.val at hy
  change P i x.val = x.val
  rw [← hy]
  exact LinearMap.congr_fun (hDiag i) y

include hOff in
omit [NeZero d] in
private theorem projectorInclusion_projection_ne {i k : ZMod d} (hk : k ≠ i) : j k ≫ q i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change P k y = x.val at hy
  change P i x.val = 0
  rw [← hy]
  exact LinearMap.congr_fun (hOff hk) y

include hSum in
private theorem projectorSum_projection_inclusion : (∑ i : ZMod d, q i ≫ j i) = 𝟙 M := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  exact hSum

include hPow in
omit [NeZero d] in
private theorem projectorOperator_pow :
    (End.of (ModuleCat.ofHom t) : End M) ^ d = End.of (ModuleCat.ofHom (a • LinearMap.id)) := by
  apply (ModuleCat.endRingEquiv M).injective
  rw [map_pow]
  exact hPow

private def projectorStep (i : ZMod d) : W i ⟶ W (i + 1) :=
  ModuleCat.ofHom ((t.comp (LinearMap.range (P i)).subtype).codRestrict _ (hStep i))

omit [NeZero d] in
private theorem projectorStep_inclusion (i : ZMod d) :
    j i ≫ ModuleCat.ofHom t = projectorStep P t hStep i ≫ j (i + 1) := rfl

/-- The affine graded sheaf associated to orthogonal projectors and a cyclic operator. -/
def affineGradedPiSheafOfProjectors :
    GradedPiSheaf d (Spec R).sheaf (schemeScalar (Spec R) ((Scheme.ΓSpecIso R).inv a)) :=
  affineGradedPiSheaf («R» := R) («M» := M) («d» := d) («W» := W)
    a (End.of (ModuleCat.ofHom t)) (projectorOperator_pow t a hPow)
    j q (projectorInclusion_projection P hDiag) (fun h => projectorInclusion_projection_ne P hOff h)
    (projectorSum_projection_inclusion P hSum) (projectorStep P t hStep) (projectorStep_inclusion P t hStep)

/-- The homogeneous sheaves identify with the sheaves of the projector images. -/
def affineGradedPiSheafOfProjectorsComponentIso (i : ZMod d) :
    tilde (W i) ≅ (affineGradedPiSheafOfProjectors P hDiag (@hOff) hSum t a hPow hStep).componentSheaf i :=
  affineGradedPiSheafComponentIso («R» := R) («M» := M) («d» := d) («W» := W)
    a (End.of (ModuleCat.ofHom t)) (projectorOperator_pow t a hPow)
    j q (projectorInclusion_projection P hDiag) (fun h => projectorInclusion_projection_ne P hOff h)
    (projectorSum_projection_inclusion P hSum) (projectorStep P t hStep) (projectorStep_inclusion P t hStep) i

/-- A split cyclic operator whose projector images give affine line sheaves gives a line datum. -/
def affineLinePiSheafOfProjectors (hLine : ∀ i : ZMod d, IsLineSheaf (Spec R) (tilde (W i))) :
    LinePiSheaf d (Spec R) ((Scheme.ΓSpecIso R).inv a) where
  graded := affineGradedPiSheafOfProjectors P hDiag (@hOff) hSum t a hPow hStep
  line i := IsLineSheaf.of_iso (S := Spec R)
    (affineGradedPiSheafOfProjectorsComponentIso P hDiag (@hOff) hSum t a hPow hStep i) (hLine i)

end Langlands.DeligneFormalSpace

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory
  _root_.AlgebraicGeometry DeligneFormalSpace ModuleLaw

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentLineDatumLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance atlasTangentLineDatumDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u,max u v} 𝒪[K] π} (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj)
variable (X : SpecialAtlas K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "B₀" => CommAlgCat.of B.obj B.obj
local notation "V" => X.atlas.tangentSubmodule B₀
local notation "P" => tangentProjector ι χ ψ X
local notation "W" => tangentComponent ι χ ψ X
local notation "ρ" => BasicAtlas.OrderAction.tangentAlgebraAction X.order B₀
local notation "idx" => RingEquiv.symm (ZMod.finEquiv (CentralSimple.reducedDegree K D))
local notation "R" => CommRingCat.of B.obj
local notation "πB" => algebraMap 𝒪[K] B.obj π

variable (σ : L ≃ₐ[K] L) (uD : Dˣ)
  (hPow : (uD : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uD : D) * ι a = ι (σ a) * (uD : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "T" => (ρ) (drinfeldIntegralUniformizer uD hPow)

set_option maxHeartbeats 600000 in
private theorem sum_tangentProjector_zmod : (∑ i : ZMod d, P (idx i)) = 1 :=
  (Equiv.sum_comp (idx).toEquiv P).trans (sum_tangentProjector ι χ ψ X)

set_option maxHeartbeats 700000 in
include hComm hσ in
private theorem tangentUniformizer_mem_succ_zmod (i : ZMod d) (x : W (idx i)) :
    T x.val ∈ W (idx (i + 1)) := by
  have hi : (idx) (i + 1) = (idx) i + 1 := by rw [map_add, map_one]
  let mem (k : Fin d) : Prop := T x.val ∈ W k
  have hx : mem ((idx) i + 1) := tangentUniformizer_mem_succ ι χ ψ X σ uD hPow hComm hσ (idx i) x
  exact (congrArg mem hi).mpr hx

set_option backward.isDefEq.respectTransparency.types false in
set_option maxHeartbeats 900000 in
/-- The compatible tangent module gives an affine Drinfeld graded line datum. -/
def tangentLinePiSheaf : LinePiSheaf d (Spec R) ((Scheme.ΓSpecIso R).inv πB) := by
  let Q (i : ZMod d) : Module.End B.obj V := P (idx i)
  have hLine (i : ZMod d) : IsLineSheaf (Spec R) (tangentComponentSheaf ι χ ψ X (idx i)) :=
    tangentComponentSheaf_isLine ι χ ψ X (idx i)
  refine affineLinePiSheafOfProjectors (A := B.obj) («V» := V) Q ?_ ?_
    (sum_tangentProjector_zmod ι χ ψ X) T πB (tangentUniformizer_pow ι X uD hPow) ?_ ?_
  · exact fun i => tangentProjector_mul_same ι χ ψ X (idx i)
  · exact fun h => tangentProjector_mul_ne ι χ ψ X ((idx).injective.ne h.symm)
  · exact tangentUniformizer_mem_succ_zmod ι χ ψ X σ uD hPow hComm hσ
  · exact hLine

end Langlands.FormalGroup.LocalDivision.SpecialAtlas

import Langlands.Geometry.FormalGroup.DeligneAffineLineSheaf
import Langlands.Geometry.FormalGroup.DeligneAffinePiSheaf
import Langlands.Geometry.FormalGroup.DrinfeldTangentStalkLine

/-! # The actual affine tangent line sheaf of a special formal order module -/

noncomputable section

namespace Langlands.FormalGroup.LocalDivision

open ValuativeRel CentralDivision CentralSimple _root_.CategoryTheory _root_.AlgebraicGeometry
  DeligneFormalSpace

universe u v s

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance tangentLineSheafLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance tangentLineSheafDegree : NeZero (CentralSimple.reducedDegree K D) :=
  ⟨(reducedDegree_pos K D).ne'⟩

variable {κ : Type u} [Field κ] [Algebra 𝒪[K] κ] [Algebra 𝓀[K] κ]
  [IsScalarTower 𝒪[K] 𝓀[K] κ]
variable (χ : IsLocalRing.ResidueField (SubfieldIntegerRing K D ι) →ₐ[𝓀[K]] κ)
variable {π : 𝒪[K]} {B : Nilp.{u, max u v} 𝒪[K] π}
variable (ψ : κ →ₐ[𝒪[K]] Nilp.Reduction π B.obj) (Y : SpecialModule K D ι B.obj)

local notation "d" => CentralSimple.reducedDegree K D
local notation "idx" => RingEquiv.symm (ZMod.finEquiv (CentralSimple.reducedDegree K D))
local notation "V" => (Fin d → B.obj)
local notation "P" => drinfeldTangentProjector ι Y.unramified χ ψ Y.order
local notation "W" => drinfeldTangentComponent ι Y.unramified χ ψ Y.order
local notation "R" => CommRingCat.of B.obj
local notation "X" => Spec R
local notation "M" => ModuleCat.of B.obj V
local notation "summand" => (fun i : ZMod d => ModuleCat.of B.obj (W (idx i)))

private def tangentInclusion (i : ZMod d) : summand i ⟶ M :=
  ModuleCat.ofHom (W (idx i)).subtype

private def tangentProjection (i : ZMod d) : M ⟶ summand i :=
  ModuleCat.ofHom (P (idx i)).rangeRestrict

local notation "j" => tangentInclusion ι χ ψ Y
local notation "p" => tangentProjection ι χ ψ Y

private theorem tangentInclusion_projection (i : ZMod d) : j i ≫ p i = 𝟙 (summand i) := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change P (idx i) y = x.val at hy
  change P (idx i) x.val = x.val
  rw [← hy]
  exact congrArg (fun f : Module.End B.obj V => f y)
    (drinfeldTangentProjector_mul_same ι Y.unramified χ ψ Y.order (idx i))

private theorem tangentInclusion_projection_ne {i k : ZMod d} (hk : k ≠ i) :
    j k ≫ p i = 0 := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  obtain ⟨y, hy⟩ := x.property
  change P (idx k) y = x.val at hy
  change P (idx i) x.val = 0
  rw [← hy]
  exact congrArg (fun f : Module.End B.obj V => f y)
    (drinfeldTangentProjector_mul_ne ι Y.unramified χ ψ Y.order ((idx).injective.ne hk.symm))

private theorem tangentSum_projection_inclusion :
    (∑ i : ZMod d, p i ≫ j i) = 𝟙 M := by
  apply ModuleCat.hom_ext
  rw [ModuleCat.hom_sum]
  change (∑ i : ZMod d, P (idx i)) = 1
  exact (Equiv.sum_comp (idx).toEquiv P).trans (sum_drinfeldTangentProjector ι Y.unramified χ ψ Y.order)

variable (σ : L ≃ₐ[K] L) (uniformizer : Dˣ)
  (hPow : (uniformizer : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uniformizer : D) * ι a = ι (σ a) * (uniformizer : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "t" => Y.order.tangentAction (drinfeldIntegralUniformizer uniformizer hPow)
local notation "aπ" => algebraMap 𝒪[K] B.obj π

private theorem uniformizerPower :
    (End.of (ModuleCat.ofHom t) : End M) ^ d = End.of (ModuleCat.ofHom (aπ • LinearMap.id)) := by
  apply (ModuleCat.endRingEquiv M).injective
  rw [map_pow]
  change t ^ d = algebraMap B.obj (Module.End B.obj V) aπ
  exact drinfeldTangentUniformizer_pow ι Y uniformizer hPow

private def tangentStep (i : ZMod d) : summand i ⟶ summand (i + 1) :=
  ModuleCat.ofHom (((t).comp (W (idx i)).subtype).codRestrict (W (idx (i + 1))) (fun x => by
    rw [map_add, map_one]
    exact (drinfeldTangentUniformizerStep ι χ ψ Y σ uniformizer hPow hComm hσ (idx i) x).property))

private theorem tangentStep_inclusion (i : ZMod d) :
    j i ≫ ModuleCat.ofHom t = tangentStep ι χ ψ Y σ uniformizer hPow hComm hσ i ≫ j (i + 1) :=
  rfl

set_option maxHeartbeats 1000000 in
/-- The affine tangent sheaf with its cyclic character grading and uniformizer operator. -/
def drinfeldTangentGradedPiSheaf :
    GradedPiSheaf d (X).sheaf (schemeScalar X ((Scheme.ΓSpecIso R).inv aπ)) :=
  affineGradedPiSheaf («R» := R) («M» := M) («d» := d) («W» := summand)
    aπ (ModuleCat.ofHom t) (uniformizerPower ι Y uniformizer hPow)
    j p (tangentInclusion_projection ι χ ψ Y)
    (fun hk => tangentInclusion_projection_ne ι χ ψ Y hk)
    (tangentSum_projection_inclusion ι χ ψ Y)
    (tangentStep ι χ ψ Y σ uniformizer hPow hComm hσ)
    (tangentStep_inclusion ι χ ψ Y σ uniformizer hPow hComm hσ)

set_option maxHeartbeats 1000000 in
/-- The homogeneous subsheaf is the associated sheaf of the tangent projector image. -/
def drinfeldTangentComponentSheafIso (i : ZMod d) :
    tilde (summand i) ≅
      (drinfeldTangentGradedPiSheaf ι χ ψ Y σ uniformizer hPow hComm hσ).componentSheaf i :=
  affineGradedPiSheafComponentIso («R» := R) («M» := M) («d» := d) («W» := summand)
    aπ (ModuleCat.ofHom t) (uniformizerPower ι Y uniformizer hPow)
    j p (tangentInclusion_projection ι χ ψ Y)
    (fun hk => tangentInclusion_projection_ne ι χ ψ Y hk)
    (tangentSum_projection_inclusion ι χ ψ Y)
    (tangentStep ι χ ψ Y σ uniformizer hPow hComm hσ)
    (tangentStep_inclusion ι χ ψ Y σ uniformizer hPow hComm hσ) i

set_option backward.isDefEq.respectTransparency false in
private theorem tangentSummand_isLineSheaf (i : ZMod d) : IsLineSheaf X (tilde (summand i)) := by
  let : Module.Finite R (summand i) :=
    drinfeldTangentComponent_finite ι Y.unramified χ ψ Y.order (idx i)
  let : Module.Projective R (summand i) :=
    drinfeldTangentComponent_projective ι Y.unramified χ ψ Y.order (idx i)
  exact isLineSheaf_tilde_of_rankAtStalk («R» := R) (summand i)
    (drinfeldTangentComponent_rankAtStalk ι χ ψ Y (idx i))

set_option maxHeartbeats 1000000 in
/-- The actual tangent sheaf and the line property of each homogeneous component. -/
def drinfeldTangentLinePiSheaf : LinePiSheaf d X ((Scheme.ΓSpecIso R).inv aπ) where
  graded := drinfeldTangentGradedPiSheaf ι χ ψ Y σ uniformizer hPow hComm hσ
  line i := IsLineSheaf.of_iso (S := X)
    (drinfeldTangentComponentSheafIso ι χ ψ Y σ uniformizer hPow hComm hσ i)
    (tangentSummand_isLineSheaf ι χ ψ Y i)

end Langlands.FormalGroup.LocalDivision

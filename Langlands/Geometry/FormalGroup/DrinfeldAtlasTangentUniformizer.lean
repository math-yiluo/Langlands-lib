import Langlands.Geometry.FormalGroup.DrinfeldAtlasTangentComponentLocalization

/-! # The degree-one uniformizer on the compatible tangent module -/

noncomputable section

universe u v s

namespace Langlands.FormalGroup.LocalDivision.SpecialAtlas

open IsLocalRing ValuativeRel CentralDivision CentralSimple
  _root_.CategoryTheory ModuleLaw

attribute [local instance] ModuleLaw.coefficientAlgebra ModuleLaw.coefficientScalarTower

private theorem projector_fixes_image {A M : Type*} [CommRing A] [AddCommMonoid M] [Module A M]
    (P : Module.End A M) (hP : P * P = P) (x : LinearMap.range P) : P x.val = x.val := by
  obtain ⟨y, hy⟩ := x.property
  rw [← hy]
  exact LinearMap.congr_fun hP y

variable {K D : Type u} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K] [DivisionRing D] [Algebra K D]
  [FiniteDimensional K D] [Algebra.IsCentral K D]
variable {L : Type s} [Field L] [Algebra K L] (ι : L →ₐ[K] D)

local instance atlasTangentGradedSheafLocalHom :
    IsLocalHom (algebraMap 𝒪[K] (SubfieldIntegerRing K D ι)) := subfieldIntegerAlgebra_isLocalHom ι

local instance atlasTangentGradedSheafDegree : NeZero (CentralSimple.reducedDegree K D) :=
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

variable (σ : L ≃ₐ[K] L) (uD : Dˣ)
  (hPow : (uD : D) ^ CentralSimple.reducedDegree K D = algebraMap K D (π : K))
  (hComm : ∀ a : L, (uD : D) * ι a = ι (σ a) * (uD : D))
  (hσ : ∀ a : SubfieldIntegerRing K D ι,
    localReducedNormIntValuation K D (ι (σ (a : L)) - ι ((a : L) ^ Nat.card 𝓀[K])) < 1)

local notation "U" => drinfeldIntegralUniformizer uD hPow
local notation "T" => (ρ) U

section Chart

variable (A : CommAlgCat.{max u v} B.obj) (a : X.atlas.opens) (ha : IsUnit (algebraMap B.obj A a.val))
local notation "Aₙ" => tangentChartNilp (B := B) A
local notation "ψₐ" => tangentChartResidue ψ A
local notation "Y" => X.chartTestModule A a ha
local notation "E" => SpecialModule.order Y
local notation "Q" => drinfeldTangentProjector (B := Aₙ) ι X.unramified χ ψₐ E
local notation "Wₐ" => tangentTestComponent ι χ ψ X A a ha
local notation "ev" => tangentToChart X A a ha

set_option maxHeartbeats 950000 in
include hComm hσ in
private theorem tangentToChart_uniformizer_succ (i : Fin d) (z : W i) :
    ev (P (i + 1) (T z.val)) = ev (T z.val) := by
  let x : Wₐ i := tangentComponentToChart ι χ ψ X A a ha i z
  let Tₐ := (E).tangentAction U
  let y : Wₐ (i + 1) := drinfeldTangentUniformizerStep (B := Aₙ) ι χ ψₐ Y σ uD hPow hComm hσ i x
  have h : ev (T z.val) = Tₐ x.val := tangentToChart_order X A a ha z.val U
  have hfix : Q (i + 1) (Tₐ x.val) = Tₐ x.val :=
    projector_fixes_image (Q (i + 1))
      (drinfeldTangentProjector_mul_same ι X.unramified χ ψₐ E (i + 1)) y
  exact (tangentToChart_projector ι χ ψ X A a ha (i + 1) (T z.val)).trans
    ((congrArg (Q (i + 1)) h).trans (hfix.trans h.symm))

end Chart

set_option maxHeartbeats 850000 in
include hComm hσ in
/-- The uniformizer sends a vector in the actual projector image into the successor image. -/
theorem tangentUniformizer_mem_succ (i : Fin d) (z : W i) : T z.val ∈ W (i + 1) := by
  refine ⟨T z.val, ?_⟩
  apply Subtype.ext
  funext a
  let A := X.atlas.localAlgebra B₀ a
  let ha := X.atlas.localUnit B₀ a
  have h : tangentToChart X A a ha (P (i + 1) (T z.val)) = tangentToChart X A a ha (T z.val) :=
    tangentToChart_uniformizer_succ ι χ ψ X σ uD hPow hComm hσ A a ha i z
  exact (X.tangentToOwnChart_apply a (P (i + 1) (T z.val))).symm.trans
    (h.trans (X.tangentToOwnChart_apply a (T z.val)))

set_option maxHeartbeats 700000 in
include hComm hσ in
/-- The actual uniformizer advances each compatible tangent component by one degree. -/
def tangentUniformizerStep (i : Fin d) : W i →ₗ[B.obj] W (i + 1) :=
  ((T).comp (W i).subtype).codRestrict (W (i + 1))
    (tangentUniformizer_mem_succ ι χ ψ X σ uD hPow hComm hσ i)

end Langlands.FormalGroup.LocalDivision.SpecialAtlas

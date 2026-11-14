import Langlands.GroupScheme.IntegralModel.FiniteUnramifiedRecoveryAbove
import Langlands.GroupScheme.GaloisCocycleTowerRecovery

/-! # A common finite field for exact model and inner-cocycle recovery -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry
open Langlands.LocalGalois Langlands.LocalGalois.Separable
open scoped ValuativeRel CategoryTheory.MonObj
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

namespace Langlands.GroupScheme.IntegralModel

open Descent Descent.FiniteUnramified GaloisPointComparison

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance commonRecoveryNormedField : NontriviallyNormedField F := localNormedField F
local instance commonRecoveryUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance commonRecoveryComplete : CompleteSpace F := localNormedField_complete F

section AtField

variable (E : IntermediateField F (SeparableClosure F))
  [hEinertia : Fact (E ≤ inertiaFixedField F)]

local instance commonRecoveryFieldAlgebra : Algebra E (inertiaFixedField F) :=
  (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hEinertia.out)).toAlgebra
local instance commonRecoveryFieldTower : IsScalarTower F E (inertiaFixedField F) :=
  IsScalarTower.of_algebraMap_eq' rfl

variable [Normal F E]

/-- Restriction-kernel automorphisms fix any subfield whose actual image lies
in the supplied finite-stage field. -/
theorem mem_fixingSubgroup_of_restrictNormal_eq_one
    (C : IntermediateField F (inertiaFixedField F))
    (hC : C.map (inertiaFixedField F).val ≤ E)
    (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
    (hσ : σ.restrictNormal E = 1) : σ ∈ C.fixingSubgroup := by
  apply (C.mem_fixingSubgroup_iff σ).mpr
  intro x hx
  let xE : E :=
    ⟨(x : SeparableClosure F), hC ((IntermediateField.mem_map C).mpr ⟨x, hx, rfl⟩)⟩
  have hxE : algebraMap E (inertiaFixedField F) xE = x := by
    apply Subtype.ext
    rfl
  have hfix := AlgEquiv.restrictNormal_commutes σ E xE
  rw [hσ] at hfix
  change algebraMap E (inertiaFixedField F) xE =
    σ (algebraMap E (inertiaFixedField F) xE) at hfix
  rw [hxE] at hfix
  exact hfix.symm

/-- The actual chosen lift restricts to the given finite-stage automorphism. -/
theorem restrictNormal_liftAutomorphism (σ : E ≃ₐ[F] E) :
    (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ).restrictNormal E =
      σ := by
  apply AlgEquiv.ext
  intro x
  apply (algebraMap E (inertiaFixedField F)).injective
  exact (AlgEquiv.restrictNormal_commutes _ E x).trans
    (liftAutomorphism_commutes F E (show E ≤ inertiaFixedField F from hEinertia.out) σ x)

variable (G : GroupScheme (Spec (CommRingCat.of F)))
  (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
    (baseChanged F (inertiaFixedField F) G))
  (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
    rationalPoints (baseChanged F (inertiaFixedField F) G))

/-- Exact recovery of the supplied model and actual cocycle over one field.
The cocycle recovery is required for every upstairs automorphism. -/
def HasFiniteInnerRecoveryAt : Prop :=
  HasFiniteRecoveryAt F E G P ∧
    ∃ d : (E ≃ₐ[F] E) → rationalPoints (baseChanged F E G),
      (∀ σ τ, d (σ * τ) = d σ * rationalConjugate F E G σ (d τ)) ∧
      ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
        relativeRationalExtend F E (inertiaFixedField F) G (d (σ.restrictNormal E)) = c σ

include hEinertia in
/-- Recovery at every automorphism gives the exact chosen-lift recovery used
by the finite integral inner-descent construction. -/
theorem recovery_at_liftAutomorphism
    (d : (E ≃ₐ[F] E) → rationalPoints (baseChanged F E G))
    (hrec : ∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
      relativeRationalExtend F E (inertiaFixedField F) G (d (σ.restrictNormal E)) = c σ)
    (σ : E ≃ₐ[F] E) :
    relativeRationalExtend F E (inertiaFixedField F) G (d σ) =
      c (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ) := by
  simpa only [restrictNormal_liftAutomorphism] using
    hrec (liftAutomorphism F E (show E ≤ inertiaFixedField F from hEinertia.out) σ)

end AtField

set_option maxHeartbeats 400000 in
/-- Finite triviality and a supplied smooth model have exact recovery over one
actual finite Galois arithmetically unramified field. -/
theorem exists_common_finiteInnerRecovery
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
    (P : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F)
      (baseChanged F (inertiaFixedField F) G))
    (hP : P.IsSmooth)
    (c : (inertiaFixedField F ≃ₐ[F] inertiaFixedField F) →
      rationalPoints (baseChanged F (inertiaFixedField F) G))
    (hc : ∀ σ τ, c (σ * τ) = c σ * rationalConjugate F (inertiaFixedField F) G σ (c τ))
    (hfinite : ∃ C : IntermediateField F (inertiaFixedField F),
      FiniteDimensional F C ∧ ∀ σ ∈ C.fixingSubgroup, c σ = 1) :
    ∃ (E : IntermediateField F (SeparableClosure F))
      (hE : Fact (E ≤ inertiaFixedField F)) (hgal : IsGalois F E),
      letI := hE
      letI := hgal
      FiniteDimensional F E ∧ ArithmeticUnramified F E ∧
        HasFiniteInnerRecoveryAt F E G P c := by
  obtain ⟨C, hfinC, htriv⟩ := hfinite
  let : FiniteDimensional F C := hfinC
  let C' := C.map (inertiaFixedField F).val
  let : FiniteDimensional F C' :=
    LinearEquiv.finiteDimensional (IntermediateField.equivMap C (inertiaFixedField F).val).toLinearEquiv
  have hC' : C' ≤ inertiaFixedField F := by
    intro x hx
    obtain ⟨y, _, rfl⟩ := (IntermediateField.mem_map C).mp hx
    exact y.property
  obtain ⟨E, hE, hfin, hgal, hunram, hCE, hmodel⟩ :=
    finiteUnramifiedRecovery_above F C' hC' G P hP
  let : Fact (E ≤ inertiaFixedField F) := hE
  let : IsGalois F E := hgal
  let : Algebra E (inertiaFixedField F) :=
    (IntermediateField.inclusion (show E ≤ inertiaFixedField F from hE.out)).toAlgebra
  let : IsScalarTower F E (inertiaFixedField F) := IsScalarTower.of_algebraMap_eq' rfl
  have hkernel (σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F)
      (hσ : σ.restrictNormal E = 1) : c σ = 1 :=
    htriv σ (mem_fixingSubgroup_of_restrictNormal_eq_one F E C hCE σ hσ)
  refine ⟨E, hE, hgal, hfin, hunram, hmodel, ?_⟩
  exact GaloisCocycleTowerRecovery.exists_rational_cocycle
    F E (inertiaFixedField F) G c hc hkernel

end Langlands.GroupScheme.IntegralModel

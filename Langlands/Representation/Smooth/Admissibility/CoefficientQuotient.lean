import Langlands.Representation.Compact.SurjectivityProof
import Langlands.Representation.Jacquet.CoefficientScalarRestriction
import Langlands.Representation.Smooth.Admissibility.CofinalProof
import Langlands.Representation.Smooth.Transfer.SubquotientProof
import Mathlib.LinearAlgebra.Isomorphisms

/-! Admissibility of actual coefficient quotients via compact invariant lifts. -/

noncomputable section

namespace Langlands

universe uR uG uV uW

variable {R : Type uR} [CommRing R] [Algebra ℂ R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module R V]
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {ρ : Representation R G V} {σ : Representation R G W}

/-- Complex averaging supplies invariant lifts for the original coefficient-linear
map, without any finite-generation or Noetherian assumption. -/
theorem fixedVectorsMap_surjective_of_complexAlgebra
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Function.Surjective (fixedVectorsMap f K.toSubgroup) := by
  let : Module ℂ V := Module.compHom V (algebraMap ℂ R)
  let : Module ℂ W := Module.compHom W (algebraMap ℂ R)
  let : IsScalarTower ℂ R V := IsScalarTower.of_compHom ℂ R V
  let : IsScalarTower ℂ R W := IsScalarTower.of_compHom ℂ R W
  let ρc := Jacquet.CoefficientRestriction.complexRepresentation ρ
  let σc := Jacquet.CoefficientRestriction.complexRepresentation σ
  let fc : ρc.IntertwiningMap σc :=
    { toLinearMap := f.toLinearMap.restrictScalars ℂ
      isIntertwining' := by
        intro g
        apply LinearMap.ext
        intro v
        exact LinearMap.congr_fun (f.isIntertwining' g) v }
  have hσ : IsSmooth σ := isSmooth_of_surjective f hf hρ
  have hsurj := Compact.fixedVectorSurjectivity G V W ρc σc hρ hσ K hK fc hf
  intro w
  let wc : fixedVectors σc K.toSubgroup := ⟨w.val, w.property⟩
  obtain ⟨v, hv⟩ := hsurj wc
  refine ⟨⟨v.val, v.property⟩, ?_⟩
  apply Subtype.ext
  exact congrArg Subtype.val hv

/-- The actual target compact fixed vectors are the native source fixed vectors
modulo the kernel of the restricted intertwiner. -/
def fixedVectorsQuotientEquiv_of_complexAlgebra
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    (fixedVectors ρ K.toSubgroup ⧸ (fixedVectorsMap f K.toSubgroup).ker) ≃ₗ[R]
      fixedVectors σ K.toSubgroup :=
  (fixedVectorsMap f K.toSubgroup).quotKerEquivOfSurjective
    (fixedVectorsMap_surjective_of_complexAlgebra f hf hρ K hK)

@[simp]
theorem fixedVectorsQuotientEquiv_of_complexAlgebra_mk
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (v : fixedVectors ρ K.toSubgroup) :
    fixedVectorsQuotientEquiv_of_complexAlgebra f hf hρ K hK (Submodule.Quotient.mk v) =
      fixedVectorsMap f K.toSubgroup v := rfl

/-- Native coefficient admissibility passes to a surjective intertwining image
when compact open subgroups are cofinal among open subgroups. -/
theorem isAdmissible_of_surjective_coefficients [IsNoetherianRing R]
    (hG : ∀ H : OpenSubgroup G,
      ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ K ≤ H)
    (f : ρ.IntertwiningMap σ) (hf : Function.Surjective f) (hρ : IsAdmissible ρ) :
    IsAdmissible σ := by
  refine ⟨isSmooth_of_surjective f hf hρ.1, fun H => ?_⟩
  obtain ⟨K, hK, hKH⟩ := hG H
  let : Module.Finite R (fixedVectors ρ K.toSubgroup) := hρ.2 K
  let e := fixedVectorsQuotientEquiv_of_complexAlgebra f hf hρ.1 K hK
  let : Module.Finite R (fixedVectors σ K.toSubgroup) :=
    Module.Finite.of_surjective e.toLinearMap e.surjective
  exact finite_fixedVectors_of_le (ρ := σ)
    (show K.toSubgroup ≤ H.toSubgroup from hKH)

end Langlands

import Langlands.CommutativeAlgebra.RegularLocalPunctualComplexStatement
import Langlands.CommutativeAlgebra.RegularLocalFiniteLengthAcyclicityStatement
import Langlands.CommutativeAlgebra.RegularLocalResidueResolutionDualityStatement
import Langlands.CommutativeAlgebra.PunctualHomologySupport
import Langlands.CommutativeAlgebra.PunctualReversedDualTopHomology

/-! # Reduction of the punctual complex theorem to two local algebra inputs -/

universe u

open CategoryTheory CategoryTheory.Limits IsLocalRing
open Langlands.Cohomology.ModuleComplex

namespace Langlands.CommutativeAlgebra

/-- Finite-length acyclicity and residue-resolution duality suffice for the
punctual perfect-complex statement. Both supporting propositions are explicit
hypotheses of this reduction. -/
theorem regularLocalPunctualComplex_of_acyclicity_of_residueResolutionDuality
    (hacyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u})
    (hduality : RegularLocalResidueResolutionDualityStatement.{u}) :
    RegularLocalPunctualComplexStatement.{u} := by
  intro R _ _ g hdim K hK hres hrank htorsion htest
  let M := punctualMinimalModel R g K hK hres hrank
  have htorsionM (i : ℤ) :
      ∃ N : ℕ, maximalIdeal R ^ N ≤ Module.annihilator R (M.complex.homology i) := by
    obtain ⟨N, hN⟩ := htorsion i
    refine ⟨N, ?_⟩
    rwa [(M.equiv.toHomologyIso i).toLinearEquiv.annihilator_eq]
  have hlowM := hacyclicity R g hdim M.complex M.finiteFree M.strictlyGE htorsionM
  have hvanishM (i : ℤ) (hi : i ≠ (g : ℤ)) : IsZero (M.complex.homology i) := by
    by_cases hlt : i < (g : ℤ)
    · exact hlowM i hlt
    · have := M.strictlyLE
      exact M.complex.isZero_of_isLE (g : ℤ) i (by omega)
  let D := reversedDual (g : ℤ) M.complex
  have hDfree : IsFiniteFree D := isFiniteFree_reversedDual _ _ M.finiteFree
  have hDGE : D.IsStrictlyGE 0 := by
    simpa [D] using reversedDual_isStrictlyGE (g : ℤ) (g : ℤ) M.complex M.strictlyLE
  have hDLE : D.IsStrictlyLE (g : ℤ) := by
    simpa [D] using reversedDual_isStrictlyLE (g : ℤ) 0 M.complex M.strictlyGE
  have htorsionD (i : ℤ) :
      ∃ N : ℕ, maximalIdeal R ^ N ≤ Module.annihilator R (D.homology i) :=
    exists_pow_le_annihilator_homology_reversedDual (maximalIdeal R) (g : ℤ)
      M.complex M.finiteFree htorsionM i
  have hlowD := hacyclicity R g hdim D hDfree hDGE htorsionD
  have hvanishD (i : ℤ) (hi : i ≠ (g : ℤ)) : IsZero (D.homology i) := by
    by_cases hlt : i < (g : ℤ)
    · exact hlowD i hlt
    · have := hDLE
      exact D.isZero_of_isLE (g : ℤ) i (by omega)
  obtain ⟨eDD⟩ := hduality R g hdim D hDfree hDGE hDLE hvanishD
    ⟨punctualModelReversedDualTopHomologyIsoResidueField M htest⟩
  refine ⟨fun i hi ↦ (hvanishM i hi).of_iso (M.equiv.toHomologyIso i).symm, ?_⟩
  exact ⟨(M.equiv.toHomologyIso (g : ℤ)).symm ≪≫
    (HomologicalComplex.homologyFunctor _ _ (g : ℤ)).mapIso
      (reversedDualBidualIso (g : ℤ) M.complex M.finiteFree.2) ≪≫ eDD⟩

/-- Choose the top-homology isomorphism supplied by the conditional reduction,
with both local-algebra inputs and all original punctual hypotheses explicit. -/
noncomputable def punctualTopHomologyIsoOfLocalAlgebra
    (hacyclicity : RegularLocalFiniteLengthAcyclicityStatement.{u})
    (hduality : RegularLocalResidueResolutionDualityStatement.{u})
    (R : Type u) [CommRing R] [IsRegularLocalRing R] (g : ℕ)
    (hdim : ringKrullDim R = g)
    (K : CochainComplex (ModuleCat.{u} R) ℤ)
    (hK : IsStrictlyPerfect K)
    (hres : ∀ i : ℤ, (i < 0 ∨ (g : ℤ) < i) →
      IsZero (((baseChange (algebraMap R (ResidueField R))).obj K).homology i))
    (hrank : Module.finrank (ResidueField R)
      (((baseChange (algebraMap R (ResidueField R))).obj K).homology 0) = 1)
    (htorsion : ∀ i : ℤ, ∃ N : ℕ,
      maximalIdeal R ^ N ≤ Module.annihilator R (K.homology i))
    (htest : ∀ J : Ideal R, maximalIdeal R ^ 2 ≤ J → J ⋖ maximalIdeal R →
      IsEmpty (((baseChange (Ideal.Quotient.mk J)).obj K).homology 0 ≅
        ModuleCat.of (R ⧸ J) (R ⧸ J))) :
    K.homology (g : ℤ) ≅ ModuleCat.of R (ResidueField R) :=
  Classical.choice
    ((regularLocalPunctualComplex_of_acyclicity_of_residueResolutionDuality
      hacyclicity hduality R g hdim K hK hres hrank htorsion htest).2)

end Langlands.CommutativeAlgebra

import Langlands.Cohomology.AcyclicResolution.DerivedCompositeIsomorphismStatement

/-! # Proof of the derived composite comparison isomorphism criterion -/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Cohomology.AcyclicResolution

universe w w' w'' v v' v'' u u' u''

set_option backward.isDefEq.respectTransparency false in
/-- Isomorphisms are detected on all integer cohomology objects. -/
theorem derivedCompositeIsomorphism :
    DerivedCompositeIsomorphismStatement.{w, w', w'', v, v', v'', u, u', u''} := by
  intro C _ _ _ _ D _ _ _ _ E _ _ _ F _ _ G _ _ H _ e A hA hG
  apply (DerivedCategory.isIso_iff E _).2
  intro n
  by_cases hn : n < 0
  · exact (DerivedPlus.isZero_homology_of_neg H A hn).isIso
      (DerivedPlus.isZero_homology_of_neg G (F.obj A) hn) _
  · lift n to ℕ using le_of_not_gt hn
    have := isIso_compComparison G e A hA hG n
    have h : IsIso
        ((DerivedCategory.homologyFunctor E (n : ℤ)).map
          (derivedCompComparison G e A hA) ≫
          (DerivedPlus.homologyIso G (injectiveResolution (F.obj A)) n).hom) := by
      rw [derivedCompComparison_homology]
      infer_instance
    exact (isIso_comp_right_iff _ _).1 h

end Langlands.Cohomology.AcyclicResolution

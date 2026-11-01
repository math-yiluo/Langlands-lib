import Langlands.Algebra.NondegenerateInductionExactnessStatements
import Langlands.Algebra.NondegenerateFInductionExactness
import Langlands.Algebra.NondegenerateFInductionAdjunction
import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor

/-!
# Injectivity preservation by Renard's actual I functor

The published exactness and canonical adjunction proofs imply both the source
exact-Hom and Mathlib injectivity conclusions at the common carrier universe.
-/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra

universe uA uB v

private theorem injectivity_of_sequenceExact_adjunction
    {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
    (F : C ⥤ D) [F.Additive] (R : D ⥤ C)
    (hF : Langlands.Renard.SequenceExact F) (adj : F ⊣ R) (X : D) :
    (Langlands.Renard.HomInjective X → Langlands.Renard.HomInjective (R.obj X)) ∧
      (Injective X → Injective (R.obj X)) := by
  let : F.PreservesMonomorphisms :=
    Functor.preservesMonomorphisms_of_preserves_shortExact_left F
      (fun S hS => hF.1 S ⟨hS.exact, hS.mono_f⟩)
  have hMathlib : Injective X → Injective (R.obj X) := adj.map_injective X
  exact ⟨fun hX => (Langlands.Renard.homInjectiveComparison (R.obj X)).mpr
    (hMathlib ((Langlands.Renard.homInjectiveComparison X).mp hX)), hMathlib⟩

/-- The actual induction functor I preserves injectives in both published senses. -/
theorem nondegenerateIInductionInjectivity :
    NondegenerateIInductionInjectivityTheorem.{uA, uB, v} := by
  intro A B a b hA hB left hAB hnd
  let := NondegenerateModuleCat.abelian.{uA, max uB v} A hA
  let := NondegenerateModuleCat.abelian.{uB, max uB v} B hB
  obtain ⟨adj, _⟩ :=
    NondegenerateInductionAdjunction.nondegenerateFInductionAdjunction.{uA, uB, v}
      A B hA hB hAB hnd
  intro X
  exact injectivity_of_sequenceExact_adjunction _ _
    (nondegenerateFInductionExactness.{uA, uB, max uB v} A B hA hB hAB hnd).1 adj X

end Langlands.Algebra

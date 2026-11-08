import Langlands.Global.AdelicAdditiveDualityProof
import Langlands.Global.Factors.HeckeArchimedeanComponents

/-! # Local data for actual global Hecke characters -/

noncomputable section

universe u

namespace Langlands.Global.HeckeFunctionalEquation

open NumberField
open Langlands.HarmonicAnalysis
open Langlands.LocalFactor.Archimedean

variable {K : Type u} [Field K] [NumberField K]

/-- Every actual finite restriction is nontrivial for a diagonal-trivial
nontrivial global additive character. -/
theorem finiteAdditiveRestriction_ne_one
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : FinitePlace K) :
    finiteAdditiveRestriction ψ v ≠ 1 := by
  obtain ⟨⟨e, he⟩, _⟩ := adelicDuality K ψ hdiag
  exact finiteAdditiveRestriction_ne_one_of_pairing ψ e he v

/-- Every actual infinite restriction is nontrivial under the same hypotheses. -/
theorem infiniteAdditiveRestriction_ne_one
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : InfinitePlace K) :
    infiniteAdditiveRestriction ψ v ≠ 1 := by
  obtain ⟨⟨e, he⟩, _⟩ := adelicDuality K ψ hdiag
  exact infiniteAdditiveRestriction_ne_one_of_pairing ψ e he v

/-- The actual finite restriction, bundled using proved global nontriviality. -/
def globalFiniteAdditiveComponent
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : FinitePlace K) :
    @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
      (CompletionPadic.topologicalData v).topology :=
  finiteAdditiveComponent ψ v (finiteAdditiveRestriction_ne_one ψ hdiag v)

theorem isFiniteAdditiveComponent_globalFiniteAdditiveComponent
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : FinitePlace K) :
    IsFiniteAdditiveComponent ψ v (globalFiniteAdditiveComponent ψ hdiag v) :=
  isFiniteAdditiveComponent_finiteAdditiveComponent ψ v _

theorem nonempty_selfDualHaar_globalFiniteAdditiveComponent
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : FinitePlace K) :
    Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v)
      (globalFiniteAdditiveComponent ψ hdiag v)) :=
  nonempty_selfDualHaar_of_nontrivial_restriction ψ v _

/-- The actual infinite restriction, bundled using proved global nontriviality. -/
def globalInfiniteAdditiveComponent
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) (v : InfinitePlace K) :
    UnitaryAdditiveCharacter (InfiniteCompletion K v) :=
  infiniteAdditiveComponent ψ v (infiniteAdditiveRestriction_ne_one ψ hdiag v)

/-- The full local-data existence conjunct of the global functional-equation
statement, using proved actual adelic duality. -/
theorem localData (χ : HeckeCharacter K)
    (ψ : UnitaryAdditiveCharacter (Adeles K))
    (hdiag : ∀ k : K, ψ (diagonal K k) = 1) :
    (∀ v : FinitePlace K,
      ∃ ψv : @UnitaryAdditiveCharacter (CompletionPadic.padicField v).Carrier _
          (CompletionPadic.topologicalData v).topology,
        IsFiniteAdditiveComponent ψ v ψv ∧
          Nonempty (LocalFactor.PadicAbelian.SelfDualHaar (CompletionPadic.topologicalData v) ψv)) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsReal),
      (∃ a : ℝˣ, IsRealAdditiveComponent ψ v hv a) ∧
        ∃ d : RealCharacterData, IsRealCharacterPresentation hv (χ.infiniteComponent v) d) ∧
    (∀ (v : InfinitePlace K) (hv : v.IsComplex),
      (∃ a : ℂˣ, IsComplexAdditiveComponent ψ v hv a) ∧
        ∃ d : ComplexCharacterData, IsComplexCharacterPresentation hv (χ.infiniteComponent v) d) := by
  obtain ⟨⟨e, he⟩, _⟩ := adelicDuality K ψ hdiag
  exact localData_of_pairing χ ψ e he

end Langlands.Global.HeckeFunctionalEquation

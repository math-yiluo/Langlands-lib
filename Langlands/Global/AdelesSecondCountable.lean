import Langlands.Global.Adelic
import Mathlib.NumberTheory.NumberField.Completion.FinitePlace
import Mathlib.LinearAlgebra.Countable
import Mathlib.Topology.Bases
import Mathlib.Topology.Homeomorph.Lemmas

/-! # Second countability of the actual number-field adele rings -/

noncomputable section

universe u v

open Filter Set Topology TopologicalSpace
open scoped RestrictedProduct

namespace Langlands.Global

/-- A countable restricted product of second-countable spaces, restricted by open
subsets, is second countable for the restricted-product topology. -/
theorem restrictedProduct_secondCountableTopology
    {ι : Type u} [Countable ι] (R : ι → Type v) (A : (i : ι) → Set (R i))
    [∀ i, TopologicalSpace (R i)] [∀ i, SecondCountableTopology (R i)]
    (hA : ∀ i, IsOpen (A i)) :
    SecondCountableTopology (Πʳ i, [R i, A i]) := by
  classical
  have hS (s : Finset ι) : cofinite ≤ 𝓟 (s : Set ι)ᶜ := by simp
  let f (s : Finset ι) := RestrictedProduct.inclusion R A (hS s)
  let U (s : Finset ι) := Set.range (f s)
  have hE (s : Finset ι) : IsOpenEmbedding (f s) :=
    RestrictedProduct.isOpenEmbedding_inclusion_principal hA (hS s)
  have hC (s : Finset ι) :
      SecondCountableTopology (Πʳ i, [R i, A i]_[𝓟 (s : Set ι)ᶜ]) :=
    RestrictedProduct.isEmbedding_coe_of_principal.secondCountableTopology
  let (s : Finset ι) : SecondCountableTopology (U s) := by
    let := hC s
    exact (hE s).isEmbedding.toHomeomorph.symm.secondCountableTopology
  apply secondCountableTopology_of_countable_cover (U := U)
    (fun s => (hE s).isOpen_range)
  apply Set.eq_univ_of_forall
  intro x
  let s := (eventually_cofinite.mp x.2).toFinset
  apply Set.mem_iUnion.mpr
  refine ⟨s, ?_⟩
  apply Set.mem_range.mpr
  apply RestrictedProduct.exists_inclusion_eq_of_eventually R A (hS s)
  change ∀ i ∈ (s : Set ι)ᶜ, x i ∈ A i
  intro i hi
  have hi' : i ∉ s := hi
  have hx : x.1 i ∈ A i := by
    simpa only [s, Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hi'
  exact hx

variable (F : Type u) [Field F] [NumberField F]

/-- A number field has a countable underlying set. -/
theorem numberField_countable : Countable F :=
  Finsupp.Countable.of_moduleFinite (R := ℚ)

/-- The finite places form a countable set, through their finitely generated ideals. -/
theorem finitePlace_countable : Countable (FinitePlace F) := by
  let := numberField_countable F
  let : Countable (NumberField.RingOfIntegers F) :=
    Subtype.val_injective.countable
  let : Countable (Ideal (NumberField.RingOfIntegers F)) :=
    Function.Surjective.countable
      (f := fun s : Finset (NumberField.RingOfIntegers F) =>
        Ideal.span (s : Set (NumberField.RingOfIntegers F)))
      (fun I => by
        obtain ⟨s, hs⟩ := I.fg_of_isNoetherianRing
        exact ⟨s, hs⟩)
  exact IsDedekindDomain.HeightOneSpectrum.asIdeal_injective.countable

/-- Density of the number field makes each nonarchimedean completion separable. -/
theorem finiteCompletion_separableSpace (v : FinitePlace F) :
    SeparableSpace (FiniteCompletion F v) := by
  let := numberField_countable F
  exact SeparableSpace.of_denseRange (algebraMap F (FiniteCompletion F v))
    (v.denseRange_algebraMap F)

/-- Each actual nonarchimedean completion is second countable. -/
theorem finiteCompletion_secondCountableTopology (v : FinitePlace F) :
    SecondCountableTopology (FiniteCompletion F v) := by
  let := finiteCompletion_separableSpace F v
  infer_instance

omit [NumberField F] in
/-- The isometric complex embedding makes each archimedean completion second countable. -/
theorem infiniteCompletion_secondCountableTopology (v : InfinitePlace F) :
    SecondCountableTopology (InfiniteCompletion F v) :=
  (NumberField.InfinitePlace.Completion.isometry_extensionEmbedding v).isEmbedding.secondCountableTopology

/-- The actual finite adele restricted product is second countable. -/
theorem finiteAdeles_secondCountableTopology : SecondCountableTopology (FiniteAdeles F) := by
  let := finitePlace_countable F
  let (v : FinitePlace F) := finiteCompletion_secondCountableTopology F v
  exact restrictedProduct_secondCountableTopology
    (FiniteCompletion F) (fun v => (v.adicCompletionIntegers F : Set (FiniteCompletion F v)))
    (fun _ => Valued.isOpen_valuationSubring _)

/-- The actual finite product of archimedean completions is second countable. -/
theorem infiniteAdeles_secondCountableTopology : SecondCountableTopology (InfiniteAdeles F) := by
  let (v : InfinitePlace F) := infiniteCompletion_secondCountableTopology F v
  exact inferInstanceAs (SecondCountableTopology ((v : InfinitePlace F) → v.Completion))

/-- The full number-field adele ring is second countable in its actual topology. -/
theorem adeles_secondCountableTopology : SecondCountableTopology (Adeles F) := by
  let := finiteAdeles_secondCountableTopology F
  let := infiniteAdeles_secondCountableTopology F
  exact inferInstanceAs (SecondCountableTopology (InfiniteAdeles F × FiniteAdeles F))

/-- A countable basis of nonempty open sets for the actual full adele ring. -/
def adelesCountableBasis : Set (Set (Adeles F)) := by
  let := adeles_secondCountableTopology F
  exact countableBasis (Adeles F)

theorem adelesCountableBasis_countable : (adelesCountableBasis F).Countable := by
  let := adeles_secondCountableTopology F
  exact countable_countableBasis (Adeles F)

theorem adelesCountableBasis_isTopologicalBasis :
    IsTopologicalBasis (adelesCountableBasis F) := by
  let := adeles_secondCountableTopology F
  exact isBasis_countableBasis (Adeles F)

end Langlands.Global

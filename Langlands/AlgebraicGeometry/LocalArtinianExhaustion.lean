import Langlands.Algebra.AdicSupportSeparation
import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreLocalStepParts
import Langlands.AlgebraicGeometry.Picard.AffineBaseChangeKernel
import Mathlib.AlgebraicGeometry.Morphisms.Immersion
import Mathlib.AlgebraicGeometry.Morphisms.QuasiFinite

/-! # The local geometric step in Artinian subscheme exhaustion -/

noncomputable section

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry IsLocalRing
open Langlands.AlgebraicGeometry.UnramifiedFunctor

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.AlgebraicGeometry.LocalArtinianExhaustion

/-- The local geometric step of SGA 3, IX 6.2. -/
def Statement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsNoetherianRing R] [IsLocalRing R]
    (X : Scheme.{u}) (f : X ⟶ Spec R),
    LocallyOfFiniteType f → LocallyQuasiFinite f → QuasiCompact f →
    ∀ (I : Type v) [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
      (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X),
      (∀ i, IsImmersion (j i)) →
      (∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i) →
      (∃ i, IsIso (pullback.snd (j i) (pullback.fst f (puncturedSpectrum R).ι))) →
      (∀ n : ℕ, ∃ i, IsIso (pullback.snd (j i)
        (pullback.fst f (maximalIdealPowQuotientMap R n)))) →
      ∃ i, IsIso (j i)

variable {X Y Z T : Scheme.{u}}

/-- A base change that is an isomorphism forces the projection's image into
that of the original morphism. -/
theorem range_subset_of_pullback_isIso (j : Y ⟶ X) (p : T ⟶ X)
    [IsIso (pullback.snd j p)] : Set.range p ⊆ Set.range j := by
  rintro _ ⟨t, rfl⟩
  have ht : t ∈ Set.range (pullback.snd j p) :=
    Set.mem_range.mpr ((pullback.snd j p).surjective t)
  rwa [Scheme.Pullback.range_snd] at ht

/-- Isomorphism after a fixed base change persists along an inclusion of
subschemes. -/
theorem pullback_isIso_of_factor (j : Y ⟶ X) (k : Z ⟶ X) (p : T ⟶ X)
    [Mono k] [IsIso (pullback.snd j p)] (a : Y ⟶ Z) (ha : a ≫ k = j) :
    IsIso (pullback.snd k p) := by
  let a' := pullback.map j p k p a (𝟙 _) (𝟙 _) (by simpa using ha.symm) (by simp)
  have ha' : a' ≫ pullback.snd k p = pullback.snd j p := by simp [a']
  have : IsSplitEpi (pullback.snd k p) :=
    IsSplitEpi.mk' ⟨inv (pullback.snd j p) ≫ a', by simp [Category.assoc, ha']⟩
  exact isIso_of_mono_of_isSplitEpi _

/-- A surjective immersion is a closed immersion. -/
theorem closedImmersion_of_surjective (j : Y ⟶ X) [IsImmersion j] [Surjective j] :
    IsClosedImmersion j :=
  IsClosedImmersion.of_isPreimmersion j (by rw [Set.range_eq_univ.mpr j.surjective]; exact isClosed_univ)

/-- The closed point belongs to the image of the residue quotient. -/
theorem closedPoint_mem_residue_range (R : CommRingCat.{u}) [IsLocalRing R] :
    closedPoint R ∈ Set.range (maximalIdealPowQuotientMap R 0) := by
  change closedPoint R ∈ Set.range (PrimeSpectrum.comap
    (Ideal.Quotient.mk (IsLocalRing.maximalIdeal R ^ (0 + 1))))
  rw [range_comap_of_surjective _ _ Ideal.Quotient.mk_surjective,
    Ideal.mk_ker]
  change IsLocalRing.maximalIdeal R ^ (0 + 1) ≤ IsLocalRing.maximalIdeal R
  simp

/-- Full punctured and special fibres force a stage to be surjective. -/
theorem surjective_of_punctured_and_residue (R : CommRingCat.{u}) [IsLocalRing R]
    (f : X ⟶ Spec R) (j : Y ⟶ X)
    [IsIso (pullback.snd j (pullback.fst f (puncturedSpectrum R).ι))]
    [IsIso (pullback.snd j (pullback.fst f (maximalIdealPowQuotientMap R 0)))] :
    Surjective j := by
  constructor
  intro x
  by_cases hx : f x = closedPoint R
  · apply range_subset_of_pullback_isIso j (pullback.fst f (maximalIdealPowQuotientMap R 0))
    rw [Scheme.Pullback.range_fst]
    change f x ∈ Set.range (maximalIdealPowQuotientMap R 0)
    rw [hx]
    exact closedPoint_mem_residue_range R
  · apply range_subset_of_pullback_isIso j (pullback.fst f (puncturedSpectrum R).ι)
    rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]
    exact hx

/-- A directed family with a full punctured stage and a full special-fibre stage
has a surjective closed-immersion stage. -/
theorem exists_closed_surjective_stage (R : CommRingCat.{u}) [IsLocalRing R]
    (f : X ⟶ Spec R) {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
    (Y : I → Scheme.{u}) (j : ∀ i, Y i ⟶ X)
    (hj : ∀ i, IsImmersion (j i))
    (hmono : ∀ i k, i ≤ k → ∃ a : Y i ⟶ Y k, a ≫ j k = j i)
    (hU : ∃ i, IsIso (pullback.snd (j i) (pullback.fst f (puncturedSpectrum R).ι)))
    (h₀ : ∃ i, IsIso (pullback.snd (j i)
      (pullback.fst f (maximalIdealPowQuotientMap R 0)))) :
    ∃ k, Surjective (j k) ∧ IsClosedImmersion (j k) ∧
      IsIso (pullback.snd (j k) (pullback.fst f (puncturedSpectrum R).ι)) := by
  obtain ⟨i, hi⟩ := hU
  obtain ⟨l, hl⟩ := h₀
  obtain ⟨k, hik, hlk⟩ := exists_ge_ge i l
  let := hj k
  let := hi
  let := hl
  obtain ⟨a, ha⟩ := hmono i k hik
  obtain ⟨b, hb⟩ := hmono l k hlk
  have hUk := pullback_isIso_of_factor (j i) (j k)
    (pullback.fst f (puncturedSpectrum R).ι) a ha
  have h₀k := pullback_isIso_of_factor (j l) (j k)
    (pullback.fst f (maximalIdealPowQuotientMap R 0)) b hb
  have hsk := surjective_of_punctured_and_residue R f (j k)
  exact ⟨k, hsk, closedImmersion_of_surjective (j k), hUk⟩

end Langlands.AlgebraicGeometry.LocalArtinianExhaustion

import Langlands.CategoryTheory.Renard.SimpleSupportSplittingSubquotientsStatements
import Langlands.CategoryTheory.Renard.SimpleSupportSumProof
import Langlands.CategoryTheory.Renard.SimpleSupportColimit
import Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty
import Mathlib.CategoryTheory.Abelian.CommSq

/-!
# Renard A.IX: a support partition splits every subquotient of a split object

Proof of the unnumbered lemma on printed268/PDF274 of the French edition
dated 9 July 2026. For a subquotient `Y` of `X`, presented by a monomorphism
`j : N ⟶ X` and an epimorphism `p : N ⟶ Y`, the canonical map
`∐ i, Y_(S i) ⟶ Y` is shown to be monic and epic. Both proofs show that the
relevant kernel or cokernel has no simple subquotient. They use the
cokernel of one coproduct injection, whose simple classes come from the
other summands.
-/

universe r w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

section Helpers

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Coproduct support for an index type that is only `Small.{r}`: reindex
through `Shrink` and apply `simpleSubquotientClasses_sigma_subset`. -/
theorem simpleSubquotientClasses_sigma_subset_of_small
    (hG : IsSourceGrothendieck.{r} C) (hAB6 : SourceAB6 C)
    {J : Type w} [Small.{r} J] (F : J → C) [HasCoproduct F] :
    simpleSubquotientClasses (∐ F) ⊆ ⋃ j, simpleSubquotientClasses (F j) := by
  let : HasCoproducts.{r} C := hG.1
  let e := equivShrink.{r} J
  intro q hq
  have hq' := simpleSubquotientClasses_subset_of_mono (Sigma.reindex e.symm F).inv hq
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
    (simpleSubquotientClasses_sigma_subset hG hAB6 (F ∘ e.symm) hq')
  exact Set.mem_iUnion.mpr ⟨e.symm k, hk⟩

/-- The cokernel of the coproduct injection at `a` only has the simple
subquotient classes of the summands at indices different from `a`. -/
theorem simpleSubquotientClasses_cokernel_sigmaι_subset
    (hG : IsSourceGrothendieck.{r} C) (hAB6 : SourceAB6 C)
    {J : Type w} [Small.{r} J] (F : J → C) [HasCoproduct F] (a : J) :
    simpleSubquotientClasses (cokernel (Sigma.ι F a)) ⊆
      ⋃ (j : J) (_ : j ≠ a), simpleSubquotientClasses (F j) := by
  let : HasCoproducts.{r} C := hG.1
  let G : {j : J // j ≠ a} → C := fun j => F j.1
  let : HasCoproductsOfShape {j : J // j ≠ a} C :=
    hasCoproductsOfShape_of_small.{r} C {j : J // j ≠ a}
  let g : (∐ G) ⟶ cokernel (Sigma.ι F a) :=
    Sigma.desc fun j => Sigma.ι F j.1 ≫ cokernel.π (Sigma.ι F a)
  have hg : Epi g := by
    refine Preadditive.epi_of_cancel_zero _ fun {Z} h hgh => ?_
    rw [← cancel_epi (cokernel.π (Sigma.ι F a)), comp_zero]
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [comp_zero]
    by_cases hi : i = a
    · subst hi
      simp
    · have := Sigma.ι G ⟨i, hi⟩ ≫= hgh
      simpa [g, G] using this
  intro q hq
  obtain ⟨k, hk⟩ := Set.mem_iUnion.mp
    (simpleSubquotientClasses_sigma_subset_of_small hG hAB6 G
      (simpleSubquotientClasses_subset_of_epi g hq))
  exact Set.mem_iUnion₂.mpr ⟨k.1, k.2, hk⟩

end Helpers

/-- Renard A.IX, printed268/PDF274: a support partition that splits `X`
splits every actual subquotient `Y` of `X`. -/
theorem simpleSupportPartitionSubquotient
    (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSupportPartitionSubquotientStatement.{r,w,v,u} C := by
  intro hG hAB6 I _ S X _ hX N Y j p _ _ _
  let : HasCoproducts.{r} C := hG.1
  obtain ⟨hpart, hSX, hSumX, hIsoX⟩ := hX
  have hSY : ∀ i : I, HasCoproduct fun P : simpleSupportSubobjects (S i) Y =>
      ((P : Subobject Y) : C) := fun i => by
    have := hasCoproductsOfShape_of_small.{r} C (simpleSupportSubobjects (S i) Y)
    infer_instance
  let : HasCoproductsOfShape I C := hasCoproductsOfShape_of_small.{r} C I
  refine ⟨hpart, hSY, inferInstance, ?_⟩
  have hsupp : ∀ (Z : C) [∀ i : I, Small.{r} (simpleSupportSubobjects (S i) Z)]
      [∀ i : I, HasCoproduct fun P : simpleSupportSubobjects (S i) Z =>
        ((P : Subobject Z) : C)] (i : I),
      HasSimpleSupport (S i) (simpleSupportSum (S i) Z : C) := by
    intro Z _ _ i
    exact (simpleSupportSumSupport C : SimpleSupportSumSupportStatement.{r} C)
      hG hAB6 (S i) (hpart.subset i) Z
  have hempty : ∀ Z : C, simpleSubquotientClasses Z = ∅ ↔ IsZero Z :=
    (simpleSubquotientEmpty C : SimpleSubquotientEmptyStatement.{r} C) hG hAB6
  have hcover : ∀ (Z : C) (q : ObjectClass C), q ∈ simpleSubquotientClasses Z →
      ∃ a, q ∈ S a := by
    intro Z q hq
    have hq' : q ∈ ⋃ i, S i := by
      rw [hpart.2]
      exact simpleSubquotientClasses_subset_simpleClasses Z hq
    exact Set.mem_iUnion.mp hq'
  let FY : I → C := fun i => (simpleSupportSum (S i) Y : C)
  let FX : I → C := fun i => (simpleSupportSum (S i) X : C)
  let φ : (∐ FY) ⟶ Y := simpleSupportPartitionDesc S Y
  -- The kernel of `φ` meets no block.
  have hmono : Mono φ := by
    refine Preadditive.mono_of_isZero_kernel _ ((hempty _).mp ?_)
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    obtain ⟨a, ha⟩ := hcover _ q hq
    have hfac : Sigma.ι FY a ≫ φ = (simpleSupportSum (S a) Y).arrow :=
      ι_simpleSupportPartitionDesc S Y a
    have : Mono (Sigma.ι FY a) := mono_of_mono_fac hfac
    have hm : Mono (kernel.ι φ ≫ cokernel.π (Sigma.ι FY a)) := by
      refine Preadditive.mono_of_cancel_zero _ fun {T} h hh => ?_
      rw [← Category.assoc] at hh
      have h1 : Abelian.monoLift (Sigma.ι FY a) (h ≫ kernel.ι φ) hh ≫ Sigma.ι FY a =
          h ≫ kernel.ι φ :=
        Abelian.monoLift_comp _ _ _
      have h2 : Abelian.monoLift (Sigma.ι FY a) (h ≫ kernel.ι φ) hh = 0 := by
        rw [← cancel_mono (simpleSupportSum (S a) Y).arrow, zero_comp, ← hfac,
          ← Category.assoc, h1, Category.assoc, kernel.condition, comp_zero]
      rw [← cancel_mono (kernel.ι φ), ← h1, h2, zero_comp, zero_comp]
    obtain ⟨b, hba, hqb⟩ := Set.mem_iUnion₂.mp
      (simpleSubquotientClasses_cokernel_sigmaι_subset hG hAB6 FY a
        (simpleSubquotientClasses_subset_of_mono
          (kernel.ι φ ≫ cokernel.π (Sigma.ι FY a)) hq))
    exact Set.disjoint_left.mp (hpart.1 hba) (hsupp Y b hqb) ha
  -- The cokernel of `φ` meets no block.
  have hepi : Epi φ := by
    refine Preadditive.epi_of_isZero_cokernel _ ((hempty _).mp ?_)
    refine Set.eq_empty_iff_forall_notMem.mpr fun q hq => ?_
    obtain ⟨a, ha⟩ := hcover _ q hq
    let EX := simpleSupportSum (S a) X
    let EY := simpleSupportSum (S a) Y
    let fst := pullback.fst j EX.arrow
    have hP : HasSimpleSupport (S a) (pullback j EX.arrow) :=
      HasSimpleSupport.of_mono (pullback.snd j EX.arrow) (hsupp X a)
    have hle : imageSubobject (fst ≫ p) ≤ EY :=
      le_simpleSupportSum (S a) Y
        (HasSimpleSupport.of_epi (factorThruImageSubobject (fst ≫ p)) hP)
    have hfac : fst ≫ p =
        (factorThruImageSubobject (fst ≫ p) ≫ Subobject.ofLE _ _ hle) ≫ EY.arrow := by
      rw [Category.assoc, Subobject.ofLE_arrow, imageSubobject_arrow_comp]
    let d : cokernel fst ⟶ cokernel φ := cokernel.desc fst (p ≫ cokernel.π φ) (by
      rw [← Category.assoc, hfac, Category.assoc]
      have : EY.arrow ≫ cokernel.π φ = 0 := by
        rw [← ι_simpleSupportPartitionDesc S Y a, Category.assoc]
        exact (Sigma.ι FY a) ≫= cokernel.condition φ |>.trans comp_zero
      rw [this, comp_zero])
    have hd : Epi d := epi_of_epi_fac (cokernel.π_desc fst (p ≫ cokernel.π φ) _)
    have hsq := IsPullback.of_hasPullback j EX.arrow
    have := Abelian.mono_cokernel_map_of_isPullback hsq
    let e : cokernel (Sigma.ι FX a) ⟶ cokernel EX.arrow :=
      cokernel.desc _ (simpleSupportPartitionDesc S X ≫ cokernel.π EX.arrow) (by
        rw [← Category.assoc, ι_simpleSupportPartitionDesc, cokernel.condition])
    have he : Epi e := by
      have := hIsoX
      exact epi_of_epi_fac (cokernel.π_desc _ _ _)
    have hq1 := simpleSubquotientClasses_subset_of_epi d hq
    have hq2 := simpleSubquotientClasses_subset_of_mono
      (cokernel.map _ _ _ _ hsq.w) hq1
    have hq3 := simpleSubquotientClasses_subset_of_epi e hq2
    obtain ⟨b, hba, hqb⟩ := Set.mem_iUnion₂.mp
      (simpleSubquotientClasses_cokernel_sigmaι_subset hG hAB6 FX a hq3)
    exact Set.disjoint_left.mp (hpart.1 hba) (hsupp X b hqb) ha
  exact isIso_of_mono_of_epi φ

end Langlands.Renard

import Langlands.CategoryTheory.Renard.SimpleSubquotientSubobjectQuotient
import Langlands.CategoryTheory.Renard.SimpleSubquotientEmpty

/-!
# Simple subquotients of arbitrary indexed subobject sums

Renard A.VI.3, unnumbered Lemma (iii), printed264/PDF270.
The proof uses finite partial sums of the supplied family and source AB5.
-/

universe w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

section

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- A morphism out of an actual subobject least upper bound vanishes if
it vanishes on every member. -/
theorem hom_eq_zero_of_subobject_isLUB {X Y : C} {s : Set (Subobject X)}
    {U : Subobject X} (hU : IsLUB s U) (p : (U : C) ⟶ Y)
    (hz : ∀ P (hP : P ∈ s), Subobject.ofLE P U (hU.1 hP) ≫ p = 0) : p = 0 := by
  let K : Subobject X := Subobject.mk (kernel.ι p ≫ U.arrow)
  have hUK : U ≤ K := hU.2 (by
    intro P hP
    exact Subobject.le_mk_of_comm
      (kernel.lift p (Subobject.ofLE P U (hU.1 hP)) (hz P hP)) (by simp))
  have hfac : Subobject.ofLE U K hUK ≫
      (Subobject.underlyingIso (kernel.ι p ≫ U.arrow)).hom ≫ kernel.ι p = 𝟙 (U : C) := by
    apply (cancel_mono U.arrow).mp
    calc
      (Subobject.ofLE U K hUK ≫
          (Subobject.underlyingIso (kernel.ι p ≫ U.arrow)).hom ≫ kernel.ι p) ≫ U.arrow =
          Subobject.ofLE U K hUK ≫
            (Subobject.underlyingIso (kernel.ι p ≫ U.arrow)).hom ≫
              (kernel.ι p ≫ U.arrow) := by simp only [Category.assoc]
      _ = Subobject.ofLE U K hUK ≫ K.arrow := by
        rw [Subobject.underlyingIso_hom_comp_eq_mk]
      _ = (𝟙 (U : C)) ≫ U.arrow := by simp
  calc
    p = (Subobject.ofLE U K hUK ≫
        (Subobject.underlyingIso (kernel.ι p ≫ U.arrow)).hom ≫ kernel.ι p) ≫ p := by
      rw [hfac, Category.id_comp]
    _ = 0 := by simp

/-- The simple subquotient classes of a binary sum are the union of the
classes of its two summands, in every abelian category. -/
theorem simpleSubquotientClasses_sup {X : C} (P Q : Subobject X) :
    simpleSubquotientClasses ((P ⊔ Q : Subobject X) : C) =
      simpleSubquotientClasses (P : C) ∪ simpleSubquotientClasses (Q : C) := by
  let iP := Subobject.ofLE P (P ⊔ Q) le_sup_left
  let iQ := Subobject.ofLE Q (P ⊔ Q) le_sup_right
  let R : Subobject ((P ⊔ Q : Subobject X) : C) := Subobject.mk iP
  let π := cokernel.π R.arrow
  have hiP : iP ≫ π = 0 := by
    rw [← Subobject.underlyingIso_arrow iP, Category.assoc]
    simp only [π, R, cokernel.condition, comp_zero]
  have : Epi (iQ ≫ π) := Preadditive.epi_of_cancel_zero _ (by
    intro Z f hf
    have hπ : π ≫ f = 0 := hom_eq_zero_of_subobject_isLUB isLUB_pair _ (by
      intro T hT
      rcases Set.mem_insert_iff.mp hT with rfl | hT
      · change iP ≫ π ≫ f = 0
        rw [← Category.assoc, hiP, zero_comp]
      · have hTQ : T = Q := Set.mem_singleton_iff.mp hT
        subst T
        simpa only [Category.assoc] using hf)
    exact zero_of_epi_comp π hπ)
  apply Set.Subset.antisymm
  · intro q hq
    rcases simpleSubquotientClasses_subset_union ((P ⊔ Q : Subobject X) : C) R hq with hq | hq
    · exact Or.inl (simpleSubquotientClasses_subset_of_mono
        (Subobject.underlyingIso iP).hom hq)
    · exact Or.inr (simpleSubquotientClasses_subset_of_epi (iQ ≫ π) hq)
  · exact Set.union_subset (simpleSubquotientClasses_subset_of_mono iP)
      (simpleSubquotientClasses_subset_of_mono iQ)

/-- The finite partial-sum identity, including the empty partial sum. -/
theorem simpleSubquotientClasses_finset_sup (hG : IsSourceGrothendieck.{w} C)
    (hAB6 : SourceAB6 C) {X : C} {I : Type w} (F : I → Subobject X) (s : Finset I) :
    simpleSubquotientClasses ((s.sup F : Subobject X) : C) =
      ⋃ i ∈ s, simpleSubquotientClasses (F i : C) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sup_empty, Finset.notMem_empty, Set.iUnion_of_empty, Set.iUnion_empty]
    exact (simpleSubquotientEmpty C hG hAB6 _).mpr
      ((isZero_zero C).of_iso Subobject.botCoeIsoZero)
  | @insert i s hi ih =>
    rw [Finset.sup_insert, simpleSubquotientClasses_sup, ih]
    simp

/-- For a nonempty directed family, source AB5 forces every simple
subquotient of its least upper bound to occur in a member. -/
theorem simpleSubquotientClasses_directed_isLUB
    (hD : DirectedSubobjectSumsDistribute.{w} C)
    {X : C} {I : Type w} [Nonempty I] (F : I → Subobject X)
    (hF : Directed (· ≤ ·) F) (U : Subobject X) (hU : IsLUB (Set.range F) U) :
    simpleSubquotientClasses (U : C) = ⋃ i, simpleSubquotientClasses (F i : C) := by
  classical
  apply Set.Subset.antisymm
  · rintro q ⟨A, B, h, hs, rfl⟩
    have := hs
    let S := cokernel (Subobject.ofLE A B h)
    let M : Subobject X := Subobject.mk (B.arrow ≫ U.arrow)
    let p : (M : C) ⟶ S := (Subobject.underlyingIso (B.arrow ≫ U.arrow)).hom ≫
      cokernel.π (Subobject.ofLE A B h)
    have : Epi p := by dsimp [p]; infer_instance
    have hMU : M ≤ U := Subobject.mk_le_of_comm B.arrow rfl
    obtain ⟨V, hV, hInt⟩ := hD X I inferInstance F hF M
    have hVU : V = U := hV.unique hU
    rw [hVU, inf_eq_left.mpr hMU] at hInt
    have hex : ∃ i, Subobject.ofLE (M ⊓ F i) M inf_le_left ≫ p ≠ 0 := by
      by_contra hn
      have hz (i : I) : Subobject.ofLE (M ⊓ F i) M inf_le_left ≫ p = 0 := by
        by_contra hni
        exact hn ⟨i, hni⟩
      have hp0 : p = 0 := hom_eq_zero_of_subobject_isLUB hInt p (by
        rintro _ ⟨i, rfl⟩
        exact hz i)
      exact id_nonzero S (zero_of_epi_comp p (by simpa using hp0))
    obtain ⟨i, hi⟩ := hex
    have : Epi (Subobject.ofLE (M ⊓ F i) M inf_le_left ≫ p) :=
      epi_of_nonzero_to_simple hi
    exact Set.mem_iUnion.mpr ⟨i, objectClass_mem_simpleSubquotientClasses_of_mono_epi
      (Subobject.ofLE (M ⊓ F i) (F i) inf_le_right)
      (Subobject.ofLE (M ⊓ F i) M inf_le_left ≫ p)⟩
  · intro q hq
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hq
    exact simpleSubquotientClasses_subset_of_mono
      (Subobject.ofLE (F i) U (hU.1 ⟨i, rfl⟩)) hi

end

/-- Renard A.VI.3, unnumbered Lemma (iii), retaining the exact source
antecedents and the independent family, Hom and object universes. -/
theorem simpleSubquotientSum (C : Type u) [Category.{v} C] [Abelian C] :
    SimpleSubquotientSumStatement.{w} C := by
  intro hG hAB6
  let : HasCoproducts.{w} C := hG.1
  intro X I F
  classical
  let T : Finset I → Subobject X := fun s => s.sup F
  have hT : Directed (· ≤ ·) T := by
    intro s t
    exact ⟨s ∪ t, Finset.sup_mono Finset.subset_union_left,
      Finset.sup_mono Finset.subset_union_right⟩
  have hLUB : IsLUB (Set.range T) (subobjectSum F) := by
    constructor
    · rintro _ ⟨s, rfl⟩
      exact Finset.sup_le fun i _ => le_subobjectSum F i
    · intro Q hQ
      apply subobjectSum_le F
      intro i
      have hi := hQ ⟨{i}, rfl⟩
      simpa only [T, Finset.sup_singleton] using hi
  rw [simpleSubquotientClasses_directed_isLUB hG.2 T hT _ hLUB]
  ext q
  simp only [Set.mem_iUnion]
  constructor
  · rintro ⟨s, hs⟩
    have hs' : ∃ i, ∃ _ : i ∈ s, q ∈ simpleSubquotientClasses (F i : C) := by
      simpa only [T, simpleSubquotientClasses_finset_sup hG hAB6 F s,
        Set.mem_iUnion] using hs
    obtain ⟨i, _, hi⟩ := hs'
    exact ⟨i, hi⟩
  · rintro ⟨i, hi⟩
    exact ⟨{i}, by simpa only [T, Finset.sup_singleton] using hi⟩

end Langlands.Renard

import Langlands.CategoryTheory.Renard.SemisimplicityEquivalenceStatements
import Langlands.CategoryTheory.Renard.SubobjectComplementComparison
import Langlands.CategoryTheory.Renard.SimpleQuotient
import Langlands.CategoryTheory.Renard.IndexedSubobjectSums
import Mathlib.CategoryTheory.Subobject.Limits
import Mathlib.Logic.Small.Set
import Mathlib.Order.ModularLattice
import Mathlib.Order.SupIndep
import Mathlib.Order.Zorn

/-!
# Renard A.VII: proof of the semisimplicity equivalence

Proof of `Langlands.Renard.SemisimplicityEquivalenceStatement` (Renard,
French edition dated 9 July 2026, Appendix A.VII, printed page 265 / PDF
page 271). Under `Small.{r} (Subobject X)` and `r`-indexed coproducts, every
set of subobjects of `X` has a least upper bound, so the subobject lattice is
complete; it is modular in any abelian category, and Renard's AB5 makes
disjointness pass to directed sums. Simple subobjects are the atoms.

* (ii) ⇔ (iii): a maximal subobject disjoint from `P` (Zorn, AB5) is a
  complement; conversely, AB6 gives a simple subobject in every nonzero
  complement.
* (i) ⇒ (ii): a subobject through which every coproduct injection factors is
  `⊤`.
* (ii) ⇒ (i): a maximal independent set of simple subobjects (Zorn, AB5) has
  sum `⊤`, and the canonical map from the coproduct of the reindexed family is
  an isomorphism (epi by the sum, mono by AB5 on the finite subcoproducts).
* The size comparison reindexes the summands, which inject into the
  subobjects of the coproduct.
-/

universe r w v u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.Renard

noncomputable section

section Modular

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The map from the binary biproduct of two subobjects onto their sum is an
epimorphism. -/
theorem epi_biprod_desc_ofLE_sup {X : C} (A B : Subobject X) :
    Epi (biprod.desc (Subobject.ofLE A (A ⊔ B) le_sup_left)
      (Subobject.ofLE B (A ⊔ B) le_sup_right)) := by
  refine Preadditive.epi_of_cancel_zero _ (fun {R} g hg => ?_)
  exact eq_zero_of_ofLE_sup_comp _ (by simpa using congrArg (biprod.inl ≫ ·) hg)
    (by simpa using congrArg (biprod.inr ≫ ·) hg)

/-- The modular law for actual subobjects in an abelian category. -/
theorem subobject_sup_inf_le_assoc_of_le {X : C} {A : Subobject X} (B : Subobject X)
    {Z : Subobject X} (hAZ : A ≤ Z) : (A ⊔ B) ⊓ Z ≤ A ⊔ B ⊓ Z := by
  let g := biprod.desc (Subobject.ofLE A (A ⊔ B) le_sup_left)
    (Subobject.ofLE B (A ⊔ B) le_sup_right)
  have : Epi g := epi_biprod_desc_ofLE_sup A B
  let t := Subobject.ofLE ((A ⊔ B) ⊓ Z) (A ⊔ B) inf_le_left
  let a := pullback.fst g t ≫ biprod.fst ≫ A.arrow
  let b := pullback.fst g t ≫ biprod.snd ≫ B.arrow
  have hsum : pullback.snd g t ≫ ((A ⊔ B) ⊓ Z).arrow = a + b := by
    have ht : t ≫ (A ⊔ B).arrow = ((A ⊔ B) ⊓ Z).arrow := Subobject.ofLE_arrow _
    rw [← ht, ← Category.assoc, ← pullback.condition, Category.assoc]
    simp [g, a, b, biprod.desc_eq, Preadditive.comp_add]
  have haA : A.Factors a := by
    simpa only [a, Category.assoc] using
      Subobject.factors_comp_arrow (pullback.fst g t ≫ biprod.fst)
  have hbB : B.Factors b := by
    simpa only [b, Category.assoc] using
      Subobject.factors_comp_arrow (pullback.fst g t ≫ biprod.snd)
  have hbZ : Z.Factors b := by
    have hb : b = pullback.snd g t ≫ ((A ⊔ B) ⊓ Z).arrow +
        (-(pullback.fst g t ≫ biprod.fst)) ≫ A.arrow := by
      rw [hsum, Preadditive.neg_comp]
      simp only [a, Category.assoc]
      abel
    rw [hb]
    exact Subobject.factors_add _ _
      (Subobject.factors_of_le _ inf_le_right (Subobject.factors_comp_arrow _))
      (Subobject.factors_of_le _ hAZ (Subobject.factors_comp_arrow _))
  have hfac : (A ⊔ B ⊓ Z).Factors (pullback.snd g t ≫ ((A ⊔ B) ⊓ Z).arrow) := by
    rw [hsum]
    exact Subobject.factors_add _ _ (Subobject.factors_of_le _ le_sup_left haA)
      (Subobject.factors_of_le _ le_sup_right
        ((Subobject.inf_factors _).mpr ⟨hbB, hbZ⟩))
  have hzero : ((A ⊔ B) ⊓ Z).arrow ≫ cokernel.π (A ⊔ B ⊓ Z).arrow = 0 := by
    rw [← cancel_epi (pullback.snd g t), comp_zero, ← Category.assoc,
      ← Subobject.factorThru_arrow _ _ hfac, Category.assoc, cokernel.condition, comp_zero]
  obtain ⟨l, hl⟩ := exists_lift_of_comp_cokernel_π _ _ hzero
  exact Subobject.le_of_comm l hl

/-- Actual subobjects of an object of an abelian category form a modular lattice. -/
instance subobjectIsModularLattice (X : C) : IsModularLattice (Subobject X) :=
  ⟨fun y _ h => subobject_sup_inf_le_assoc_of_le y h⟩

end Modular

section CompleteLattice

/-- An `r`-small set is the range of its members reindexed by `Shrink.{r}`. -/
theorem range_shrink_coe {α : Type w} (s : Set α) [Small.{r} s] :
    Set.range (fun j : Shrink.{r} s => ((equivShrink s).symm j : α)) = s := by
  ext a
  constructor
  · rintro ⟨j, rfl⟩
    exact ((equivShrink s).symm j).2
  · intro ha
    exact ⟨equivShrink s ⟨a, ha⟩, by simp⟩

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- With `r`-indexed coproducts, every set of actual subobjects of an object
whose subobject type is `r`-small has a least upper bound. -/
theorem exists_isLUB_of_small (hcop : HasCoproducts.{r} C) {X : C}
    [Small.{r} (Subobject X)] (s : Set (Subobject X)) :
    ∃ U : Subobject X, IsLUB s U := by
  obtain ⟨U, hU⟩ := hasIndexedSubobjectSums_of_hasCoproducts hcop X (Shrink.{r} s)
    (fun j => ((equivShrink s).symm j : Subobject X))
  exact ⟨U, by rwa [range_shrink_coe] at hU⟩

/-- The complete lattice on the actual subobjects of `X` given by chosen least
upper bounds. Its order, binary operations and bounds are the existing ones. -/
abbrev subobjectCompleteLatticeOfIsLUB {X : C} (h : ∀ s : Set (Subobject X), ∃ U, IsLUB s U) :
    CompleteLattice (Subobject X) where
  __ := (inferInstance : Lattice (Subobject X))
  __ := (inferInstance : BoundedOrder (Subobject X))
  sSup s := (h s).choose
  isLUB_sSup s := (h s).choose_spec
  sInf s := (h (lowerBounds s)).choose
  isGLB_sInf s := isLUB_lowerBounds.mp (h (lowerBounds s)).choose_spec

/-- Renard's AB5 in disjointness form: a subobject disjoint from every member of
a nonempty directed `r`-small set of subobjects is disjoint from its least upper
bound. -/
theorem disjoint_of_isLUB_of_directedOn (hD : DirectedSubobjectSumsDistribute.{r} C)
    {X : C} {D : Set (Subobject X)} [Small.{r} D] (hne : D.Nonempty)
    (hdir : DirectedOn (· ≤ ·) D) {U : Subobject X} (hU : IsLUB D U) {N : Subobject X}
    (hN : ∀ d ∈ D, Disjoint N d) : Disjoint N U := by
  let F : Shrink.{r} D → Subobject X := fun j => ((equivShrink D).symm j : Subobject X)
  have : Nonempty (Shrink.{r} D) := ⟨equivShrink D ⟨_, hne.some_mem⟩⟩
  have hF : Directed (· ≤ ·) F := by
    intro i j
    obtain ⟨z, hz, hiz, hjz⟩ :=
      hdir _ ((equivShrink D).symm i).2 _ ((equivShrink D).symm j).2
    exact ⟨equivShrink D ⟨z, hz⟩, by simpa [F] using hiz, by simpa [F] using hjz⟩
  obtain ⟨U', hU', hNU'⟩ := hD X (Shrink.{r} D) this F hF N
  rw [range_shrink_coe] at hU'
  rw [hU.unique hU', disjoint_iff_inf_le]
  refine hNU'.2 ?_
  rintro _ ⟨j, rfl⟩
  exact disjoint_iff_inf_le.mp (hN _ ((equivShrink D).symm j).2)

end CompleteLattice

section Complements

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- Renard A.VII (ii) ⇒ (iii), lattice form: if `X` is the sum of its simple
subobjects, then its subobject lattice is complemented. A complement of `P` is
a maximal subobject disjoint from `P`, found by Zorn's lemma and AB5. -/
theorem complementedLattice_of_isSumOfSimpleSubobjects (hG : IsSourceGrothendieck.{r} C)
    {X : C} [Small.{r} (Subobject X)] (h : IsSumOfSimpleSubobjects X) :
    ComplementedLattice (Subobject X) := by
  let := subobjectCompleteLatticeOfIsLUB (exists_isLUB_of_small hG.1 (X := X))
  refine ⟨fun P => ?_⟩
  obtain ⟨Q, hQ, hmax⟩ := zorn_le₀ {Q : Subobject X | Disjoint P Q} (by
    intro c hc hchain
    rcases c.eq_empty_or_nonempty with rfl | hne
    · exact ⟨⊥, disjoint_bot_right, fun _ h => h.elim⟩
    · exact ⟨sSup c, disjoint_of_isLUB_of_directedOn hG.2 hne hchain.directedOn
        (isLUB_sSup c) hc, fun _ hz => le_sSup hz⟩)
  refine ⟨Q, hQ, codisjoint_iff.mpr (top_le_iff.mp (h.2 fun a ha => ?_))⟩
  by_contra hle
  have hatom : IsAtom a := (subobject_simple_iff_isAtom a).mp ha
  have hdis : Disjoint P (Q ⊔ a) :=
    hQ.disjoint_sup_right_of_disjoint_sup_left (hatom.not_le_iff_disjoint.mp hle).symm
  exact hle ((le_sup_right.trans (hmax hdis le_sup_left)).trans le_sup_right)

/-- Complementedness passes from the subobjects of `Y` to the subobjects of the
object underlying a subobject of `Y`. -/
theorem complementedLattice_subobject {Y : C} [ComplementedLattice (Subobject Y)]
    (P : Subobject Y) : ComplementedLattice (Subobject (P : C)) :=
  (Subobject.subobjectOrderIso P).symm.complementedLattice

/-- With source AB6, a nonzero object with complemented subobject lattice has a
simple subobject: a nonzero finite-type subobject `B` has a maximal proper
subobject, and its complement in the subobjects of `B` is simple. -/
theorem exists_simple_subobject_of_complementedLattice (hAB6 : SourceAB6 C) {Y : C}
    (hY : ¬ IsZero Y) [ComplementedLattice (Subobject Y)] :
    ∃ A : Subobject Y, Simple (A : C) := by
  obtain ⟨B, hBfinite, hBzero⟩ := exists_nonzero_finiteType_subobject hAB6 hY
  obtain ⟨M, -, hs⟩ := exists_simple_cokernel_of_finiteType hBzero hBfinite
  have : Simple (cokernel (Subobject.ofLE M ⊤ le_top)) :=
    Simple.of_iso ((cokernelCompIsIso (Subobject.ofLE M ⊤ le_top) (⊤ : Subobject _).arrow).symm ≪≫
      cokernelIsoOfEq (Subobject.ofLE_arrow le_top))
  have hM : IsCoatom M := ((simple_cokernel_ofLE_iff_covBy M ⊤ le_top).mp this).isCoatom
  have := complementedLattice_subobject B
  obtain ⟨N, hMN⟩ := exists_isCompl M
  have : Simple (N : C) := (subobject_simple_iff_isAtom N).mpr (hMN.symm.isAtom_iff_isCoatom.mpr hM)
  exact ⟨Subobject.mk (N.arrow ≫ B.arrow), Simple.of_iso (Subobject.underlyingIso _)⟩

/-- Renard A.VII (iii) ⇒ (ii), lattice form: with source AB6, an object whose
subobject lattice is complemented is the sum of its simple subobjects. -/
theorem isSumOfSimpleSubobjects_of_complementedLattice (hAB6 : SourceAB6 C) {X : C}
    [ComplementedLattice (Subobject X)] : IsSumOfSimpleSubobjects X := by
  refine ⟨fun _ _ => le_top, fun G hG => ?_⟩
  obtain ⟨H, hGH⟩ := exists_isCompl G
  by_cases hH : H = ⊥
  · rw [← hGH.sup_eq_top, hH, sup_bot_eq]
  have hHzero : ¬ IsZero (H : C) := by
    intro hz
    exact hH ((Subobject.mk_arrow H).symm.trans
      (Subobject.mk_eq_bot_iff_zero.mpr (hz.eq_of_src _ _)))
  have := complementedLattice_subobject H
  obtain ⟨A, hA⟩ := exists_simple_subobject_of_complementedLattice hAB6 hHzero
  let A' : Subobject X := Subobject.mk (A.arrow ≫ H.arrow)
  have hA' : Simple (A' : C) := Simple.of_iso (Subobject.underlyingIso _)
  have hle : A' ≤ G ⊓ H := le_inf (hG hA') (Subobject.mk_le_of_comm A.arrow rfl)
  rw [hGH.inf_eq_bot, le_bot_iff, Subobject.mk_eq_bot_iff_zero] at hle
  have hAzero : A.arrow = 0 := by
    rw [← cancel_mono H.arrow, hle, zero_comp]
  have : IsAtom A := (subobject_simple_iff_isAtom A).mp hA
  exact (this.ne_bot ((Subobject.mk_arrow A).symm.trans
    (Subobject.mk_eq_bot_iff_zero.mpr hAzero))).elim

/-- Renard A.VII (ii) ⇔ (iii) under the source hypotheses. -/
theorem isSumOfSimpleSubobjects_iff_everySubobjectHasComplement
    (hG : IsSourceGrothendieck.{r} C) (hAB6 : SourceAB6 C) (X : C)
    [Small.{r} (Subobject X)] :
    IsSumOfSimpleSubobjects X ↔ EverySubobjectHasComplement X := by
  rw [everySubobjectComplementedLattice C X]
  exact ⟨complementedLattice_of_isSumOfSimpleSubobjects hG,
    fun _ => isSumOfSimpleSubobjects_of_complementedLattice hAB6⟩

end Complements

section Reducible

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The injections of a colimit cofan in an abelian category are monomorphisms:
each has a retraction which vanishes on the other summands. -/
theorem mono_cofan_inj {I : Type w} {S : I → C} {X : C} {ι : ∀ i, S i ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) (i : I) : Mono (ι i) := by
  classical
  let p : X ⟶ S i := Cofan.IsColimit.desc hc (Pi.single i (𝟙 (S i)))
  have hp : ι i ≫ p = 𝟙 _ := by
    simpa [p] using Cofan.IsColimit.fac hc (Pi.single i (𝟙 (S i))) i
  exact (IsSplitMono.mk' ⟨p, hp⟩).mono

/-- A subobject through which every injection of a colimit cofan factors is `⊤`. -/
theorem eq_top_of_factors_cofan {I : Type w} {S : I → C} {X : C} {ι : ∀ i, S i ⟶ X}
    (hc : IsColimit (Cofan.mk X ι)) {G : Subobject X} (h : ∀ i, G.Factors (ι i)) :
    G = ⊤ := by
  let s : X ⟶ (G : C) := Cofan.IsColimit.desc hc fun i => G.factorThru (ι i) (h i)
  have hs : s ≫ G.arrow = 𝟙 X := Cofan.IsColimit.hom_ext hc _ _ fun i => by
    have : ι i ≫ s = G.factorThru (ι i) (h i) :=
      Cofan.IsColimit.fac hc (fun i => G.factorThru (ι i) (h i)) i
    change ι i ≫ s ≫ G.arrow = ι i ≫ 𝟙 X
    rw [← Category.assoc, this, Subobject.factorThru_arrow, Category.comp_id]
  have : IsSplitEpi G.arrow := IsSplitEpi.mk' ⟨s, hs⟩
  have : IsIso G.arrow := isIso_of_mono_of_epi _
  exact Subobject.eq_top_of_isIso_arrow G

/-- Renard A.VII (i) ⇒ (ii), at any index size: a direct sum of simple objects
is the sum of its simple subobjects. -/
theorem isSumOfSimpleSubobjects_of_isCompletelyReducible {X : C}
    (h : IsCompletelyReducible.{w} X) : IsSumOfSimpleSubobjects X := by
  obtain ⟨I, S, ι, hS, ⟨hc⟩⟩ := h
  refine ⟨fun _ _ => le_top, fun G hG => (eq_top_of_factors_cofan hc fun i => ?_).ge⟩
  have := mono_cofan_inj hc i
  have := hS i
  have hsimple : Simple (Subobject.mk (ι i) : C) := Simple.of_iso (Subobject.underlyingIso _)
  exact Subobject.factors_of_le _ (hG hsimple) (Subobject.mk_factors_self _)

/-- A finite sum of morphisms, each factoring through the corresponding member
of a family of subobjects, factors through the finite supremum of the family. -/
theorem factors_finset_sum {J : Type w} {X Y : C} (T : Finset J) (E : J → Subobject X)
    (g : J → (Y ⟶ X)) (h : ∀ k ∈ T, (E k).Factors (g k)) :
    (T.sup E).Factors (∑ k ∈ T, g k) := by
  classical
  induction T using Finset.induction_on with
  | empty => simpa using Subobject.factors_zero
  | insert a T ha ih =>
    rw [Finset.sum_insert ha, Finset.sup_insert]
    exact Subobject.factors_add _ _
      (Subobject.factors_of_le _ le_sup_left (h a (Finset.mem_insert_self a T)))
      (Subobject.factors_of_le _ le_sup_right
        (ih fun k hk => h k (Finset.mem_insert_of_mem hk)))

/-- If `X` is the sum of its simple subobjects, then it is the sum of an
`r`-indexed family of simple subobjects each of which is disjoint from the sum
of finitely many others. The family is a maximal independent set of atoms of
the subobject lattice, found by Zorn's lemma and AB5. -/
theorem exists_independent_simple_family (hG : IsSourceGrothendieck.{r} C) {X : C}
    [Small.{r} (Subobject X)] (h : IsSumOfSimpleSubobjects X) :
    ∃ (J : Type r) (E : J → Subobject X), (∀ j, Simple (E j : C)) ∧
      IsLUB (Set.range E) ⊤ ∧
      ∀ (F : Finset J) (j : J), j ∉ F → Disjoint (E j) (F.sup E) := by
  let := subobjectCompleteLatticeOfIsLUB (exists_isLUB_of_small hG.1 (X := X))
  obtain ⟨s, -, ⟨hsa, hs⟩, hmax⟩ := zorn_subset_nonempty
    {s : Set (Subobject X) | (∀ a ∈ s, IsAtom a) ∧ sSupIndep s} (fun c hc hchain hne => by
      refine ⟨⋃₀ c, ⟨fun a ha => ?_, fun a ha => ?_⟩, fun s hs => Set.subset_sUnion_of_mem hs⟩
      · obtain ⟨t, ht, hat⟩ := Set.mem_sUnion.mp ha
        exact (hc ht).1 a hat
      · obtain ⟨t₀, ht₀, hat₀⟩ := Set.mem_sUnion.mp ha
        let D := (fun t => sSup (t \ {a})) '' {t | t ∈ c ∧ a ∈ t}
        refine disjoint_of_isLUB_of_directedOn hG.2 (D := D) ⟨_, t₀, ⟨ht₀, hat₀⟩, rfl⟩ ?_
          ⟨?_, fun u hu => sSup_le fun b hb => ?_⟩ ?_
        · rintro _ ⟨t₁, ⟨ht₁, hat₁⟩, rfl⟩ _ ⟨t₂, ⟨ht₂, hat₂⟩, rfl⟩
          rcases hchain.total ht₁ ht₂ with h12 | h21
          · exact ⟨_, ⟨t₂, ⟨ht₂, hat₂⟩, rfl⟩,
              sSup_le_sSup (Set.sdiff_subset_sdiff_left h12), le_rfl⟩
          · exact ⟨_, ⟨t₁, ⟨ht₁, hat₁⟩, rfl⟩, le_rfl,
              sSup_le_sSup (Set.sdiff_subset_sdiff_left h21)⟩
        · rintro _ ⟨t, ⟨ht, -⟩, rfl⟩
          exact sSup_le_sSup (Set.sdiff_subset_sdiff_left (Set.subset_sUnion_of_mem ht))
        · obtain ⟨hb, hba⟩ := hb
          obtain ⟨t, ht, hbt⟩ := Set.mem_sUnion.mp hb
          rcases hchain.total ht ht₀ with htt | htt
          · exact (le_sSup (show b ∈ t₀ \ {a} from ⟨htt hbt, hba⟩)).trans
              (hu ⟨t₀, ⟨ht₀, hat₀⟩, rfl⟩)
          · exact (le_sSup (show b ∈ t \ {a} from ⟨hbt, hba⟩)).trans
              (hu ⟨t, ⟨ht, htt hat₀⟩, rfl⟩)
        · rintro _ ⟨t, ⟨ht, hat⟩, rfl⟩
          exact (hc ht).2 hat) ∅ ⟨fun _ h => h.elim, sSupIndep_empty⟩
  have htop : sSup s = ⊤ := by
    refine top_le_iff.mp (h.2 fun a ha => ?_)
    by_contra hle
    have hatom : IsAtom a := (subobject_simple_iff_isAtom a).mp ha
    have hdis : Disjoint a (sSup s) := hatom.not_le_iff_disjoint.mp hle
    have hins : insert a s ∈ {s : Set (Subobject X) | (∀ a ∈ s, IsAtom a) ∧ sSupIndep s} := by
      refine ⟨fun b hb => ?_, fun b hb => ?_⟩
      · rcases hb with rfl | hb
        · exact hatom
        · exact hsa b hb
      · rcases hb with rfl | hb
        · exact hdis.mono_right (sSup_le_sSup fun x hx => by
            rcases hx with ⟨rfl | hx, hxb⟩
            · exact (hxb rfl).elim
            · exact hx)
        · have h1 : Disjoint (b ⊔ sSup (s \ {b})) a :=
            (hdis.mono_right (sup_le (le_sSup hb) (sSup_le_sSup Set.sdiff_subset))).symm
          refine ((hs hb).disjoint_sup_right_of_disjoint_sup_left h1).mono_right
            (sSup_le fun x hx => ?_)
          rcases hx with ⟨rfl | hx, hxb⟩
          · exact le_sup_right
          · exact le_sup_of_le_left (le_sSup ⟨hx, hxb⟩)
    exact hle (le_sSup (hmax hins (Set.subset_insert a s) (Set.mem_insert a s)))
  let E : Shrink.{r} s → Subobject X := fun j => ((equivShrink s).symm j : Subobject X)
  have hEs : ∀ j, E j ∈ s := fun j => ((equivShrink s).symm j).2
  have hEinj : Function.Injective E :=
    Subtype.val_injective.comp (equivShrink s).symm.injective
  refine ⟨Shrink.{r} s, E, fun j => (subobject_simple_iff_isAtom _).mpr (hsa _ (hEs j)), ?_,
    fun F j hj => (hs (hEs j)).mono_right (Finset.sup_le fun k hk =>
      le_sSup (show E k ∈ s \ {E j} from ⟨hEs k, fun hkj => hj (hEinj hkj ▸ hk)⟩))⟩
  rw [range_shrink_coe, ← htop]
  exact isLUB_sSup s

/-- With AB5, the canonical map from the coproduct of an `r`-indexed family of
subobjects which sum to `X`, each disjoint from the sum of finitely many
others, is an isomorphism. -/
theorem isIso_sigmaDesc_of_independent (hD : DirectedSubobjectSumsDistribute.{r} C) {X : C}
    {J : Type r} (E : J → Subobject X) [HasCoproduct fun j => (E j : C)]
    (hsum : IsLUB (Set.range E) ⊤)
    (hind : ∀ (F : Finset J) (j : J), j ∉ F → Disjoint (E j) (F.sup E)) :
    IsIso (Sigma.desc fun j => (E j).arrow) := by
  classical
  let S : J → C := fun j => (E j : C)
  let φ : ∐ S ⟶ X := Sigma.desc fun j => (E j).arrow
  have hιφ : ∀ j, Sigma.ι S j ≫ φ = (E j).arrow := fun j => Sigma.ι_comp_desc _ j
  have : Epi φ := by
    refine Preadditive.epi_of_cancel_zero _ (fun {R} g hg => ?_)
    have hk : kernelSubobject g = ⊤ := top_le_iff.mp (hsum.2 (by
      rintro _ ⟨j, rfl⟩
      exact le_kernelSubobject _ _ (by rw [← hιφ, Category.assoc, hg, comp_zero])))
    have := kernelSubobject_arrow_comp g
    rw [hk] at this
    rwa [← cancel_epi (⊤ : Subobject X).arrow, comp_zero]
  have hmono : ∀ j, Mono (Sigma.ι S j) := mono_cofan_inj (coproductIsCoproduct S)
  let p : ∀ j, ∐ S ⟶ S j := fun j => Sigma.desc (Pi.single j (𝟙 (S j)))
  have hιp : ∀ j, Sigma.ι S j ≫ p j = 𝟙 _ := fun j => by simp [p]
  have hιp' : ∀ j k, k ≠ j → Sigma.ι S j ≫ p k = 0 := fun j k hkj => by simp [p, hkj.symm]
  let Y : Finset J → Subobject (∐ S) := fun F => F.sup fun j => Subobject.mk (Sigma.ι S j)
  let e : Finset J → (∐ S ⟶ ∐ S) := fun F => ∑ j ∈ F, p j ≫ Sigma.ι S j
  have hιe : ∀ F, ∀ j ∈ F, Sigma.ι S j ≫ e F = Sigma.ι S j := by
    intro F j hj
    simp only [e, Preadditive.comp_sum]
    rw [Finset.sum_eq_single_of_mem j hj (fun k _ hkj => by
      rw [← Category.assoc, hιp' j k hkj, zero_comp])]
    rw [← Category.assoc, hιp, Category.id_comp]
  have hYe : ∀ F, Y F ≤ kernelSubobject (e F - 𝟙 _) := fun F => Finset.sup_le fun j hj =>
    Subobject.mk_le_of_comm _ (Subobject.factorThru_arrow _ _ (kernelSubobject_factors _ _
      (by rw [Preadditive.comp_sub, hιe F j hj, Category.comp_id, sub_self])))
  let N := kernelSubobject φ
  have hNY : ∀ F, Disjoint N (Y F) := by
    intro F
    let m := (N ⊓ Y F).arrow
    have hmφ : m ≫ φ = 0 :=
      (kernelSubobject_factors_iff φ m).mp (Subobject.inf_arrow_factors_left _ _)
    have hme : m = ∑ k ∈ F, (m ≫ p k) ≫ Sigma.ι S k := by
      have := (kernelSubobject_factors_iff _ m).mp
        (Subobject.factors_of_le _ (hYe F) (Subobject.inf_arrow_factors_right _ _))
      rw [Preadditive.comp_sub, Category.comp_id, sub_eq_zero] at this
      conv_lhs => rw [← this]
      simp only [e, Preadditive.comp_sum, Category.assoc]
    have hsum0 : ∑ k ∈ F, (m ≫ p k) ≫ (E k).arrow = 0 := by
      rw [← hmφ]
      conv_rhs => rw [hme]
      simp only [Preadditive.sum_comp, Category.assoc, hιφ]
    have hmp : ∀ j ∈ F, m ≫ p j = 0 := by
      intro j hj
      have heq : (m ≫ p j) ≫ (E j).arrow =
          ∑ k ∈ F.erase j, (-(m ≫ p k)) ≫ (E k).arrow := by
        rw [← Finset.add_sum_erase _ _ hj] at hsum0
        simp only [Preadditive.neg_comp, Finset.sum_neg_distrib]
        exact eq_neg_of_add_eq_zero_left hsum0
      have hfac : (E j ⊓ (F.erase j).sup E).Factors ((m ≫ p j) ≫ (E j).arrow) :=
        (Subobject.inf_factors _).mpr ⟨Subobject.factors_comp_arrow _,
          heq ▸ factors_finset_sum _ E _ fun k _ => Subobject.factors_comp_arrow _⟩
      rw [(hind (F.erase j) j (Finset.notMem_erase j F)).eq_bot,
        Subobject.bot_factors_iff_zero] at hfac
      rwa [← cancel_mono (E j).arrow, zero_comp]
    have hm : m = 0 := by
      rw [hme]
      exact Finset.sum_eq_zero fun k hk => by rw [hmp k hk, zero_comp]
    rw [disjoint_iff, ← Subobject.mk_arrow (N ⊓ Y F)]
    exact Subobject.mk_eq_bot_iff_zero.mpr hm
  have hYtop : IsLUB (Set.range Y) ⊤ := by
    refine ⟨fun _ _ => le_top, fun u hu => (eq_top_of_factors_cofan
      (coproductIsCoproduct S) fun j => ?_).ge⟩
    have hle : Subobject.mk (Sigma.ι S j) ≤ u := by
      refine le_trans ?_ (hu ⟨{j}, rfl⟩)
      simp [Y]
    exact Subobject.factors_of_le _ hle (Subobject.mk_factors_self _)
  have : Small.{r} (Set.range Y) := small_range Y
  have hN : N = ⊥ := disjoint_top.mp
    (disjoint_of_isLUB_of_directedOn hD (D := Set.range Y) ⟨_, ∅, rfl⟩
      (by
        rintro _ ⟨F, rfl⟩ _ ⟨G, rfl⟩
        exact ⟨_, ⟨F ∪ G, rfl⟩, Finset.sup_mono Finset.subset_union_left,
          Finset.sup_mono Finset.subset_union_right⟩)
      hYtop (by rintro _ ⟨F, rfl⟩; exact hNY F))
  have : Mono φ := Preadditive.mono_of_cancel_zero _ fun {R} g hg => by
    have := kernelSubobject_factors φ g hg
    rwa [show kernelSubobject φ = ⊥ from hN, Subobject.bot_factors_iff_zero] at this
  exact isIso_of_mono_of_epi φ

/-- Renard A.VII (ii) ⇒ (i) at the source size `r`. -/
theorem isCompletelyReducible_of_isSumOfSimpleSubobjects (hG : IsSourceGrothendieck.{r} C)
    {X : C} [Small.{r} (Subobject X)] (h : IsSumOfSimpleSubobjects X) :
    IsCompletelyReducible.{r} X := by
  obtain ⟨J, E, hE, hsum, hind⟩ := exists_independent_simple_family hG h
  have := hG.1
  have := isIso_sigmaDesc_of_independent hG.2 E hsum hind
  exact (IsCompletelyReducible.iff_exists_iso_sigma X).mpr
    ⟨J, fun j => (E j : C), inferInstance, hE,
      ⟨(asIso (Sigma.desc fun j => (E j).arrow)).symm⟩⟩

end Reducible

section Resize

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The index type of a coproduct of simple objects injects into the
subobjects of the coproduct: distinct summands give distinct subobjects, since
the projection onto one summand is the identity on it and zero on the others. -/
theorem small_of_simple_coproduct_index {I : Type w} (S : I → C)
    [HasCoproduct S] (hS : ∀ i, Simple (S i))
    [Small.{r} (Subobject (∐ S))] : Small.{r} I := by
  classical
  let F : I → Subobject (∐ S) := fun i => Subobject.mk (Sigma.ι S i)
  apply small_of_injective (f := F)
  intro i j hij
  by_contra hne
  let π : ∐ S ⟶ S i := Sigma.desc (Pi.single i (𝟙 (S i)))
  have hii : Sigma.ι S i ≫ π = 𝟙 (S i) := by simp [π]
  have hji : Sigma.ι S j ≫ π = 0 := by simp [π, hne]
  have hfac : Subobject.ofMkLEMk (Sigma.ι S i) (Sigma.ι S j) hij.le ≫ Sigma.ι S j =
      Sigma.ι S i := Subobject.ofMkLEMk_comp hij.le
  have hz : 𝟙 (S i) = 0 := by
    rw [← hii, ← hfac, Category.assoc, hji, comp_zero]
  let := hS i
  exact (id_nonzero (S i)) hz

/-- Complete reducibility at any index size implies complete reducibility at
size `r` for an object whose subobject type is `r`-small: the index type is
reindexed by `Shrink.{r}`. -/
theorem isCompletelyReducible_resize {X : C} [Small.{r} (Subobject X)]
    (h : IsCompletelyReducible.{w} X) : IsCompletelyReducible.{r} X := by
  obtain ⟨I, S, hcop, hS, ⟨e⟩⟩ := (IsCompletelyReducible.iff_exists_iso_sigma X).mp h
  let := hcop
  let : Small.{r} (Subobject (∐ S)) :=
    small_map (Subobject.mapIsoToOrderIso e.symm).toEquiv
  let : Small.{r} I := small_of_simple_coproduct_index S hS
  let g : Shrink.{r} I ≃ I := (equivShrink I).symm
  have hc : IsColimit (Cofan.mk (∐ S) (fun j => Sigma.ι S (g j))) :=
    IsColimit.ofIsoColimit
      ((IsColimit.precomposeHomEquiv (Discrete.functorComp S g) _).symm
        (IsColimit.whiskerEquivalence (coproductIsCoproduct S) (Discrete.equivalence g)))
      (Cocone.ext (Iso.refl _) (by rintro ⟨j⟩; simp))
  exact IsCompletelyReducible.of_iso e.symm
    ⟨Shrink.{r} I, fun j => S (g j), fun j => Sigma.ι S (g j), fun j => hS (g j), ⟨hc⟩⟩

/-- For an object whose subobject type is `r`-small, the semisimple-object
alias (index size `max u v`) agrees with complete reducibility at size `r`. -/
theorem isSemisimpleObject_iff_isCompletelyReducible {X : C} [Small.{r} (Subobject X)] :
    IsSemisimpleObject X ↔ IsCompletelyReducible.{r} X :=
  ⟨isCompletelyReducible_resize, isCompletelyReducible_resize⟩

end Resize

/-- Renard A.VII: under the source hypotheses, for an object whose subobject
type is `r`-small, the semisimple-object alias agrees with complete
reducibility at size `r`, and conditions (i), (ii) and (iii) are equivalent. -/
theorem semisimplicityEquivalence (C : Type u) [Category.{v} C] [Abelian C] :
    SemisimplicityEquivalenceStatement.{r} C := by
  intro hG hAB6 X _
  have h1 : IsSemisimpleObject X ↔ IsCompletelyReducible.{r} X :=
    isSemisimpleObject_iff_isCompletelyReducible
  exact ⟨h1, ⟨isSumOfSimpleSubobjects_of_isCompletelyReducible,
    fun h => h1.mpr (isCompletelyReducible_of_isSumOfSimpleSubobjects hG h)⟩,
    isSumOfSimpleSubobjects_iff_everySubobjectHasComplement hG hAB6 X⟩

end

end Langlands.Renard

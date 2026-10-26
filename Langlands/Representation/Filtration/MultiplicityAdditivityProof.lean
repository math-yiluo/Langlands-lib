import Langlands.Representation.Filtration.MultiplicityAdditivityStatement
import Langlands.Representation.Filtration.MultiplicityIndependenceProof
import Langlands.Representation.Filtration.MultiplicityTransportProof
import Langlands.Representation.Filtration.GradedRefinementProof
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Representation.Filtration.RepresentationLength

open scoped BigOperators

namespace Langlands

universe uK uG uA uB uC uT

namespace MultiplicityAdditivityProof

open LengthCriterionProof

/-- Counting a family of selected factor occurrences commutes with its
dependent disjoint union. -/
theorem card_selected_sigma {n : ℕ} (lengths : Fin n → ℕ)
    (P : ∀ i, Fin (lengths i) → Prop) :
    Nat.card {x : (Σ i, Fin (lengths i)) // P x.1 x.2} =
      ∑ i, Nat.card {j : Fin (lengths i) // P i j} := by
  let e : {x : (Σ i, Fin (lengths i)) // P x.1 x.2} ≃
      (Σ i, {j : Fin (lengths i) // P i j}) :=
    { toFun := fun x => ⟨x.1.1, x.1.2, x.2⟩
      invFun := fun x => ⟨⟨x.1, x.2.1⟩, x.2.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  exact (Nat.card_congr e).trans Nat.card_sigma

/-- Finite module length yields an actual finite composition series. -/
theorem exists_series {k : Type uK} [Field k] {G : Type uG} [Monoid G]
    {A : Rep.{uA} k G}
    (h : IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule) :
    ∃ n, HasCompositionSeriesLength A n := by
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
  exact ⟨s.length, hasCompositionSeriesLength_of_compositionSeries s h₀ h₁⟩

section Quotients

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {A : Rep.{uA} k G} {B : Rep.{uB} k G} {C : Rep.{uC} k G}

/-- Descending a surjection whose exact kernel is the lower interval
produces an actual equivalence of representations. -/
theorem quotient_equiv_of_surjective (S T : Subrepresentation A.ρ)
    (f : T.toRepresentation.IntertwiningMap B.ρ)
    (hker : ∀ x : T.toSubmodule, x ∈ lower S T ↔ f x = 0)
    (hf : Function.Surjective f) :
    Nonempty ((quotientRep S T).Equiv B.ρ) := by
  let L := (lower S T).liftQ f.toLinearMap (fun x hx => (hker x).mp hx)
  let F : (quotientRep S T).IntertwiningMap B.ρ :=
    { toLinearMap := L
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (lower S T) x
        exact LinearMap.congr_fun (f.isIntertwining' g) x }
  refine ⟨F.ofBijective ⟨?_, ?_⟩⟩
  · apply LinearMap.ker_eq_bot.mp
    exact Submodule.ker_liftQ_eq_bot _ _ _ (fun x hx => (hker x).mpr hx)
  · intro b
    obtain ⟨x, rfl⟩ := hf b
    exact ⟨(lower S T).mkQ x, rfl⟩

/-- The zero lower endpoint gives the original upper representation. -/
theorem quotient_bot_equiv (T : Subrepresentation A.ρ) :
    Nonempty ((quotientRep ⊥ T).Equiv T.toRepresentation) := by
  let f : T.toRepresentation.IntertwiningMap T.toRepresentation :=
    { toLinearMap := LinearMap.id
      isIntertwining' _ := rfl }
  apply quotient_equiv_of_surjective (B := Rep.of T.toRepresentation) ⊥ T f
  · intro x
    change (x : A) = 0 ↔ x = 0
    exact ⟨fun h => Subtype.ext h, fun h => congrArg Subtype.val h⟩
  · exact Function.surjective_id

/-- An injective intertwiner identifies its source with its actual range. -/
theorem source_equiv_range (i : A.ρ.IntertwiningMap B.ρ)
    (hi : Function.Injective i) :
    Nonempty (A.ρ.Equiv i.range.toRepresentation) := by
  let f : A.ρ.IntertwiningMap i.range.toRepresentation :=
    { toLinearMap := i.toLinearMap.rangeRestrict
      isIntertwining' g := by
        apply LinearMap.ext
        intro x
        exact Subtype.ext (LinearMap.congr_fun (i.isIntertwining' g) x) }
  refine ⟨f.ofBijective ⟨?_, ?_⟩⟩
  · intro x y h
    exact hi (congrArg Subtype.val h)
  · rintro ⟨b, a, rfl⟩
    exact ⟨a, rfl⟩

/-- The two successive quotients of the range filtration are the given
outer representations of a short exact sequence. -/
theorem two_step_equivs (i : A.ρ.IntertwiningMap B.ρ)
    (q : B.ρ.IntertwiningMap C.ρ) (hi : Function.Injective i)
    (hq : Function.Surjective q)
    (hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap) :
    Nonempty ((((LengthTwo.twoStep i.range).gradedRepresentation 0).ρ).Equiv A.ρ) ∧
      Nonempty ((((LengthTwo.twoStep i.range).gradedRepresentation 1).ρ).Equiv C.ρ) := by
  constructor
  · obtain ⟨e⟩ := quotient_bot_equiv i.range
    obtain ⟨f⟩ := source_equiv_range i hi
    exact ⟨e.trans f.symm⟩
  · let f : (⊤ : Subrepresentation B.ρ).toRepresentation.IntertwiningMap C.ρ :=
      { toLinearMap := q.toLinearMap.comp (⊤ : Subrepresentation B.ρ).toSubmodule.subtype
        isIntertwining' g := by
          apply LinearMap.ext
          intro x
          exact LinearMap.congr_fun (q.isIntertwining' g) x }
    apply quotient_equiv_of_surjective i.range ⊤ f
    · intro x
      change (x : B) ∈ LinearMap.range i.toLinearMap ↔ q (x : B) = 0
      rw [hex]
      rfl
    · intro c
      obtain ⟨b, rfl⟩ := hq c
      exact ⟨⟨b, Submodule.mem_top⟩, rfl⟩

end Quotients

end MultiplicityAdditivityProof

open LengthCriterionProof MultiplicityAdditivityProof

/-- Lift and concatenate the actual interval series, retaining the
bijection of every factor occurrence. -/
theorem jordanHolderFiltrationAdditivity :
    JordanHolderFiltrationAdditivityStatement.{uK, uG, uA, uT} := by
  classical
  intro k _ G _ A τ n s lengths counts H
  choose t ht hc using H
  have lift (i : Fin n) := actualQuotientSeriesLift k G A
    (s.subrepresentation i.castSucc) (s.subrepresentation i.succ)
    (s.monotone_subrepresentation (Fin.castSucc_le_succ i)) (lengths i) (t i) (ht i)
  choose c h₀ h₁ a ha using lift
  obtain ⟨m, r, hr, e, he⟩ :=
    GradedRefinementProof.assemble s (Equiv.refl _) c h₀ h₁
  let E : Fin m ≃ (Σ i, Fin (lengths i)) :=
    e.trans (Equiv.sigmaCongrRight a)
  have hgraded (j : Fin m) :
      Nonempty ((r.gradedRepresentation j).ρ.Equiv
        ((t (E j).1).gradedRepresentation (E j).2).ρ) := by
    obtain ⟨u⟩ := he j
    obtain ⟨v⟩ := ha (e j).1 (e j).2
    exact ⟨u.trans v⟩
  have hlen : m = ∑ i, lengths i := by
    have hcard := Nat.card_congr E
    simpa only [Nat.card_fin, Nat.card_sigma] using hcard
  have hcount : r.factorMultiplicity τ = ∑ i, counts i := by
    unfold ObjectRepFiltration.factorMultiplicity
    calc
      _ = Nat.card {x : (Σ i, Fin (lengths i)) //
          Nonempty (((t x.1).gradedRepresentation x.2).ρ.Equiv τ.ρ)} := by
        apply Nat.card_congr
        refine E.subtypeEquiv ?_
        intro j
        obtain ⟨u⟩ := hgraded j
        exact ⟨fun ⟨v⟩ => ⟨u.symm.trans v⟩, fun ⟨v⟩ => ⟨u.trans v⟩⟩
      _ = ∑ i, Nat.card {j : Fin (lengths i) //
          Nonempty (((t i).gradedRepresentation j).ρ.Equiv τ.ρ)} :=
        card_selected_sigma lengths
          (fun i j => Nonempty (((t i).gradedRepresentation j).ρ.Equiv τ.ρ))
      _ = ∑ i, counts i := Finset.sum_congr rfl (fun i _ => hc i)
  subst m
  exact ⟨r, hr, hcount⟩

/-- Finite ambient length makes every graded piece finite; reconstruction
then compares its independently chosen length and count to the ambient ones. -/
theorem jordanHolderFiltrationDecomposition :
    JordanHolderFiltrationDecompositionStatement.{uK, uG, uA, uT} := by
  classical
  intro k _ G _ A τ N M n hN hM s
  have hlength : repLength A.ρ = N := by
    obtain ⟨r, hr⟩ := hN
    exact repLength_eq_of_hasSimpleFactors r hr
  have hfin (i : Fin n) :
      IsFiniteLength (MonoidAlgebra k G) (s.gradedRepresentation i).ρ.asModule := by
    apply Module.length_ne_top_iff.mp
    have hi : repLength (s.gradedRepresentation i).ρ ≤ (N : ℕ∞) := by
      rw [← hlength, repLength_eq_sum_of_filtration s]
      exact Finset.single_le_sum
        (f := fun j : Fin n => repLength (s.gradedRepresentation j).ρ)
        (fun _ _ => zero_le) (Finset.mem_univ i)
    exact ne_top_of_le_ne_top (by simp) hi
  choose lengths t ht using fun i => exists_series (hfin i)
  let counts : Fin n → ℕ := fun i => (t i).factorMultiplicity τ
  have H : ∀ i : Fin n,
      ∃ r : ObjectRepFiltration (s.gradedRepresentation i) (lengths i),
        r.HasSimpleFactors ∧ r.factorMultiplicity τ = counts i :=
    fun i => ⟨t i, ht i, rfl⟩
  obtain ⟨r, hr, hc⟩ := jordanHolderFiltrationAdditivity k G A τ n s lengths counts H
  refine ⟨lengths, counts, H, ?_, ?_⟩
  · have heq := (repLength_eq_of_hasSimpleFactors r hr).symm.trans hlength
    exact_mod_cast heq
  · exact HasJordanHolderMultiplicity.unique ⟨_, r, hr, hc⟩ hM

/-- Apply the two-step actual range filtration and transport both supplied
outer series through the actual quotient equivalences. -/
theorem jordanHolderShortExactAdditivity :
    JordanHolderShortExactAdditivityStatement.{uK, uG, uA, uB, uC, uT} := by
  classical
  intro k _ G _ A B C τ i q hi hq hex mA mC hA hC
  let s := LengthTwo.twoStep i.range
  obtain ⟨⟨eA⟩, ⟨eC⟩⟩ := two_step_equivs i q hi hq hex
  obtain ⟨nA, tA, htA, hcA⟩ :=
    (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation 0) A
      τ τ eA (Representation.Equiv.refl _) mA).mpr hA
  obtain ⟨nC, tC, htC, hcC⟩ :=
    (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation 1) C
      τ τ eC (Representation.Equiv.refl _) mC).mpr hC
  have H : ∀ j : Fin 2,
      ∃ t : ObjectRepFiltration (s.gradedRepresentation j) (![nA, nC] j),
        t.HasSimpleFactors ∧ t.factorMultiplicity τ = ![mA, mC] j := by
    intro j
    fin_cases j
    · exact ⟨tA, htA, hcA⟩
    · exact ⟨tC, htC, hcC⟩
  obtain ⟨r, hr, hc⟩ :=
    jordanHolderFiltrationAdditivity k G B τ 2 s ![nA, nC] ![mA, mC] H
  exact ⟨_, r, hr, by simpa using hc⟩

/-- Finite ambient length and the two-step actual range filtration produce
outer series, whose transported counts add to the ambient count. -/
theorem jordanHolderShortExactDecomposition :
    JordanHolderShortExactDecompositionStatement.{uK, uG, uA, uB, uC, uT} := by
  classical
  intro k _ G _ A B C τ i q hi hq hex mB hB
  let s := LengthTwo.twoStep i.range
  obtain ⟨N, r, hr, hcount⟩ := hB
  obtain ⟨lengths, counts, H, -, hc⟩ :=
    jordanHolderFiltrationDecomposition k G B τ N mB 2 ⟨r, hr⟩
      ⟨N, r, hr, hcount⟩ s
  obtain ⟨⟨eA⟩, ⟨eC⟩⟩ := two_step_equivs i q hi hq hex
  refine ⟨counts 0, counts 1, ?_, ?_, ?_⟩
  · apply (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation 0) A
      τ τ eA (Representation.Equiv.refl _) (counts 0)).mp
    obtain ⟨t, ht, hc⟩ := H 0
    exact ⟨_, t, ht, hc⟩
  · apply (equivJordanHolderMultiplicityTransport k G (s.gradedRepresentation 1) C
      τ τ eC (Representation.Equiv.refl _) (counts 1)).mp
    obtain ⟨t, ht, hc⟩ := H 1
    exact ⟨_, t, ht, hc⟩
  · simpa using hc

/-- Decompose the range sequence of the injection and compare the actual
source count by multiplicity independence. -/
theorem jordanHolderInjectiveMonotonicity :
    JordanHolderInjectiveMonotonicityStatement.{uK, uG, uA, uB, uT} := by
  intro k _ G _ A B τ i hi mA mB hA hB
  let C : Rep.{uB} k G :=
    Rep.of (B.ρ.quotient i.range.toSubmodule
      (fun g _ hx => i.range.apply_mem_toSubmodule g hx))
  let q : B.ρ.IntertwiningMap C.ρ :=
    { toLinearMap := i.range.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change i.range.toSubmodule = LinearMap.ker i.range.toSubmodule.mkQ
    exact (Submodule.ker_mkQ _).symm
  obtain ⟨a, c, ha, -, hac⟩ :=
    jordanHolderShortExactDecomposition k G A B C τ i q hi
      (Submodule.mkQ_surjective _) hex mB hB
  have heq := HasJordanHolderMultiplicity.unique ha hA
  omega

/-- Decompose the kernel sequence of the surjection and compare the
actual target count by multiplicity independence. -/
theorem jordanHolderSurjectiveMonotonicity :
    JordanHolderSurjectiveMonotonicityStatement.{uK, uG, uA, uB, uT} := by
  intro k _ G _ A B τ q hq mA mB hA hB
  let K : Rep.{uA} k G := Rep.of q.ker.toRepresentation
  let i : K.ρ.IntertwiningMap A.ρ :=
    { toLinearMap := q.ker.toSubmodule.subtype
      isIntertwining' _ := rfl }
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap :=
    Submodule.range_subtype _
  obtain ⟨a, b, -, hb, hab⟩ :=
    jordanHolderShortExactDecomposition k G K A B τ i q
      (Submodule.injective_subtype _) hq hex mA hA
  have heq := HasJordanHolderMultiplicity.unique hb hB
  omega

/-- The actual inclusion and second projection form the split exact
sequence for the binary product. -/
theorem jordanHolderProductAdditivity :
    JordanHolderProductAdditivityStatement.{uK, uG, uA, uB, uT} := by
  intro k _ G _ A B τ mA mB hA hB
  let i := Representation.IntertwiningMap.inl k A.ρ B.ρ
  let q := Representation.IntertwiningMap.snd k A.ρ B.ρ
  apply jordanHolderShortExactAdditivity k G A (Rep.of (A.ρ.prod B.ρ)) B τ i q
      (fun x y h => congrArg Prod.fst h)
      (fun b => ⟨(0, b), rfl⟩)
      (LinearMap.range_inl k A B) mA mB hA hB

/-- The complete seven-clause additive multiplicity family, retaining all
six independent universe parameters and actual composition-series witnesses. -/
theorem jordanHolderMultiplicityAdditivity :
    JordanHolderMultiplicityAdditivityStatement.{uK, uG, uA, uB, uC, uT} :=
  ⟨jordanHolderFiltrationAdditivity, jordanHolderFiltrationDecomposition,
    jordanHolderShortExactAdditivity, jordanHolderShortExactDecomposition,
    jordanHolderInjectiveMonotonicity, jordanHolderSurjectiveMonotonicity,
    jordanHolderProductAdditivity⟩

end Langlands

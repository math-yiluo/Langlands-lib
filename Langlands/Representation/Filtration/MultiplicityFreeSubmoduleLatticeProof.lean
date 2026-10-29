import Langlands.Representation.Filtration.MultiplicityFreeSubmoduleLatticeStatement
import Langlands.Representation.Filtration.MultiplicityAdditivityProof
import Langlands.Representation.Filtration.MultiplicityTransportProof

/-! The constituent-support lattice of a multiplicity-free representation. -/

namespace Langlands

universe uK uG uA uT

namespace MultiplicityFreeSubmoduleLatticeProof

open LengthCriterionProof MultiplicityAdditivityProof

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {A : Rep.{uA} k G}

/-- The inclusion of nested invariant subspaces as an actual intertwiner. -/
def inclusion {S R : Subrepresentation A.ρ} (h : S ≤ R) :
    S.toRepresentation.IntertwiningMap R.toRepresentation where
  toLinearMap := Submodule.inclusion h
  isIntertwining' _ := rfl

/-- The inclusion of an invariant subspace into the ambient representation. -/
def subtype (S : Subrepresentation A.ρ) :
    S.toRepresentation.IntertwiningMap A.ρ where
  toLinearMap := S.toSubmodule.subtype
  isIntertwining' _ := rfl

/-- Finite ambient length gives every invariant subspace an actual finite
composition series. -/
theorem exists_series_sub {n : ℕ} (s : ObjectRepFiltration A n)
    (hs : s.HasSimpleFactors) (S : Subrepresentation A.ρ) :
    ∃ m, HasCompositionSeriesLength (Rep.of S.toRepresentation) m := by
  apply exists_series
  apply Module.length_ne_top_iff.mp
  have hA : repLength A.ρ = n := repLength_eq_of_hasSimpleFactors s hs
  have h := repLength_eq_subrepresentation_add_quotient A.ρ S
  have hle : repLength S.toRepresentation ≤ (n : ℕ∞) := by
    rw [← hA, h]
    exact le_self_add
  exact ne_top_of_le_ne_top (by simp) hle

/-- Every invariant subspace has a multiplicity for every target, witnessed
by an actual finite composition series. -/
theorem exists_mult_sub {n : ℕ} (s : ObjectRepFiltration A n)
    (hs : s.HasSimpleFactors) (S : Subrepresentation A.ρ) (τ : Rep.{uT} k G) :
    ∃ m, HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ m := by
  obtain ⟨_, t, ht⟩ := exists_series_sub s hs S
  exact ⟨_, _, t, ht, rfl⟩

/-- Multiplicities are monotone along inclusions of invariant subspaces. -/
theorem mult_mono {S R : Subrepresentation A.ρ} (h : S ≤ R) {τ : Rep.{uT} k G}
    {a b : ℕ} (ha : HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ a)
    (hb : HasJordanHolderMultiplicity (Rep.of R.toRepresentation) τ b) : a ≤ b :=
  jordanHolderInjectiveMonotonicity k G (Rep.of S.toRepresentation)
    (Rep.of R.toRepresentation) τ (inclusion h) (Submodule.inclusion_injective h)
    a b ha hb

/-- In a multiplicity-free series every target occurs at most once. -/
theorem factorMultiplicity_le_one {n : ℕ} (s : ObjectRepFiltration A n)
    (hfree : ∀ i j : Fin n,
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ) →
        i = j)
    (τ : Rep.{uT} k G) : s.factorMultiplicity τ ≤ 1 := by
  unfold ObjectRepFiltration.factorMultiplicity
  rw [Finite.card_le_one_iff_subsingleton]
  constructor
  rintro ⟨i, ⟨e⟩⟩ ⟨j, ⟨f⟩⟩
  exact Subtype.ext (hfree i j ⟨e.trans f.symm⟩)

/-- Every invariant subspace of a multiplicity-free representation has
multiplicities at most one. -/
theorem mult_le_one {n : ℕ} (s : ObjectRepFiltration A n) (hs : s.HasSimpleFactors)
    (hfree : ∀ i j : Fin n,
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ) →
        i = j)
    (S : Subrepresentation A.ρ) {τ : Rep.{uT} k G} {a : ℕ}
    (ha : HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ a) : a ≤ 1 :=
  (jordanHolderInjectiveMonotonicity k G (Rep.of S.toRepresentation) A τ
    (subtype S) (Submodule.injective_subtype _) a _ ha ⟨n, s, hs, rfl⟩).trans
    (factorMultiplicity_le_one s hfree τ)

/-- The diagonal inclusion of the meet into the product of the two summands. -/
noncomputable def diagonal (S R : Subrepresentation A.ρ) :
    (S ⊓ R).toRepresentation.IntertwiningMap
      (S.toRepresentation.prod R.toRepresentation) :=
  Representation.IntertwiningMap.prod (inclusion inf_le_left) (inclusion inf_le_right)

/-- The difference map from the product of the two summands onto the join. -/
noncomputable def difference (S R : Subrepresentation A.ρ) :
    (S.toRepresentation.prod R.toRepresentation).IntertwiningMap
      (S ⊔ R).toRepresentation :=
  (inclusion le_sup_left).comp
      (Representation.IntertwiningMap.fst k S.toRepresentation R.toRepresentation) -
    (inclusion le_sup_right).comp
      (Representation.IntertwiningMap.snd k S.toRepresentation R.toRepresentation)

theorem diagonal_injective (S R : Subrepresentation A.ρ) :
    Function.Injective (diagonal S R) := by
  intro x y h
  exact Subtype.ext (congrArg (fun p => ((Prod.fst p : S.toSubmodule) : A)) h)

theorem difference_surjective (S R : Subrepresentation A.ρ) :
    Function.Surjective (difference S R) := by
  rintro ⟨z, hz⟩
  obtain ⟨y, hy, w, hw, rfl⟩ := Submodule.mem_sup.mp hz
  refine ⟨(⟨y, hy⟩, ⟨-w, R.toSubmodule.neg_mem hw⟩), ?_⟩
  apply Subtype.ext
  change y - -w = y + w
  exact sub_neg_eq_add y w

theorem range_diagonal (S R : Subrepresentation A.ρ) :
    LinearMap.range (diagonal S R).toLinearMap =
      LinearMap.ker (difference S R).toLinearMap := by
  ext ⟨a, b⟩
  constructor
  · rintro ⟨x, hx⟩
    rw [← hx]
    apply Subtype.ext
    change (x : A) - (x : A) = 0
    exact sub_self _
  · intro h
    have h' : (a : A) - (b : A) = 0 := congrArg Subtype.val h
    have hab : (a : A) = b := sub_eq_zero.mp h'
    refine ⟨⟨a, a.2, hab ▸ b.2⟩, ?_⟩
    apply Prod.ext
    · exact Subtype.ext rfl
    · exact Subtype.ext hab

/-- The modular law for multiplicities, from the Mayer–Vietoris short exact
sequence `S ⊓ R → S × R → S ⊔ R`. -/
theorem mult_modular (S R : Subrepresentation A.ρ) {τ : Rep.{uT} k G}
    {a b c d : ℕ}
    (ha : HasJordanHolderMultiplicity (Rep.of (S ⊓ R).toRepresentation) τ a)
    (hb : HasJordanHolderMultiplicity (Rep.of (S ⊔ R).toRepresentation) τ b)
    (hc : HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ c)
    (hd : HasJordanHolderMultiplicity (Rep.of R.toRepresentation) τ d) :
    a + b = c + d := by
  have hP := jordanHolderProductAdditivity k G (Rep.of S.toRepresentation)
    (Rep.of R.toRepresentation) τ c d hc hd
  obtain ⟨a', b', ha', hb', hsum⟩ :=
    jordanHolderShortExactDecomposition k G (Rep.of (S ⊓ R).toRepresentation)
      (Rep.of (S.toRepresentation.prod R.toRepresentation))
      (Rep.of (S ⊔ R).toRepresentation) τ (diagonal S R) (difference S R)
      (diagonal_injective S R) (difference_surjective S R) (range_diagonal S R)
      (c + d) hP
  rw [HasJordanHolderMultiplicity.unique ha ha', HasJordanHolderMultiplicity.unique hb hb']
  exact hsum

/-- A proper inclusion of invariant subspaces with a finite upper series
strictly increases the multiplicity of some target in the ambient universe. -/
theorem exists_mult_lt {T S : Subrepresentation A.ρ} (hTS : T ≤ S) (hST : ¬ S ≤ T)
    {N : ℕ} (hN : HasCompositionSeriesLength (Rep.of S.toRepresentation) N) :
    ∃ τ : Rep.{uA} k G, ∀ a b : ℕ,
      HasJordanHolderMultiplicity (Rep.of T.toRepresentation) τ a →
      HasJordanHolderMultiplicity (Rep.of S.toRepresentation) τ b → a < b := by
  let i := inclusion hTS
  have hi : Function.Injective i := Submodule.inclusion_injective hTS
  let C : Rep.{uA} k G :=
    Rep.of (S.toRepresentation.quotient i.range.toSubmodule
      (fun g _ hx => i.range.apply_mem_toSubmodule g hx))
  let q : S.toRepresentation.IntertwiningMap C.ρ :=
    { toLinearMap := i.range.toSubmodule.mkQ
      isIntertwining' _ := rfl }
  have hq : Function.Surjective q := Submodule.mkQ_surjective _
  have hex : LinearMap.range i.toLinearMap = LinearMap.ker q.toLinearMap := by
    change i.range.toSubmodule = LinearMap.ker i.range.toSubmodule.mkQ
    exact (Submodule.ker_mkQ _).symm
  obtain ⟨t, ht⟩ := hN
  obtain ⟨-, -, -, ⟨nC, rC, hrC, -⟩, -⟩ :=
    jordanHolderShortExactDecomposition k G (Rep.of T.toRepresentation)
      (Rep.of S.toRepresentation) C C i q hi hq hex _ ⟨N, t, ht, rfl⟩
  have hnC : 0 < nC := by
    rcases Nat.eq_zero_or_pos nC with h0 | hpos
    · exfalso
      subst h0
      have hlen : repLength C.ρ = 0 := by
        exact_mod_cast repLength_eq_of_hasSimpleFactors rC hrC
      have hsub := repLength_eq_zero_iff.mp hlen
      apply hST
      intro x hx
      have hmk : q ⟨x, hx⟩ = 0 := Subsingleton.elim _ _
      have hmem : (⟨x, hx⟩ : S.toSubmodule) ∈ LinearMap.ker q.toLinearMap := hmk
      rw [← hex] at hmem
      obtain ⟨y, hy⟩ := hmem
      have hxy : (y : A) = x := congrArg Subtype.val hy
      rw [← hxy]
      exact y.2
    · exact hpos
  refine ⟨rC.gradedRepresentation ⟨0, hnC⟩, ?_⟩
  intro a b ha hb
  obtain ⟨a', c', ha', hc', hsum⟩ :=
    jordanHolderShortExactDecomposition k G (Rep.of T.toRepresentation)
      (Rep.of S.toRepresentation) C (rC.gradedRepresentation ⟨0, hnC⟩) i q hi hq hex
      b hb
  have hc : rC.factorMultiplicity (rC.gradedRepresentation ⟨0, hnC⟩) = c' :=
    HasJordanHolderMultiplicity.unique ⟨nC, rC, hrC, rfl⟩ hc'
  have hpos : 0 < rC.factorMultiplicity (rC.gradedRepresentation ⟨0, hnC⟩) := by
    unfold ObjectRepFiltration.factorMultiplicity
    exact Nat.card_pos_iff.mpr
      ⟨⟨⟨⟨0, hnC⟩, ⟨Representation.Equiv.refl _⟩⟩⟩, inferInstance⟩
  have haa := HasJordanHolderMultiplicity.unique ha ha'
  omega

end MultiplicityFreeSubmoduleLatticeProof

open LengthCriterionProof MultiplicityAdditivityProof MultiplicityFreeSubmoduleLatticeProof

/-- Multiplicities of invariant subspaces of a multiplicity-free
representation are at most one, monotone, modular and strictly increasing on
proper inclusions; these give all six clauses. -/
theorem multiplicityFreeSubmoduleLattice :
    MultiplicityFreeSubmoduleLatticeStatement.{uK, uG, uA} := by
  intro k _ G _ A hA
  obtain ⟨N, s, hs, hfree⟩ := hA
  choose m hm using fun (S : Subrepresentation A.ρ) (τ : Rep.{uA} k G) =>
    exists_mult_sub s hs S τ
  have mem_iff : ∀ (S : Subrepresentation A.ρ) (τ : Rep.{uA} k G),
      τ ∈ (jordanHolderSupport (Rep.of S.toRepresentation) : Set (Rep.{uA} k G)) ↔
        0 < m S τ := by
    intro S τ
    constructor
    · rintro ⟨a, ha, hpos⟩
      rwa [HasJordanHolderMultiplicity.unique ha (hm S τ)] at hpos
    · intro hpos
      exact ⟨m S τ, hm S τ, hpos⟩
  have le_one : ∀ S τ, m S τ ≤ 1 := fun S τ => mult_le_one s hs hfree S (hm S τ)
  have mono : ∀ {S R : Subrepresentation A.ρ}, S ≤ R → ∀ τ, m S τ ≤ m R τ :=
    fun h τ => mult_mono h (hm _ τ) (hm _ τ)
  have modular : ∀ S R τ, m (S ⊓ R) τ + m (S ⊔ R) τ = m S τ + m R τ :=
    fun S R τ => mult_modular S R (hm _ τ) (hm _ τ) (hm _ τ) (hm _ τ)
  dsimp only
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro S
    obtain ⟨n, t, ht⟩ := exists_series_sub s hs S
    exact ⟨n, t, ht⟩
  · intro S R
    constructor
    · intro h τ hτ
      rw [mem_iff] at hτ ⊢
      exact lt_of_lt_of_le hτ (mono h τ)
    · intro hsub
      by_contra hSR
      have hST : ¬ S ≤ S ⊓ R := fun h => hSR (h.trans inf_le_right)
      obtain ⟨τ, hτ⟩ := exists_mult_lt (inf_le_left : S ⊓ R ≤ S) hST
        (exists_series_sub s hs S).choose_spec
      have hlt := hτ _ _ (hm _ τ) (hm _ τ)
      have hS : 0 < m S τ := lt_of_le_of_lt (Nat.zero_le _) hlt
      have hR : 0 < m R τ := (mem_iff R τ).mp (hsub ((mem_iff S τ).mpr hS))
      have := modular S R τ
      have := le_one (S ⊔ R) τ
      have := le_one S τ
      omega
  · intro S R
    ext τ
    rw [Set.mem_union, mem_iff, mem_iff, mem_iff]
    have := modular S R τ
    have := mono (le_sup_left : S ≤ S ⊔ R) τ
    have := mono (le_sup_right : R ≤ S ⊔ R) τ
    omega
  · intro S R
    ext τ
    rw [Set.mem_inter_iff, mem_iff, mem_iff, mem_iff]
    have := modular S R τ
    have := mono (inf_le_left : S ⊓ R ≤ S) τ
    have := mono (inf_le_right : S ⊓ R ≤ R) τ
    have := le_one (S ⊔ R) τ
    omega
  · ext τ
    simp only [Set.mem_empty_iff_false, iff_false]
    rw [mem_iff]
    obtain ⟨n, t, ht, hc⟩ := hm ⊥ τ
    have hlen : (n : ℕ∞) = 0 :=
      (repLength_eq_of_hasSimpleFactors t ht).symm.trans (repLength_bot A.ρ)
    have hn : n = 0 := by exact_mod_cast hlen
    subst hn
    rw [← hc]
    unfold ObjectRepFiltration.factorMultiplicity
    rw [Nat.card_eq_zero.mpr (Or.inl ⟨fun x => x.1.elim0⟩)]
    exact lt_irrefl 0
  · let φ : (⊤ : Subrepresentation A.ρ).toRepresentation.Equiv A.ρ :=
      { toLinearMap := (⊤ : Subrepresentation A.ρ).toSubmodule.subtype
        isIntertwining' := fun _ => rfl
        invFun := fun v => ⟨v, trivial⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    ext τ
    exact exists_congr fun a => and_congr_left' <|
      equivJordanHolderMultiplicityTransport k G
        (Rep.of (⊤ : Subrepresentation A.ρ).toRepresentation) A τ τ φ
        (Representation.Equiv.refl _) a

end Langlands

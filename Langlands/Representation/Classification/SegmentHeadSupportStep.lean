import Langlands.Representation.Classification.SegmentHeadSupportSplit
import Langlands.Representation.Classification.SegmentHeadDecreasingSocle
import Langlands.Representation.Classification.SupercuspidalSupportUniquenessProof
import Langlands.Representation.Classification.CuspidalIntegralTwistFreenessProof
import Langlands.Representation.Classification.IrreducibleProductFiniteLengthProof
import Langlands.Representation.Classification.SegmentTruncationObstructionStatement
import Langlands.Representation.Classification.SegmentHeadDerivativeSupportTruncationStatement
import Langlands.Representation.Derivative.GeneralLinearDerivativeFiniteLengthProof
import Langlands.Representation.Derivative.ProductVanishing
import Langlands.Representation.Category.FiniteIndexRestriction

/-!
# The inductive step for the support of derivatives of segment heads

Let `Δ = [ρ, ν^(m-1) ρ]` with `m = k + 2 ≥ 3` and let `π` be a supplied head of
`ρ × νρ × ⋯ × ν^(m-1) ρ`. Assume the support bound for all heads of segments of
length `m - 1`. Then every irreducible subquotient of every derivative of `π`
has a supercuspidal support whose set is a terminal truncation of `Δ`.

The proof compares two products containing `π`:

* `π` is a subrepresentation of `ν^(m-1) ρ × π'`, where `π'` is the head of
  `[ρ, ν^(m-2) ρ]` (through the decreasing socle of `π'` and of `π`);
* `π` is a quotient of `ρ × π''`, where `π''` is the head of `[νρ, ν^(m-1) ρ]`
  (through the head kernel of the increasing induction).

The Leibniz pieces of the derivatives of both products and the induction
hypothesis give two descriptions of the support; their only common values are
the terminal truncations of `Δ`, by uniqueness of supports and the integral
twist-freeness of supercuspidal classes.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency.types false

open CategoryTheory

namespace Langlands.Classification.SegmentHeadSupport

open GeneralLinear PadicField.TopologicalData Derivative

universe uG uV uF

section Constituents

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- A nonzero finite-length smooth representation has an irreducible
subrepresentation (an atom of its Artinian lattice of subrepresentations). -/
theorem exists_irreducible_subrepresentation {A : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.HasFiniteLength) [Nontrivial A] :
    ∃ C : SmoothRep.{0, uG, uV} ℂ G, C.IsIrreducible ∧
      ∃ j : C ⟶ A, Function.Injective (SmoothRep.hom j) := by
  have : IsArtinian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).2
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.representation)
  have : IsAtomic (Subrepresentation A.representation) := e.isAtomic_iff.mpr inferInstance
  have hbt : (⊥ : Subrepresentation A.representation) ≠ ⊤ := by
    obtain ⟨v, hv⟩ := exists_ne (0 : A)
    intro hb
    apply hv
    have hmem : v ∈ (⊤ : Subrepresentation A.representation).toSubmodule := Submodule.mem_top
    rw [← hb] at hmem
    exact (Submodule.mem_bot ℂ).mp hmem
  obtain ⟨U, hU, -⟩ :=
    (eq_bot_or_exists_atom_le (⊤ : Subrepresentation A.representation)).resolve_left hbt.symm
  exact ⟨SmoothRep.subrepresentation A U,
    FiniteIndexRestriction.isIrreducible_toRepresentation_of_isAtom U hU,
    SmoothRep.subtype A U, SmoothRep.subtype_injective A U⟩

/-- A nonzero finite-length smooth representation has an irreducible quotient
(the quotient by a coatom of its Noetherian lattice of submodules; the argument
of `SmoothRep.exists_irreducible_quotient_subquotient_of_nonzero`). -/
theorem exists_irreducible_quotient {A : SmoothRep.{0, uG, uV} ℂ G}
    (hA : A.HasFiniteLength) [Nontrivial A] :
    ∃ C : SmoothRep.{0, uG, uV} ℂ G, C.IsIrreducible ∧
      ∃ q : A ⟶ C, Function.Surjective (SmoothRep.hom q) := by
  have : IsNoetherian (MonoidAlgebra ℂ G) A.representation.asModule :=
    (isFiniteLength_iff_isNoetherian_isArtinian.mp hA).1
  let : Nontrivial A.representation.asModule := ‹Nontrivial A›
  obtain ⟨N, hN⟩ :=
    IsCoatomic.exists_coatom (α := Submodule (MonoidAlgebra ℂ G) A.representation.asModule)
  let S : Subrepresentation A.representation := Subrepresentation.ofSubmodule' N
  let C := SmoothRep.quotient A S
  let r : A ⟶ C := SmoothRep.mkQ A S
  let rg := Representation.IntertwiningMap.equivLinearMapAsModule _ _ (SmoothRep.hom r)
  have hrg : Function.Surjective rg := SmoothRep.mkQ_surjective A S
  have hker : rg.ker = N := by
    ext v
    change Submodule.Quotient.mk v = (0 : A ⧸ S.toSubmodule) ↔ v ∈ N
    exact Submodule.Quotient.mk_eq_zero _
  have hsimp : IsSimpleModule (MonoidAlgebra ℂ G) (A.representation.asModule ⧸ rg.ker) := by
    apply isSimpleModule_iff_isCoatom.mpr
    rwa [hker]
  have hCsimp : IsSimpleModule (MonoidAlgebra ℂ G) C.representation.asModule :=
    IsSimpleModule.congr (rg.quotKerEquivOfSurjective hrg).symm
  exact ⟨C, (Representation.irreducible_iff_isSimpleModule_asModule _).mpr hCsimp, r, hrg⟩

end Constituents

section Head

variable {G : Type uG} [Group G] {V W W' : Type uV} [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']

/-- Every irreducible quotient of a representation with an irreducible head is
equivalent to that head. -/
theorem IsIrreducibleHead.nonempty_equiv_of_quotient {ρ : Representation ℂ G V}
    {π : Representation ℂ G W} {ω : Representation ℂ G W'} (h : IsIrreducibleHead ρ π)
    (hω : ω.IsIrreducible) (q : ρ.IntertwiningMap ω) (hq : Function.Surjective q) :
    Nonempty (ω.Equiv π) := by
  obtain ⟨e⟩ := h.nonempty_headEquiv
  exact ⟨(headEquivOfSurjective q hq (h.headKernel_eq ω hω q hq)).symm.trans e⟩

end Head

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

section Members

variable {T : F.TopologicalData}

/-- `ν^j (ν^i ρ) = ν^(i+j) ρ` for natural exponents. -/
theorem twist_natCast_twist (ρ : CuspidalDatum.{uV, uF} T) (i j : ℕ) :
    (ρ.twist ((i : ℕ) : ℝ)).twist ((j : ℕ) : ℝ) = ρ.twist ((i + j : ℕ) : ℝ) := by
  rw [CuspidalDatum.twist_twist]
  congr 1
  push_cast
  ring

/-- Integral twist-freeness, natural form: `ν^i ρ = ν^j ρ` forces `i = j`. -/
theorem twist_natCast_inj (ρ : CuspidalDatum.{uV, uF} T) {i j : ℕ}
    (h : ρ.twist ((i : ℕ) : ℝ) = ρ.twist ((j : ℕ) : ℝ)) : i = j := by
  have hz : ρ.twist (((i : ℤ) - (j : ℤ) : ℤ) : ℝ) = ρ := by
    calc
      _ = (ρ.twist ((i : ℕ) : ℝ)).twist (-((j : ℕ) : ℝ)) := by
        rw [CuspidalDatum.twist_twist]
        congr 1
        push_cast
        ring
      _ = (ρ.twist ((j : ℕ) : ℝ)).twist (-((j : ℕ) : ℝ)) :=
        congrArg (fun x => x.twist (-((j : ℕ) : ℝ))) h
      _ = ρ := by rw [CuspidalDatum.twist_twist, neg_add_cancel, CuspidalDatum.twist_zero]
  have := (cuspidalIntegralTwistFreeness F T ρ ((i : ℤ) - (j : ℤ))).mp hz
  omega

/-- The members of a segment are pairwise distinct. -/
theorem member_inj (Δ : Segment.{uV, uF} T) {i j : ℕ} (h : Δ.member i = Δ.member j) :
    i = j :=
  twist_natCast_inj Δ.base h

/-- The cuspidal data `ν^j ρ` with `a ≤ j < b`. -/
def window (ρ : CuspidalDatum.{uV, uF} T) (a b : ℕ) : Set (CuspidalDatum.{uV, uF} T) :=
  {x | ∃ j, a ≤ j ∧ j < b ∧ ρ.twist ((j : ℕ) : ℝ) = x}

/-- Shifting the base of a window by `ν^c`. -/
theorem window_twist (ρ : CuspidalDatum.{uV, uF} T) (c a b : ℕ) :
    window (ρ.twist ((c : ℕ) : ℝ)) a b = window ρ (a + c) (b + c) := by
  ext x
  constructor
  · rintro ⟨j, h1, h2, rfl⟩
    exact ⟨j + c, by omega, by omega, by rw [twist_natCast_twist, Nat.add_comm]⟩
  · rintro ⟨j, h1, h2, rfl⟩
    refine ⟨j - c, by omega, by omega, ?_⟩
    rw [twist_natCast_twist, show c + (j - c) = j by omega]

/-- The terminal subsegment `[ν^a ρ, ν^(m-1) ρ]` of `Δ = [ρ, ν^(m-1) ρ]`, for
`a < m`. -/
def tailSegment (Δ : Segment.{uV, uF} T) (a : ℕ) (ha : a < Δ.length) :
    Segment.{uV, uF} T where
  base := Δ.member a
  length := Δ.length - a
  length_pos := Nat.sub_pos_of_lt ha

theorem tailSegment_support (Δ : Segment.{uV, uF} T) (a : ℕ) (ha : a < Δ.length) :
    (tailSegment Δ a ha).support = window Δ.base a Δ.length := by
  ext x
  constructor
  · rintro ⟨i, hi, rfl⟩
    change i < Δ.length - a at hi
    exact ⟨a + i, by omega, by omega, (twist_natCast_twist Δ.base a i).symm⟩
  · rintro ⟨j, haj, hj, rfl⟩
    refine ⟨j - a, by change j - a < Δ.length - a; omega, ?_⟩
    change (Δ.base.twist ((a : ℕ) : ℝ)).twist ((j - a : ℕ) : ℝ) = _
    rw [twist_natCast_twist, show a + (j - a) = j by omega]

/-- The supports of the optional terminal truncations of `Δ` are exactly the
windows `{ν^j ρ | a ≤ j < m}`, `a ≤ m`. -/
theorem exists_terminal_iff (Δ : Segment.{uV, uF} T) (S : Set (CuspidalDatum.{uV, uF} T)) :
    (∃ A : Option (Segment.{uV, uF} T),
      Segment.IsTerminalTruncation A Δ ∧ S = Segment.optionalSupport A) ↔
      ∃ a ≤ Δ.length, S = window Δ.base a Δ.length := by
  constructor
  · rintro ⟨A, hA, rfl⟩
    cases A with
    | none =>
      refine ⟨Δ.length, le_rfl, ?_⟩
      ext x
      simp only [Segment.optionalSupport, Set.mem_empty_iff_false, false_iff]
      rintro ⟨j, h1, h2, -⟩
      omega
    | some E =>
      obtain ⟨hsub, hlast⟩ := hA
      obtain ⟨a, -, hab⟩ := hsub E.base_mem_support
      have hmem : ∀ i : ℕ, E.member i = Δ.member (a + i) := fun i => by
        change E.base.twist ((i : ℕ) : ℝ) = Δ.base.twist ((a + i : ℕ) : ℝ)
        rw [← hab]
        exact twist_natCast_twist Δ.base a i
      have hlt : ∀ i < E.length, a + i < Δ.length := by
        intro i hi
        obtain ⟨j, hj, hje⟩ := hsub (E.member_mem_support hi)
        rw [hmem] at hje
        have := member_inj Δ hje
        omega
      obtain ⟨i0, hi0, hi0e⟩ := hlast
      rw [hmem] at hi0e
      have h0 := member_inj Δ (j := Δ.length - 1) hi0e
      have hEl := hlt (E.length - 1) (by have := E.length_pos; omega)
      have hE := E.length_pos
      refine ⟨a, by omega, ?_⟩
      ext x
      constructor
      · rintro ⟨i, hi, rfl⟩
        exact ⟨a + i, by omega, hlt i hi, (hmem i).symm⟩
      · rintro ⟨j, haj, hj, rfl⟩
        refine ⟨j - a, by omega, ?_⟩
        rw [hmem, show a + (j - a) = j by omega]
        rfl
  · rintro ⟨a, ha, rfl⟩
    rcases Nat.lt_or_ge a Δ.length with ha' | ha'
    · refine ⟨some (tailSegment Δ a ha'), ?_, (tailSegment_support Δ a ha').symm⟩
      change (tailSegment Δ a ha').support ⊆ Δ.support ∧ Δ.last ∈ (tailSegment Δ a ha').support
      rw [tailSegment_support]
      refine ⟨?_, ⟨Δ.length - 1, by omega, by omega, rfl⟩⟩
      rintro x ⟨j, -, hj, rfl⟩
      exact ⟨j, hj, rfl⟩
    · refine ⟨none, trivial, ?_⟩
      ext x
      simp only [Segment.optionalSupport, Set.mem_empty_iff_false, iff_false]
      rintro ⟨j, h1, h2, -⟩
      omega

/-- Combination of the two sides. The subrepresentation side describes the
support by the window of `[ρ, ν^k ρ]`, possibly with `ν^(k+1) ρ` added; the
quotient side by the window of `[νρ, ν^(k+1) ρ]`, possibly with `ρ` added. For
`k ≥ 1` and equal nonzero supports, the support is a terminal window of
`[ρ, ν^(k+1) ρ]`. -/
theorem window_of_sides (ρ : CuspidalDatum.{uV, uF} T) {k : ℕ} (hk : 1 ≤ k)
    {s s₀ : Multiset (CuspidalDatum.{uV, uF} T)}
    (hsub : (∃ s', (∃ a ≤ k + 1, {x | x ∈ s'} = window ρ a (k + 1)) ∧
        s = ρ.twist ((k + 1 : ℕ) : ℝ) ::ₘ s') ∨
      ∃ a ≤ k + 1, {x | x ∈ s} = window ρ a (k + 1))
    (hquot : (∃ s', (∃ a ≤ k + 1, {x | x ∈ s'} = window ρ (a + 1) (k + 1 + 1)) ∧
        s₀ = ρ.twist ((0 : ℕ) : ℝ) ::ₘ s') ∨
      ∃ a ≤ k + 1, {x | x ∈ s₀} = window ρ (a + 1) (k + 1 + 1))
    (huniq : s ≠ 0 → s = s₀) :
    ∃ a ≤ k + 2, {x | x ∈ s} = window ρ a (k + 2) := by
  rcases hsub with ⟨s', ⟨a, ha, hs'⟩, rfl⟩ | ⟨a, ha, hs⟩
  · refine ⟨a, by omega, ?_⟩
    ext x
    simp only [Set.mem_ofPred_eq, Multiset.mem_cons]
    constructor
    · rintro (rfl | hx)
      · exact ⟨k + 1, by omega, by omega, rfl⟩
      · obtain ⟨j, haj, hj, rfl⟩ := (Set.ext_iff.mp hs' x).mp hx
        exact ⟨j, haj, by omega, rfl⟩
    · rintro ⟨j, haj, hj, rfl⟩
      by_cases hjk : j = k + 1
      · subst hjk
        exact Or.inl rfl
      · exact Or.inr ((Set.ext_iff.mp hs' _).mpr ⟨j, haj, by omega, rfl⟩)
  · rcases Nat.lt_or_ge k a with hka | hka
    · refine ⟨k + 2, le_rfl, ?_⟩
      rw [hs]
      ext x
      constructor <;> rintro ⟨j, h1, h2, -⟩ <;> omega
    · exfalso
      have hkmem : ρ.twist ((k : ℕ) : ℝ) ∈ s :=
        (Set.ext_iff.mp hs _).mpr ⟨k, hka, by omega, rfl⟩
      have hs0 : s ≠ 0 := by
        rintro rfl
        exact Multiset.notMem_zero _ hkmem
      rw [← huniq hs0] at hquot
      have hnot : ρ.twist ((k + 1 : ℕ) : ℝ) ∉ s := by
        intro hx
        obtain ⟨j, -, hj, hjx⟩ := (Set.ext_iff.mp hs _).mp hx
        have := twist_natCast_inj ρ hjx
        omega
      rcases hquot with ⟨s', ⟨a', ha', hs'⟩, hcons⟩ | ⟨a', ha', hs'⟩
      · rcases Nat.lt_or_ge k a' with hka' | hka'
        · have hs'0 : s' = 0 := by
            apply Multiset.eq_zero_of_forall_notMem
            intro x hx
            obtain ⟨j, h1, h2, -⟩ := (Set.ext_iff.mp hs' x).mp hx
            omega
          rw [hcons, hs'0, Multiset.cons_zero, Multiset.mem_singleton] at hkmem
          have := twist_natCast_inj ρ hkmem
          omega
        · apply hnot
          rw [hcons]
          exact Multiset.mem_cons_of_mem
            ((Set.ext_iff.mp hs' _).mpr ⟨k + 1, by omega, by omega, rfl⟩)
      · rcases Nat.lt_or_ge k a' with hka' | hka'
        · obtain ⟨j, h1, h2, -⟩ := (Set.ext_iff.mp hs' _).mp hkmem
          omega
        · exact hnot ((Set.ext_iff.mp hs' _).mpr ⟨k + 1, by omega, by omega, rfl⟩)

/-- A nonzero supercuspidal support only occurs in positive rank. -/
theorem pos_of_isSupercuspidalSupport {n : ℕ}
    {σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)} (hs : T.IsSupercuspidalSupport σ s)
    (h0 : s ≠ 0) : 0 < n := by
  obtain ⟨k, ρ, rfl, hsum, -⟩ := hs
  cases k with
  | zero => exact absurd (by simp) h0
  | succ k =>
    rw [← hsum, Fin.sum_univ_succ]
    exact Nat.add_pos_left (ρ 0).rank_pos _

end Members

variable (T : F.TopologicalData)

section RankCast

theorem rankCast_map_injective {a b : ℕ} (h : a = b)
    {X Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (hf : letI := T.topology; Function.Injective (SmoothRep.hom f)) :
    letI := T.topology
    Function.Injective (SmoothRep.hom ((generalLinearRankCast T h).map f)) := by
  subst h
  exact hf

theorem rankCast_map_surjective {a b : ℕ} (h : a = b)
    {X Y : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier)}
    (f : letI := T.topology; X ⟶ Y)
    (hf : letI := T.topology; Function.Surjective (SmoothRep.hom f)) :
    letI := T.topology
    Function.Surjective (SmoothRep.hom ((generalLinearRankCast T h).map f)) := by
  subst h
  exact hf

theorem nontrivial_rankCast {a b : ℕ} (h : a = b)
    (X : letI := T.topology; SmoothRep.{0, uF, uV} ℂ (GeneralLinear a F.Carrier))
    [Nontrivial X] : Nontrivial ((generalLinearRankCast T h).obj X) := by
  subst h
  exact ‹Nontrivial X›

end RankCast

/-- A supplied segment head is irreducible. -/
theorem isIrreducible_of_isSegmentHead {Δ : Segment.{uV, uF} T}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)}
    (h : T.IsSegmentHead Δ π) : letI := T.topology; π.IsIrreducible := by
  obtain ⟨_, _, hh⟩ := h
  exact hh.1

/-- The target's support conclusion for every derivative of every supplied head
of the segment `Δ`. -/
def HeadSupportBound (Δ : Segment.{uV, uF} T) : Prop :=
  letI := T.topology
  ∀ (ψ : HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier)
    (π : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier)),
    T.IsSegmentHead Δ π →
    ∀ (k : ℕ) (hk : k ≤ Δ.degree)
      (σ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - k) F.Carrier)),
      σ.IsIrreducible →
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree k hk).obj π) →
      ∃ (s : Multiset (CuspidalDatum.{uV, uF} T)) (A : Option (Segment.{uV, uF} T)),
        T.IsSupercuspidalSupport σ s ∧ Segment.IsTerminalTruncation A Δ ∧
          {ρ | ρ ∈ s} = Segment.optionalSupport A

section Transfer

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- BZ77 3.2: the derivatives are exact. -/
theorem preservesShortExact_derivative (N d : ℕ) (hd : d ≤ N) :
    letI := T.topology
    PreservesShortExact (generalLinearDerivative.{uF, uV} T ψ N d hd) := by
  let := T.topology
  intro S P Q i q hi hq hex
  exact generalLinearDerivativeExactness F T ψ N d hd S P Q i q hi hq hex

/-- Let `A₀` represent `ρ₀`, let `π'` be irreducible, and let `X` be an actual
subquotient of `A₀ × π'`. Assume that every irreducible subquotient of every
derivative of `π'` has a support satisfying `Q`. Then every irreducible
subquotient of every derivative of `X` has a support `ρ₀ + s'` or `s'` with
`Q s'` (BZ77 4.14(c) with BZ77 §4.4). -/
theorem support_of_isSubquotient_product (ρ0 : CuspidalDatum.{uV, uF} T)
    (A0 : letI := T.topology; SupercuspidalRep.{uF, uV} (F := F.Carrier) (n := ρ0.rank))
    (hA0 : ρ0.IsRepresentedBy A0) {b N : ℕ} (h : ρ0.rank + b = N)
    (π' : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear b F.Carrier))
    (hπ' : letI := T.topology; π'.IsIrreducible)
    (Q : Multiset (CuspidalDatum.{uV, uF} T) → Prop)
    (IH : letI := T.topology
      ∀ (d : ℕ) (hd : d ≤ b)
        (τ : SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (b - d) F.Carrier)),
        τ.IsIrreducible →
        SmoothRep.IsSubquotient τ ((generalLinearDerivative T ψ b d hd).obj π') →
        ∃ s', T.IsSupercuspidalSupport τ s' ∧ Q s')
    (X : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear N F.Carrier))
    (hX : letI := T.topology
      SmoothRep.IsSubquotient X ((generalLinearRankCast T h).obj
        ((T.binaryNormalizedProductFunctor ρ0.rank b).obj
          (SmoothRep.universeLift.{uF} A0.obj, π'))))
    (d : ℕ) (hd : d ≤ N)
    (σ : letI := T.topology; SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (N - d) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsq : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ N d hd).obj X)) :
    ∃ s, T.IsSupercuspidalSupport σ s ∧ ((∃ s', Q s' ∧ s = ρ0 ::ₘ s') ∨ Q s) := by
  let := T.topology
  have h1 : SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ N d hd).obj
      ((generalLinearRankCast T h).obj ((T.binaryNormalizedProductFunctor ρ0.rank b).obj
        (SmoothRep.universeLift.{uF} A0.obj, π')))) :=
    isSubquotient_trans hsq ((preservesShortExact_derivative T ψ N d hd).isSubquotient_map hX)
  subst h
  let L := SmoothRep.universeLift.{uF} A0.obj
  have hLirr : L.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff A0.obj).mpr A0.property.1
  have hLsc : IsSupercuspidal L.representation :=
    isSupercuspidal_of_equiv (SmoothRep.universeLiftEquiv.{uF} A0.obj) A0.property.2
  have hL := derivativePattern_of_supercuspidal T ψ ρ0.rank_pos L hLirr hLsc
  rcases leibniz_cases T ψ ρ0.rank_pos hd L hL π' σ hσ h1 with
    ⟨hdb, h', h2⟩ | ⟨-, hdb, h', h2⟩
  · have h3 := (isSubquotient_rankCast_iff T h' σ _).mp h2
    have hσ' := isIrreducible_rankCast T h'.symm σ hσ
    obtain ⟨τ, hτ, hτsq, hστ⟩ := exists_irreducible_of_isSubquotient_map
      (preservesShortExact_binaryNormalized_sectR T ρ0.rank_pos L)
      (generalLinearDerivativeFiniteLength F T ψ b d hdb π'
        (hasFiniteLength_of_isIrreducible hπ')) hσ' h3
    obtain ⟨s', hs', hQ⟩ := IH d hdb τ hτ hτsq
    have h4 := isSupercuspidalSupport_cons T ρ0 A0 hA0 τ s' hs' _ hσ' hστ
    exact ⟨ρ0 ::ₘ s', (isSupercuspidalSupport_rankCast_iff T h'.symm σ _).mp h4,
      Or.inl ⟨s', hQ, rfl⟩⟩
  · have h3 := (isSubquotient_rankCast_iff T h' σ _).mp h2
    obtain ⟨s', hs', hQ⟩ := IH _ hdb _ (isIrreducible_rankCast T h'.symm σ hσ) h3
    exact ⟨s', (isSupercuspidalSupport_rankCast_iff T h'.symm σ _).mp hs', Or.inr hQ⟩

end Transfer

section Sides

variable (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology)

/-- The segment `[ρ, ν^k ρ]`: `Δ` without its last member when `Δ.length = k + 2`. -/
def initSegment (Δ : Segment.{uV, uF} T) (k : ℕ) : Segment.{uV, uF} T where
  base := Δ.base
  length := k + 1
  length_pos := Nat.succ_pos k

/-- The segment `[νρ, ν^(k+1) ρ]`: `Δ` without its first member when
`Δ.length = k + 2`. -/
def succSegment (Δ : Segment.{uV, uF} T) (k : ℕ) : Segment.{uV, uF} T where
  base := Δ.base.twist ((1 : ℕ) : ℝ)
  length := k + 1
  length_pos := Nat.succ_pos k

/-- The subrepresentation side. A supplied head `π` of `Δ = [ρ, ν^(k+1) ρ]` embeds
in `ν^(k+1) ρ × π'` for the head `π'` of `[ρ, ν^k ρ]`: an irreducible
subrepresentation of `ν^(k+1) ρ × π'` lies in the decreasing induction of `Δ`, whose
socle is `π`. Hence the support of every irreducible subquotient of a derivative of
`π` is a terminal window of `[ρ, ν^k ρ]`, possibly with `ν^(k+1) ρ` added. -/
theorem sub_side (Δ : Segment.{uV, uF} T) {k : ℕ} (hm : Δ.length = k + 2)
    (IH : HeadSupportBound T (initSegment T Δ k))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (d : ℕ) (hd : d ≤ Δ.degree)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - d) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsq : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree d hd).obj π)) :
    ∃ s, T.IsSupercuspidalSupport σ s ∧
      ((∃ s', (∃ a ≤ k + 1, {x | x ∈ s'} = window Δ.base a (k + 1)) ∧
          s = Δ.base.twist ((k + 1 : ℕ) : ℝ) ::ₘ s') ∨
        ∃ a ≤ k + 1, {x | x ∈ s} = window Δ.base a (k + 1)) := by
  let := T.topology
  obtain ⟨A, hA, -⟩ := id hπ
  let Δ' := initSegment T Δ k
  obtain ⟨π', hπ', -⟩ := segmentSpecialConstituentExistence F T Δ'
  have hπ'irr := isIrreducible_of_isSegmentHead T hπ'
  let j' := hπ'.decreasingSocleEmbedding A hA
  let A0 := twistRep T ((k + 1 : ℕ) : ℝ) A
  let L := SmoothRep.universeLift.{uF} A0.obj
  have hLirr : L.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff A0.obj).mpr A0.property.1
  let Φ := Prod.sectR L _ ⋙ T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)
  let ι₁ := Φ.map (SmoothRep.ofHom j'.1)
  have hι₁ : Function.Injective (SmoothRep.hom ι₁) :=
    (preservesShortExact_binaryNormalized_sectR T Δ.rank_pos L).map_injective _ j'.2
  obtain ⟨e⟩ := nonempty_iso_segmentInducedDown_split T Δ.rank_pos hm A.obj
  have h : Δ.rank + (k + 1) * Δ.rank = Δ.degree := uniform_split_rank hm
  let M := (generalLinearRankCast T h).obj
    ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj (L, π'))
  let ι : M ⟶ T.segmentInducedDown A.obj Δ.length Δ.rank_pos :=
    (generalLinearRankCast T h).map ι₁ ≫ e.inv
  have hι : Function.Injective (SmoothRep.hom ι) :=
    (SmoothRep.hom_hom_injective e.symm).comp (rankCast_map_injective T h ι₁ hι₁)
  have hfl : (T.segmentInducedDown A.obj Δ.length Δ.rank_pos).HasFiniteLength :=
    irreducibleProductFiniteLength F T _ Δ.degree_pos
      (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos) (T.segmentFactorsDown A.obj Δ.length Δ.rank_pos)
      (fun i => (twistRep T ((Δ.length - 1 - (i : ℕ) : ℕ) : ℝ) A).property.1)
  have hM : M.HasFiniteLength :=
    hfl.of_injective (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom ι)) hι
  have : Nontrivial L := nontrivial_of_isIrreducible hLirr
  have : Nontrivial π' := nontrivial_of_isIrreducible hπ'irr
  have : Nontrivial ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj (L, π')) :=
    ProductVanishing.nontrivial_binary T (L, π')
  have : Nontrivial M := nontrivial_rankCast T h _
  obtain ⟨τ, hτ, jτ, hjτ⟩ := exists_irreducible_subrepresentation hM
  obtain ⟨eτ⟩ := hπ.nonempty_equiv_of_down_subrepresentation A hA hτ (SmoothRep.hom (jτ ≫ ι))
    (hι.comp hjτ)
  have hX : SmoothRep.IsSubquotient π M :=
    SmoothRep.IsSubquotient.of_iso_left (SmoothRep.mkIso eτ)
      (SmoothRep.IsSubrepresentation.isSubquotient ⟨jτ, hjτ⟩)
  exact support_of_isSubquotient_product T ψ (Δ.base.twist ((k + 1 : ℕ) : ℝ)) A0
    (isRepresentedBy_twistRep T _ hA) h π' hπ'irr
    (fun s' => ∃ a ≤ k + 1, {x | x ∈ s'} = window Δ.base a (k + 1))
    (fun d' hd' τ' hτ' hsq' => by
      obtain ⟨s', E, hs', hE, hset⟩ := IH ψ π' hπ' d' hd' τ' hτ' hsq'
      exact ⟨s', hs', (exists_terminal_iff Δ' _).mp ⟨E, hE, hset⟩⟩)
    π hX d hd σ hσ hsq

/-- The quotient side. A supplied head `π` of `Δ = [ρ, ν^(k+1) ρ]` is a quotient of
`ρ × π''` for the head `π''` of `[νρ, ν^(k+1) ρ]`: an irreducible quotient of
`ρ × π''` is a quotient of the increasing induction of `Δ`, whose head is `π`.
Hence the support of every irreducible subquotient of a derivative of `π` is a
terminal window of `[νρ, ν^(k+1) ρ]`, possibly with `ρ` added. -/
theorem quot_side (Δ : Segment.{uV, uF} T) {k : ℕ} (hm : Δ.length = k + 2)
    (IH : HeadSupportBound T (succSegment T Δ k))
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear Δ.degree F.Carrier))
    (hπ : T.IsSegmentHead Δ π) (d : ℕ) (hd : d ≤ Δ.degree)
    (σ : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (Δ.degree - d) F.Carrier))
    (hσ : letI := T.topology; σ.IsIrreducible)
    (hsq : letI := T.topology
      SmoothRep.IsSubquotient σ ((generalLinearDerivative T ψ Δ.degree d hd).obj π)) :
    ∃ s, T.IsSupercuspidalSupport σ s ∧
      ((∃ s', (∃ a ≤ k + 1, {x | x ∈ s'} = window Δ.base (a + 1) (k + 1 + 1)) ∧
          s = Δ.base.twist ((0 : ℕ) : ℝ) ::ₘ s') ∨
        ∃ a ≤ k + 1, {x | x ∈ s} = window Δ.base (a + 1) (k + 1 + 1)) := by
  let := T.topology
  obtain ⟨A, hA, -⟩ := id hπ
  have hhead := (T.isSegmentHead_iff Δ π A hA).mp hπ
  let Δ'' := succSegment T Δ k
  let B := twistRep T ((1 : ℕ) : ℝ) A
  have hB : Δ''.base.IsRepresentedBy B := isRepresentedBy_twistRep T _ hA
  obtain ⟨π'', hπ'', -⟩ := segmentSpecialConstituentExistence F T Δ''
  have hπ''irr := isIrreducible_of_isSegmentHead T hπ''
  obtain ⟨-, q'', hq'', -⟩ := (T.isSegmentHead_iff Δ'' π'' B hB).mp hπ''
  let A0 := twistRep T ((0 : ℕ) : ℝ) A
  let L := SmoothRep.universeLift.{uF} A0.obj
  have hLirr : L.IsIrreducible :=
    (SmoothRep.isIrreducible_universeLift_iff A0.obj).mpr A0.property.1
  let Φ := Prod.sectR L _ ⋙ T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)
  let κ₁ := Φ.map (SmoothRep.ofHom q'')
  have hκ₁ : Function.Surjective (SmoothRep.hom κ₁) :=
    (preservesShortExact_binaryNormalized_sectR T Δ.rank_pos L).map_surjective _ hq''
  obtain ⟨e⟩ := nonempty_iso_segmentInduced_split T Δ.rank_pos hm A.obj
  have h : Δ.rank + (k + 1) * Δ.rank = Δ.degree := uniform_split_rank hm
  let M := (generalLinearRankCast T h).obj
    ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj (L, π''))
  let κ : T.segmentInduced A.obj Δ.length Δ.rank_pos ⟶ M :=
    e.hom ≫ (generalLinearRankCast T h).map κ₁
  have hκ : Function.Surjective (SmoothRep.hom κ) :=
    (rankCast_map_surjective T h κ₁ hκ₁).comp (SmoothRep.hom_hom_surjective e)
  have hfl : (T.segmentInduced A.obj Δ.length Δ.rank_pos).HasFiniteLength :=
    irreducibleProductFiniteLength F T _ Δ.degree_pos
      (BlockShape.uniform Δ.length Δ.rank Δ.rank_pos) (T.segmentFactors A.obj Δ.length Δ.rank_pos)
      (fun i => (twistRep T (((i : ℕ) : ℕ) : ℝ) A).property.1)
  have hM : M.HasFiniteLength :=
    hfl.of_surjective (f := Representation.IntertwiningMap.equivLinearMapAsModule _ _
      (SmoothRep.hom κ)) hκ
  have : Nontrivial L := nontrivial_of_isIrreducible hLirr
  have : Nontrivial π'' := nontrivial_of_isIrreducible hπ''irr
  have : Nontrivial ((T.binaryNormalizedProductFunctor Δ.rank ((k + 1) * Δ.rank)).obj
      (L, π'')) :=
    ProductVanishing.nontrivial_binary T (L, π'')
  have : Nontrivial M := nontrivial_rankCast T h _
  obtain ⟨ω, hω, qω, hqω⟩ := exists_irreducible_quotient hM
  obtain ⟨eω⟩ := IsIrreducibleHead.nonempty_equiv_of_quotient hhead hω
    (SmoothRep.hom (κ ≫ qω)) (hqω.comp hκ)
  have hX : SmoothRep.IsSubquotient π M :=
    SmoothRep.IsSubquotient.of_iso_left (SmoothRep.mkIso eω)
      (SmoothRep.IsQuotient.isSubquotient ⟨qω, hqω⟩)
  exact support_of_isSubquotient_product T ψ (Δ.base.twist ((0 : ℕ) : ℝ)) A0
    (isRepresentedBy_twistRep T _ hA) h π'' hπ''irr
    (fun s' => ∃ a ≤ k + 1, {x | x ∈ s'} = window Δ.base (a + 1) (k + 1 + 1))
    (fun d' hd' τ' hτ' hsq' => by
      obtain ⟨s', E, hs', hE, hset⟩ := IH ψ π'' hπ'' d' hd' τ' hτ' hsq'
      obtain ⟨a, ha, hwin⟩ := (exists_terminal_iff Δ'' _).mp ⟨E, hE, hset⟩
      refine ⟨s', hs', a, ha, ?_⟩
      rw [hwin]
      exact window_twist Δ.base 1 a (k + 1))
    π hX d hd σ hσ hsq

end Sides

section Induction

/-- The inductive step: for `k ≥ 1`, the support bound for all segments of
length `k + 1` gives it for every segment of length `k + 2`. -/
theorem headSupportBound_step {k : ℕ} (hk : 1 ≤ k) (Δ : Segment.{uV, uF} T)
    (hm : Δ.length = k + 2)
    (IH : ∀ Δ' : Segment.{uV, uF} T, Δ'.length = k + 1 → HeadSupportBound T Δ') :
    HeadSupportBound T Δ := by
  let := T.topology
  intro ψ π hπ d hd σ hσ hsq
  obtain ⟨s, hs, hsub⟩ := sub_side T ψ Δ hm (IH _ rfl) π hπ d hd σ hσ hsq
  obtain ⟨s₀, hs₀, hquot⟩ := quot_side T ψ Δ hm (IH _ rfl) π hπ d hd σ hσ hsq
  have huniq : s ≠ 0 → s = s₀ := fun h0 =>
    glSupercuspidalSupportUniqueness.{uV, uF} p F T _ (pos_of_isSupercuspidalSupport hs h0)
      σ hσ s s₀ hs hs₀
  obtain ⟨a, ha, hset⟩ := window_of_sides Δ.base hk hsub hquot huniq
  obtain ⟨E, hE, hE'⟩ := (exists_terminal_iff Δ {x | x ∈ s}).mpr
    ⟨a, by omega, by rw [hm]; exact hset⟩
  exact ⟨s, E, hs, hE, hE'⟩

/-- The support bound for every segment, from the cases of length one and two. -/
theorem headSupportBound_of_base
    (h1 : ∀ Δ : Segment.{uV, uF} T, Δ.length = 1 → HeadSupportBound T Δ)
    (h2 : ∀ Δ : Segment.{uV, uF} T, Δ.length = 2 → HeadSupportBound T Δ)
    (Δ : Segment.{uV, uF} T) : HeadSupportBound T Δ := by
  suffices H : ∀ n, ∀ Δ : Segment.{uV, uF} T, Δ.length = n + 1 → HeadSupportBound T Δ from
    H (Δ.length - 1) Δ (by have := Δ.length_pos; omega)
  intro n
  induction n with
  | zero => exact h1
  | succ n ih =>
    rcases n with _ | n
    · exact h2
    · intro Δ hΔ
      exact headSupportBound_step T (k := n + 1) (by omega) Δ (by omega) ih

/-- The target proposition from the cases of length one and two. -/
theorem supportTruncation_of_base
    (h1 : ∀ Δ : Segment.{uV, uF} T, Δ.length = 1 → HeadSupportBound T Δ)
    (h2 : ∀ Δ : Segment.{uV, uF} T, Δ.length = 2 → HeadSupportBound T Δ) :
    SegmentHeadDerivativeSupportTruncation.{uF, uV} F T := by
  intro ψ Δ π hπ k hk σ hσ hsub
  exact headSupportBound_of_base T h1 h2 Δ ψ π hπ k hk σ hσ hsub

end Induction

end Langlands.Classification.SegmentHeadSupport

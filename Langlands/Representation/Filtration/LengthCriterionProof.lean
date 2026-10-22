import Langlands.Representation.Filtration.LengthCriterionStatement
import Mathlib.RingTheory.Length

/-! Proof of the bounded-chain criterion for actual representation composition length. -/

namespace Langlands

universe uK uG uV

namespace LengthCriterionProof

section Quotient

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
  {V : Type uV} [AddCommGroup V] [Module k V] {ρ : Representation k G V}

/-- The lower invariant subspace, pulled back to the carrier of the upper one. -/
abbrev lower (S T : Subrepresentation ρ) : Submodule k T.toSubmodule :=
  S.toSubmodule.comap T.toSubmodule.subtype

theorem lower_le_comap (S T : Subrepresentation ρ) (g : G) :
    lower S T ≤ (lower S T).comap (T.toRepresentation g) :=
  fun _ hv => S.apply_mem_toSubmodule g hv

/-- The actual successive quotient representation of `T` by `S`. -/
abbrev quotientRep (S T : Subrepresentation ρ) :
    Representation k G (T.toSubmodule ⧸ lower S T) :=
  T.toRepresentation.quotient (lower S T) (lower_le_comap S T)

theorem quotientRep_mk (S T : Subrepresentation ρ) (g : G) (x : T.toSubmodule) :
    quotientRep S T g ((lower S T).mkQ x) = (lower S T).mkQ (T.toRepresentation g x) :=
  rfl

/-- The image in the successive quotient of an invariant subspace of `ρ`. -/
def push (S T X : Subrepresentation ρ) : Subrepresentation (quotientRep S T) where
  toSubmodule := (X.toSubmodule.comap T.toSubmodule.subtype).map (lower S T).mkQ
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨T.toRepresentation g x, X.apply_mem_toSubmodule g hx, (quotientRep_mk S T g x).symm⟩

/-- The preimage in `ρ` of an invariant subspace of the successive quotient. -/
def pull (S T : Subrepresentation ρ) (U : Subrepresentation (quotientRep S T)) :
    Subrepresentation ρ where
  toSubmodule := (U.toSubmodule.comap (lower S T).mkQ).map T.toSubmodule.subtype
  apply_mem_toSubmodule g := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨T.toRepresentation g x, ?_, rfl⟩
    have h := U.apply_mem_toSubmodule g hx
    rwa [quotientRep_mk] at h

theorem mem_bot_iff {W : Type uV} [AddCommGroup W] [Module k W] {σ : Representation k G W}
    {w : W} : w ∈ (⊥ : Subrepresentation σ) ↔ w = 0 :=
  Submodule.mem_bot k

theorem mem_top {W : Type uV} [AddCommGroup W] [Module k W] {σ : Representation k G W}
    {w : W} : w ∈ (⊤ : Subrepresentation σ) :=
  Submodule.mem_top

theorem mkQ_mem_bot_iff {S T : Subrepresentation ρ} (x : T.toSubmodule) :
    (lower S T).mkQ x ∈ (⊥ : Subrepresentation (quotientRep S T)) ↔ (x : V) ∈ S :=
  mem_bot_iff.trans (Submodule.Quotient.mk_eq_zero (lower S T))

/-- The actual successive quotient is irreducible exactly when `S` is covered by `T`. -/
theorem isIrreducible_quotientRep_iff {S T : Subrepresentation ρ} (hST : S ≤ T) :
    Representation.IsIrreducible (quotientRep S T) ↔ S ⋖ T := by
  constructor
  · intro hirr
    have hlt : S < T := by
      refine lt_of_le_of_ne hST ?_
      rintro rfl
      apply bot_ne_top (α := Subrepresentation (quotientRep S S))
      refine le_antisymm bot_le ?_
      intro q _
      obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (lower S S) q
      exact mem_bot_iff.mpr ((Submodule.Quotient.mk_eq_zero _).mpr x.2)
    refine ⟨hlt, fun X hSX hXT => ?_⟩
    rcases hirr.eq_bot_or_eq_top (push S T X) with h | h
    · apply hSX.not_ge
      intro v hv
      have hmem : (lower S T).mkQ ⟨v, hXT.le hv⟩ ∈ push S T X := ⟨⟨v, hXT.le hv⟩, hv, rfl⟩
      rw [h] at hmem
      exact (mkQ_mem_bot_iff (S := S) (T := T) ⟨v, hXT.le hv⟩).mp hmem
    · apply hXT.not_ge
      intro v hv
      have hmem : (lower S T).mkQ ⟨v, hv⟩ ∈ push S T X := by
        rw [h]
        exact mem_top
      obtain ⟨y, hy, hyx⟩ := hmem
      have hdiff : y - ⟨v, hv⟩ ∈ lower S T := (Submodule.Quotient.eq _).mp hyx
      have hdiff' : (y : V) - v ∈ X := hSX.le hdiff
      have hv' : v = (y : V) - ((y : V) - v) := by abel
      rw [hv']
      exact X.toSubmodule.sub_mem hy hdiff'
  · intro hcov
    have hTS : ¬ T ≤ S := hcov.lt.not_ge
    have hex : ∃ v ∈ T, v ∉ S := by
      by_contra hne
      exact hTS fun v hv => by_contra fun hvS => hne ⟨v, hv, hvS⟩
    obtain ⟨v, hvT, hvS⟩ := hex
    refine { exists_pair_ne := ⟨⊥, ⊤, ?_⟩, eq_bot_or_eq_top := fun U => ?_ }
    · intro h
      have hmem : (lower S T).mkQ ⟨v, hvT⟩ ∈ (⊥ : Subrepresentation (quotientRep S T)) := by
        rw [h]
        exact mem_top
      exact hvS ((mkQ_mem_bot_iff (S := S) (T := T) ⟨v, hvT⟩).mp hmem)
    · have hSU : S ≤ pull S T U := by
        intro w hw
        refine ⟨⟨w, hST hw⟩, ?_, rfl⟩
        show (lower S T).mkQ ⟨w, hST hw⟩ ∈ U.toSubmodule
        have h0 : (lower S T).mkQ ⟨w, hST hw⟩ = 0 :=
          (Submodule.Quotient.mk_eq_zero (lower S T)).mpr hw
        rw [h0]
        exact U.toSubmodule.zero_mem
      have hUT : pull S T U ≤ T := by
        rintro _ ⟨x, _, rfl⟩
        exact x.2
      rcases hcov.eq_or_eq hSU hUT with h | h
      · left
        refine le_antisymm ?_ bot_le
        intro q hq
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (lower S T) q
        have hx : (x : V) ∈ pull S T U := ⟨x, hq, rfl⟩
        rw [h] at hx
        exact mem_bot_iff.mpr ((Submodule.Quotient.mk_eq_zero _).mpr hx)
      · right
        refine le_antisymm le_top ?_
        intro q _
        obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective (lower S T) q
        have hx : (x : V) ∈ pull S T U := by
          rw [h]
          exact x.2
        obtain ⟨x', hx', hx'x⟩ := hx
        have : x' = x := Subtype.ext hx'x
        rw [← this]
        exact hx'

end Quotient

section Filtration

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G] {A : Rep.{uV} k G}

/-- Simple actual factors are exactly covering steps between consecutive invariant subspaces. -/
theorem hasSimpleFactors_iff_covBy {n : ℕ} (s : ObjectRepFiltration A n) :
    s.HasSimpleFactors ↔
      ∀ i : Fin n, s.subrepresentation i.castSucc ⋖ s.subrepresentation i.succ :=
  forall_congr' fun i =>
    isIrreducible_quotientRep_iff (s.monotone_subrepresentation
      (show i.castSucc < i.succ from Fin.castSucc_lt_succ).le)

/-- An actual composition series gives a module composition series from bottom to top. -/
theorem exists_compositionSeries {n : ℕ} (h : HasCompositionSeriesLength A n) :
    ∃ s : CompositionSeries (Submodule (MonoidAlgebra k G) A.ρ.asModule),
      s.head = ⊥ ∧ s.last = ⊤ ∧ s.length = n := by
  obtain ⟨f, hf⟩ := h
  have hcov := (hasSimpleFactors_iff_covBy f).mp hf
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.ρ)
  refine ⟨⟨n, fun i => e (f.subrepresentation i), fun i => ?_⟩, ?_, ?_, rfl⟩
  · exact (apply_covBy_apply_iff e).mpr (hcov i)
  · change e (f.subrepresentation 0) = ⊥
    rw [f.subrepresentation_zero]
    exact e.map_bot
  · change e (f.subrepresentation (Fin.last n)) = ⊤
    rw [f.subrepresentation_last]
    exact e.map_top

/-- A module composition series from bottom to top gives an actual composition series. -/
theorem hasCompositionSeriesLength_of_compositionSeries
    (s : CompositionSeries (Submodule (MonoidAlgebra k G) A.ρ.asModule))
    (h₀ : s.head = ⊥) (h₁ : s.last = ⊤) : HasCompositionSeriesLength A s.length := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.ρ)
  let f : ObjectRepFiltration A s.length :=
    ObjectRepFiltration.ofSubrepresentations (fun i => e.symm (s i))
      (e.symm.monotone.comp s.strictMono.monotone)
      (by
        change e.symm s.head = ⊥
        rw [h₀]
        exact e.symm.map_bot)
      (by
        change e.symm s.last = ⊤
        rw [h₁]
        exact e.symm.map_top)
  refine ⟨f, (hasSimpleFactors_iff_covBy f).mpr fun i => ?_⟩
  exact (apply_covBy_apply_iff e.symm).mpr (s.step i)

/-- Every strict chain is bounded by the length of an actual composition series. -/
theorem le_of_hasCompositionSeriesLength {n : ℕ} (h : HasCompositionSeriesLength A n)
    {m : ℕ} (c : Fin (m + 1) → Subrepresentation A.ρ) (hc : StrictMono c) : m ≤ n := by
  obtain ⟨s, h₀, h₁, hlen⟩ := exists_compositionSeries h
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.ρ)
  have hm := Order.LTSeries.length_le_krullDim (LTSeries.mk m (fun i => e (c i)) (e.strictMono.comp hc))
  rw [← Module.coe_length, ← Module.length_compositionSeries s h₀ h₁, hlen] at hm
  exact_mod_cast hm

/-- A uniform bound on strict chains yields an actual composition series within the bound. -/
theorem hasCompositionLengthAtMost_of_bound {b : ℕ}
    (H : ∀ (m : ℕ) (c : Fin (m + 1) → Subrepresentation A.ρ), StrictMono c → m ≤ b) :
    HasCompositionLengthAtMost A b := by
  let e := Subrepresentation.subrepresentationSubmoduleOrderIso (ρ := A.ρ)
  have hdim : Order.krullDim (Submodule (MonoidAlgebra k G) A.ρ.asModule) ≤ (b : ℕ∞) := by
    rw [Order.krullDim, iSup_le_iff]
    intro p
    have hp := H p.length (fun i => e.symm (p i)) (e.symm.strictMono.comp p.strictMono)
    exact_mod_cast hp
  have hfin : IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule := by
    rw [← Module.length_ne_top_iff]
    intro htop
    rw [← Module.coe_length, htop] at hdim
    exact absurd (WithBot.coe_le_coe.mp hdim) (by simp)
  obtain ⟨s, h₀, h₁⟩ := isFiniteLength_iff_exists_compositionSeries.mp hfin
  exact ⟨s.length, H s.length (fun i => e.symm (s i)) (e.symm.strictMono.comp s.strictMono),
    hasCompositionSeriesLength_of_compositionSeries s h₀ h₁⟩

/-- An actual composition series gives finite length over the monoid algebra. -/
theorem isFiniteLength_of_hasCompositionSeriesLength {n : ℕ}
    (h : HasCompositionSeriesLength A n) :
    IsFiniteLength (MonoidAlgebra k G) A.ρ.asModule := by
  obtain ⟨s, h₀, h₁, -⟩ := exists_compositionSeries h
  exact isFiniteLength_of_exists_compositionSeries ⟨s, h₀, h₁⟩

end Filtration

end LengthCriterionProof

open LengthCriterionProof in
/-- The bounded-chain criterion for actual representation composition length. -/
theorem objectCompositionLengthCriterion : ObjectCompositionLengthCriterion.{uK, uG, uV} := by
  intro k _ G _ A b
  refine ⟨⟨?_, hasCompositionLengthAtMost_of_bound⟩, ?_⟩
  · rintro ⟨n, hn, h⟩ m c hc
    exact (le_of_hasCompositionSeriesLength h c hc).trans hn
  · rintro ⟨n, -, h⟩
    exact isFiniteLength_of_hasCompositionSeriesLength h

end Langlands

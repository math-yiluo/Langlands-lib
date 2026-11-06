import Langlands.Representation.Classification.UnitaryGenericStatement

/-! # Involutive matching of Hermitian inducing parameters -/

noncomputable section

namespace Langlands.Classification

open CategoryTheory GeneralLinear

universe u uF uV

/-- Choose the given matching on positive exponents, its inverse on negative
exponents, and the identity on zero exponents. -/
def oppositeExponentPartner {I : Type u} (e : I ≃ I) (s : I → ℝ) (i : I) : I :=
  if 0 < s i then e i else if s i < 0 then e.symm i else i

theorem oppositeExponentPartner_exponent {I : Type u} (e : I ≃ I) (s : I → ℝ)
    (hs : ∀ i, s (e i) = -s i) (i : I) :
    s (oppositeExponentPartner e s i) = -s i := by
  have hinv : s (e.symm i) = -s i := by
    have h := hs (e.symm i)
    rw [e.apply_symm_apply] at h
    linarith
  unfold oppositeExponentPartner
  split_ifs with hp hn
  · exact hs i
  · exact hinv
  · have : s i = 0 := le_antisymm (le_of_not_gt hp) (le_of_not_gt hn)
    simp [this]

theorem oppositeExponentPartner_involutive {I : Type u} (e : I ≃ I) (s : I → ℝ)
    (hs : ∀ i, s (e i) = -s i) :
    Function.Involutive (oppositeExponentPartner e s) := by
  intro i
  have hinv : s (e.symm i) = -s i := by
    have h := hs (e.symm i)
    rw [e.apply_symm_apply] at h
    linarith
  by_cases hp : 0 < s i
  · have hn : s (e i) < 0 := by rw [hs]; linarith
    simp [oppositeExponentPartner, hp, hn, not_lt_of_ge (le_of_lt hn)]
  · by_cases hn : s i < 0
    · have hp' : 0 < s (e.symm i) := by rw [hinv]; linarith
      simp [oppositeExponentPartner, hp, hn, hp']
    · simp [oppositeExponentPartner, hp, hn]

/-- The canonical involutive opposite-exponent matching. -/
def oppositeExponentInvolution {I : Type u} (e : I ≃ I) (s : I → ℝ)
    (hs : ∀ i, s (e i) = -s i) : I ≃ I :=
  { toFun := oppositeExponentPartner e s
    invFun := oppositeExponentPartner e s
    left_inv := oppositeExponentPartner_involutive e s hs
    right_inv := oppositeExponentPartner_involutive e s hs }

/-- Any reflexive symmetric matching property of the original permutation is
preserved by the involutive matching, including multiplicities. -/
theorem oppositeExponentPartner_relation {I : Type u} (e : I ≃ I) (s : I → ℝ)
    (R : I → I → Prop) (hrefl : ∀ i, R i i)
    (hsymm : ∀ i j, R i j → R j i) (he : ∀ i, R i (e i)) (i : I) :
    R i (oppositeExponentPartner e s i) := by
  unfold oppositeExponentPartner
  split_ifs
  · exact he i
  · apply hsymm (e.symm i) i
    simpa only [e.apply_symm_apply] using he (e.symm i)
  · exact hrefl i

private theorem nonempty_transport_iso_symm {J : Type*} {C : J → Type*}
    [∀ j, Category (C j)] {a b : J} (h : a = b) (X : C a) (Y : C b)
    (hXY : Nonempty ((h ▸ X) ≅ Y)) : Nonempty ((h.symm ▸ Y) ≅ X) := by
  cases h
  obtain ⟨E⟩ := hXY
  exact ⟨E.symm⟩

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} {T : F.TopologicalData}

/-- Hermitian parameter symmetry admits an involutive rank-preserving matching
by actual block isomorphisms; no ordinary self-duality is asserted. -/
theorem HasHermitianSymmetricParameters.exists_involutive
    {n : ℕ} {B : BlockShape n}
    {δ : letI := T.topology
      ∀ i, SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear (B.size i) F.Carrier)}
    {s : Fin B.length → ℝ}
    (h : HasHermitianSymmetricParameters F T B δ s) :
    letI := T.topology
    ∃ (e : Fin B.length ≃ Fin B.length) (hr : ∀ i, B.size i = B.size (e i)),
      Function.Involutive e ∧
      ∀ i, s (e i) = -s i ∧ Nonempty ((hr i ▸ δ i) ≅ δ (e i)) := by
  let := T.topology
  obtain ⟨e, hr, he⟩ := h
  have hs : ∀ i, s (e i) = -s i := by
    intro i
    have := (he i).1
    linarith
  let R : Fin B.length → Fin B.length → Prop :=
    fun i j => ∃ h : B.size i = B.size j, Nonempty ((h ▸ δ i) ≅ δ j)
  have hrefl : ∀ i, R i i := fun i => ⟨rfl, ⟨Iso.refl _⟩⟩
  have hsymm : ∀ i j, R i j → R j i := by
    rintro i j ⟨hij, hE⟩
    exact ⟨hij.symm, nonempty_transport_iso_symm
      (C := fun a => SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear a F.Carrier))
      hij (δ i) (δ j) hE⟩
  have hrel : ∀ i, R i (oppositeExponentPartner e s i) :=
    oppositeExponentPartner_relation e s R hrefl hsymm
      (fun i => ⟨hr i, (he i).2⟩)
  choose hr' hi using hrel
  refine ⟨oppositeExponentInvolution e s hs, hr',
    oppositeExponentPartner_involutive e s hs, ?_⟩
  intro i
  exact ⟨oppositeExponentPartner_exponent e s hs i, hi i⟩

end Langlands.Classification

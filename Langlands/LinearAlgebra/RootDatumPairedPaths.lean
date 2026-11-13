import Langlands.LinearAlgebra.RootDatumPathUniqueness
import Langlands.LinearAlgebra.EvenPathDistance

/-! # Paired simple roots of a pairing-compatible action and their even paths -/

noncomputable section

open Set Function

set_option autoImplicit false

namespace Langlands.LinearAlgebra.RootDatumPairedPaths

open RootDatumOrbitPairs RootDatumReversedPath RootDatumPathWeights
open Langlands.GroupScheme.SplitPinning (middleDistance)

variable {ι M N : Type*} [Finite ι] [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum ι M N} {b : P.Base} {Γ : Type*} [Group Γ]
    (ρ : Γ →* Equiv.Perm b.support)

/-- A simple root is paired if some group element moves it to a distinct simple root that
is not orthogonal to it. -/
def IsPaired (a : b.support) : Prop :=
  ∃ γ : Γ, ρ γ a ≠ a ∧ ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)

open Classical in
/-- The partner of a paired simple root, the unique distinct non-orthogonal simple root in
its orbit. An unpaired simple root is its own partner. -/
def partner (a : b.support) : b.support :=
  if h : IsPaired ρ a then ρ h.choose a else a

/-- An auxiliary injective numbering of the simple roots, used to select one root of each
pair. -/
def key (a : b.support) : ℕ := (Fintype.equivFin b.support a : ℕ)

omit [Finite ι] in
theorem key_injective : Function.Injective (key (b := b)) := by
  intro a a' h
  exact (Fintype.equivFin b.support).injective (Fin.ext h)

theorem middleDistance_rev (m : ℕ) (j : Fin (2 * m)) :
    middleDistance m (j.rev : ℕ) = middleDistance m j := by
  have := j.2
  simp only [middleDistance, Fin.val_rev]
  split_ifs <;> omega

variable {ρ}

omit [Finite ι] in
theorem IsPaired.exists_eq_partner {a : b.support} (h : IsPaired ρ a) :
    ∃ γ : Γ, ρ γ a = partner ρ a ∧ ρ γ a ≠ a ∧ ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι) := by
  classical
  refine ⟨h.choose, ?_, h.choose_spec.1, h.choose_spec.2⟩
  simp [partner, h]

omit [Finite ι] in
theorem IsPaired.partner_ne {a : b.support} (h : IsPaired ρ a) : partner ρ a ≠ a := by
  obtain ⟨δ, hδ, hδa, -⟩ := h.exists_eq_partner
  rwa [← hδ]

omit [Finite ι] in
theorem not_isOrthogonal_of_not_isPaired {z : b.support} (hz : ¬ IsPaired ρ z) (γ : Γ)
    (hγ : ρ γ z ≠ z) : P.IsOrthogonal (z : ι) (ρ γ z : ι) := by
  by_contra ho
  exact hz ⟨γ, hγ, ho⟩

omit [Finite ι] in
private theorem conj_apply (σ γ : Γ) (a : b.support) :
    ρ (σ * γ * σ⁻¹) (ρ σ a) = ρ σ (ρ γ a) := by
  simp [Equiv.Perm.mul_apply]

section Compatible

variable (hρ : IsPairingCompatible b ρ)
include hρ

/-- The partner is the only distinct non-orthogonal simple root in the orbit. -/
theorem IsPaired.eq_partner {a : b.support} (h : IsPaired ρ a) {γ : Γ} (hγ : ρ γ a ≠ a)
    (hγo : ¬ P.IsOrthogonal (a : ι) (ρ γ a : ι)) : ρ γ a = partner ρ a := by
  obtain ⟨δ, hδ, hδa, hδo⟩ := h.exists_eq_partner
  rw [← hδ]
  exact eq_of_not_isOrthogonal hρ a hγ hδa hγo hδo

/-- A paired simple root and its partner form an `A₂` pair. -/
theorem IsPaired.pairing_partner {a : b.support} (h : IsPaired ρ a) :
    P.pairing (a : ι) (partner ρ a : ι) = -1 ∧ P.pairing (partner ρ a : ι) (a : ι) = -1 := by
  obtain ⟨δ, hδ, hδa, hδo⟩ := h.exists_eq_partner
  rw [← hδ]
  exact pairing_eq_neg_one_of_not_isOrthogonal hρ a hδa hδo

private theorem IsPaired.partner_aux {a : b.support} (h : IsPaired ρ a) :
    ∃ δ : Γ, ρ δ (partner ρ a) = a ∧ a ≠ partner ρ a ∧
      ¬ P.IsOrthogonal (partner ρ a : ι) (a : ι) := by
  obtain ⟨δ, hδ, hδa, hδo⟩ := h.exists_eq_partner
  have h2 := apply_apply_eq_of_not_isOrthogonal hρ a hδa hδo
  rw [← hδ]
  exact ⟨δ, h2, Ne.symm hδa, fun ho => hδo ⟨ho.2, ho.1⟩⟩

/-- The partner of a paired simple root is paired. -/
theorem IsPaired.partner_isPaired {a : b.support} (h : IsPaired ρ a) :
    IsPaired ρ (partner ρ a) := by
  obtain ⟨δ, h2, hne, ho⟩ := h.partner_aux hρ
  exact ⟨δ, by rw [h2]; exact hne, by rw [h2]; exact ho⟩

/-- Taking partners is an involution on paired simple roots. -/
theorem IsPaired.partner_partner {a : b.support} (h : IsPaired ρ a) :
    partner ρ (partner ρ a) = a := by
  obtain ⟨δ, h2, hne, ho⟩ := h.partner_aux hρ
  rw [← (h.partner_isPaired hρ).eq_partner hρ (γ := δ) (by rw [h2]; exact hne)
    (by rw [h2]; exact ho), h2]

omit [Finite ι] in
private theorem isOrthogonal_apply (σ : Γ) (a c : b.support) :
    P.IsOrthogonal (ρ σ a : ι) (ρ σ c : ι) ↔ P.IsOrthogonal (a : ι) (c : ι) := by
  simp only [RootPairing.IsOrthogonal, hρ.pairing_apply]

/-- Pairedness is invariant under the action. -/
theorem IsPaired.apply {a : b.support} (h : IsPaired ρ a) (σ : Γ) : IsPaired ρ (ρ σ a) := by
  obtain ⟨γ, hγ, hγo⟩ := h
  refine ⟨σ * γ * σ⁻¹, ?_, ?_⟩
  · rw [conj_apply]
    exact fun h' => hγ ((ρ σ).injective h')
  · rw [conj_apply, isOrthogonal_apply hρ]
    exact hγo

theorem isPaired_apply_iff {a : b.support} (σ : Γ) : IsPaired ρ (ρ σ a) ↔ IsPaired ρ a := by
  refine ⟨fun h => ?_, fun h => h.apply hρ σ⟩
  have := h.apply hρ σ⁻¹
  simpa using this

/-- The action commutes with taking partners. -/
theorem IsPaired.partner_apply {a : b.support} (h : IsPaired ρ a) (σ : Γ) :
    partner ρ (ρ σ a) = ρ σ (partner ρ a) := by
  obtain ⟨δ, hδ, hδa, hδo⟩ := h.exists_eq_partner
  rw [← hδ, ← conj_apply]
  symm
  apply (h.apply hρ σ).eq_partner hρ
  · rw [conj_apply]
    exact fun h' => hδa ((ρ σ).injective h')
  · rw [conj_apply, isOrthogonal_apply hρ]
    exact hδo

end Compatible

variable (ρ) in
/-- The index set of the pairs: the paired simple roots of smaller `key` than their
partners. -/
def PairIndex : Type _ := {a : b.support // IsPaired ρ a ∧ key a < key (partner ρ a)}

instance : Finite (PairIndex ρ) :=
  inferInstanceAs (Finite {a : b.support // IsPaired ρ a ∧ key a < key (partner ρ a)})

open Classical in
variable (ρ) in
/-- The selected root of the pair of a paired simple root. -/
def pairRep (a : b.support) : b.support :=
  if key a < key (partner ρ a) then a else partner ρ a

omit [Finite ι] in
theorem pairRep_val (c : PairIndex ρ) : pairRep ρ c.1 = c.1 := by
  simp [pairRep, c.2.2]

section Compatible

variable (hρ : IsPairingCompatible b ρ)
include hρ

omit hρ in
private theorem key_partner_ne {a : b.support} (h : IsPaired ρ a) :
    key (partner ρ a) ≠ key a :=
  fun he => h.partner_ne (key_injective he)

theorem pairRep_spec {a : b.support} (h : IsPaired ρ a) :
    IsPaired ρ (pairRep ρ a) ∧ key (pairRep ρ a) < key (partner ρ (pairRep ρ a)) := by
  classical
  have hne := key_partner_ne h
  unfold pairRep
  split_ifs with hk
  · exact ⟨h, hk⟩
  · refine ⟨h.partner_isPaired hρ, ?_⟩
    rw [h.partner_partner hρ]
    omega

theorem pairRep_partner {a : b.support} (h : IsPaired ρ a) :
    pairRep ρ (partner ρ a) = pairRep ρ a := by
  classical
  have hne := key_partner_ne h
  unfold pairRep
  rw [h.partner_partner hρ]
  by_cases hk : key a < key (partner ρ a)
  · simp [hk, show ¬ key (partner ρ a) < key a by omega]
  · simp [hk, show key (partner ρ a) < key a by omega]

theorem pairRep_apply_pairRep {a : b.support} (h : IsPaired ρ a) (σ : Γ) :
    pairRep ρ (ρ σ (pairRep ρ a)) = pairRep ρ (ρ σ a) := by
  classical
  by_cases hk : key a < key (partner ρ a)
  · rw [show pairRep ρ a = a by simp [pairRep, hk]]
  · rw [show pairRep ρ a = partner ρ a by simp [pairRep, hk], ← h.partner_apply hρ σ,
      pairRep_partner hρ (h.apply hρ σ)]

/-- The action on pairs: move the selected root and select again. -/
def pairSMul (σ : Γ) (c : PairIndex ρ) : PairIndex ρ :=
  ⟨pairRep ρ (ρ σ c.1), pairRep_spec hρ (c.2.1.apply hρ σ)⟩

/-- The induced action of the group on the pairs. -/
abbrev pairAction : MulAction Γ (PairIndex ρ) where
  smul := pairSMul hρ
  one_smul c := Subtype.ext (by
    change pairRep ρ (ρ 1 c.1) = c.1
    rw [map_one, Equiv.Perm.one_apply, pairRep_val])
  mul_smul σ τ c := Subtype.ext (by
    change pairRep ρ (ρ (σ * τ) c.1) = pairRep ρ (ρ σ (pairRep ρ (ρ τ c.1)))
    rw [pairRep_apply_pairRep hρ (c.2.1.apply hρ τ), map_mul, Equiv.Perm.mul_apply])

theorem pairSMul_val (σ : Γ) (c : PairIndex ρ) : (pairSMul hρ σ c).1 = pairRep ρ (ρ σ c.1) :=
  rfl

/-- A group element carries the selected root and its partner to the selected root and
the partner of the image pair, in the same or in the opposite order. -/
theorem pairSMul_orientation (σ : Γ) (c : PairIndex ρ) :
    ((pairSMul hρ σ c).1 = ρ σ c.1 ∧ partner ρ (pairSMul hρ σ c).1 = ρ σ (partner ρ c.1)) ∨
      ((pairSMul hρ σ c).1 = ρ σ (partner ρ c.1) ∧
        partner ρ (pairSMul hρ σ c).1 = ρ σ c.1) := by
  classical
  have hc := c.2.1
  rw [pairSMul_val]
  unfold pairRep
  split_ifs with hk
  · exact Or.inl ⟨rfl, hc.partner_apply hρ σ⟩
  · exact Or.inr ⟨hc.partner_apply hρ σ, (hc.apply hρ σ).partner_partner hρ⟩

/-- A paired simple root and its partner are the middle pair of a path component of even
length. -/
theorem IsPaired.exists_path {a : b.support} (h : IsPaired ρ a) :
    ∃ (m : ℕ) (β : Fin (2 * m) → b.support), IsPathComponent β ∧
      (∀ i : Fin (2 * m), (i : ℕ) + 1 = m → β i = a) ∧
      (∀ i : Fin (2 * m), (i : ℕ) = m → β i = partner ρ a) := by
  obtain ⟨δ, hδ, hδa, hδo⟩ := h.exists_eq_partner
  obtain ⟨m, β, hβ, hβa⟩ := exists_isReversedPath hρ hδa hδo
  refine ⟨m, β, hβ.isPathComponent, hβa, fun i hi => ?_⟩
  have hm := hβ.pos
  let j : Fin (2 * m) := ⟨m - 1, by omega⟩
  have hj : β j = a := hβa j (by simp only [j]; omega)
  have hrev : j.rev = i := by
    ext
    simp only [j, Fin.val_rev]
    omega
  rw [← hrev, ← hβ.apply_eq_rev, hj, hδ]

/-- Half the length of the path of a pair. -/
def half (c : PairIndex ρ) : ℕ := (c.2.1.exists_path hρ).choose

/-- The path component of a pair, in path order, with the pair in the middle. -/
def path (c : PairIndex ρ) : Fin (2 * half hρ c) → b.support :=
  (c.2.1.exists_path hρ).choose_spec.choose

theorem path_spec (c : PairIndex ρ) :
    IsPathComponent (path hρ c) ∧
      (∀ i : Fin (2 * half hρ c), (i : ℕ) + 1 = half hρ c → path hρ c i = c.1) ∧
      (∀ i : Fin (2 * half hρ c), (i : ℕ) = half hρ c → path hρ c i = partner ρ c.1) :=
  (c.2.1.exists_path hρ).choose_spec.choose_spec

theorem isPathComponent_path (c : PairIndex ρ) : IsPathComponent (path hρ c) :=
  (path_spec hρ c).1

theorem half_pos (c : PairIndex ρ) : 0 < half hρ c := by
  have := (isPathComponent_path hρ c).pos
  omega

theorem path_left (c : PairIndex ρ) :
    path hρ c ⟨half hρ c - 1, by have := half_pos hρ c; omega⟩ = c.1 :=
  (path_spec hρ c).2.1 _ (by have := half_pos hρ c; simp only; omega)

theorem path_right (c : PairIndex ρ) :
    path hρ c ⟨half hρ c, by have := half_pos hρ c; omega⟩ = partner ρ c.1 :=
  (path_spec hρ c).2.2 _ rfl

/-- Paths of distinct pairs are disjoint. -/
theorem path_disjoint (c c' : PairIndex ρ) (i : Fin (2 * half hρ c))
    (i' : Fin (2 * half hρ c')) (h : path hρ c i = path hρ c' i') : c = c' := by
  obtain ⟨hL, hβ⟩ := (isPathComponent_path hρ c).eq_or_eq_rev (isPathComponent_path hρ c') h
  have hm : half hρ c' = half hρ c := by omega
  have hpos := half_pos hρ c
  have hmid : c'.1 = c.1 ∨ c'.1 = partner ρ c.1 := by
    rcases hβ with hβ | hβ
    · left
      rw [← path_left hρ c', hβ, ← path_left hρ c]
      congr 1
      ext
      simp [hm]
    · right
      rw [← path_left hρ c', hβ, ← path_right hρ c]
      congr 1
      ext
      simp only [Fin.val_rev, Fin.val_cast]
      omega
  rcases hmid with h1 | h1
  · exact (Subtype.ext h1).symm
  · exfalso
    have k1 := c.2.2
    have k2 := c'.2.2
    rw [h1, c.2.1.partner_partner hρ] at k2
    omega

/-- The image under a group element of a vertex of a path is a vertex of the image path, at
the same distance from the middle pair. -/
theorem exists_path_smul (σ : Γ) (c : PairIndex ρ) (i : Fin (2 * half hρ c)) :
    ∃ i' : Fin (2 * half hρ (pairSMul hρ σ c)),
      path hρ (pairSMul hρ σ c) i' = ρ σ (path hρ c i) ∧
        middleDistance (half hρ (pairSMul hρ σ c)) i' = middleDistance (half hρ c) i := by
  have hβ := isPathComponent_path hρ (pairSMul hρ σ c)
  have hβ' : IsPathComponent (fun j => ρ σ (path hρ c j)) :=
    (isPathComponent_path hρ c).comp_perm (ρ σ) (fun u v => hρ.pairing_apply σ u v)
  have hpos := half_pos hρ c
  have hpos' := half_pos hρ (pairSMul hρ σ c)
  -- the two paths share a middle vertex
  have hshare : ∃ (j : Fin (2 * half hρ (pairSMul hρ σ c))) (j' : Fin (2 * half hρ c)),
      path hρ (pairSMul hρ σ c) j = ρ σ (path hρ c j') := by
    refine ⟨⟨half hρ (pairSMul hρ σ c) - 1, by omega⟩, ?_⟩
    rw [path_left]
    rcases pairSMul_orientation hρ σ c with h | h
    · exact ⟨⟨half hρ c - 1, by omega⟩, by rw [path_left, h.1]⟩
    · exact ⟨⟨half hρ c, by omega⟩, by rw [path_right, h.1]⟩
  obtain ⟨j, j', hjj⟩ := hshare
  obtain ⟨hL, hrel⟩ := hβ.eq_or_eq_rev hβ' hjj
  have hm : half hρ c = half hρ (pairSMul hρ σ c) := by omega
  rcases hrel with hrel | hrel
  · refine ⟨Fin.cast (hβ.length_eq hβ' hjj) i, (hrel i).symm, ?_⟩
    simp only [Fin.val_cast, hm]
  · refine ⟨Fin.rev (Fin.cast (hβ.length_eq hβ' hjj) i), (hrel i).symm, ?_⟩
    rw [middleDistance_rev]
    simp only [Fin.val_cast, hm]

open Classical in
/-- The distance of a simple root from the middle pair of the path containing it, and `0`
for simple roots on no path. -/
def level (z : b.support) : ℕ :=
  if h : ∃ (c : PairIndex ρ) (i : Fin (2 * half hρ c)), path hρ c i = z then
    middleDistance (half hρ h.choose) h.choose_spec.choose else 0

theorem middleDistance_eq_of_path_eq {c c' : PairIndex ρ} {i : Fin (2 * half hρ c)}
    {i' : Fin (2 * half hρ c')} (h : path hρ c i = path hρ c' i') :
    middleDistance (half hρ c) i = middleDistance (half hρ c') i' := by
  have hc := path_disjoint hρ c c' i i' h
  subst hc
  rw [(isPathComponent_path hρ c).injective h]

theorem level_path (c : PairIndex ρ) (i : Fin (2 * half hρ c)) :
    level hρ (path hρ c i) = middleDistance (half hρ c) i := by
  classical
  have h : ∃ (c' : PairIndex ρ) (i' : Fin (2 * half hρ c')), path hρ c' i' = path hρ c i :=
    ⟨c, i, rfl⟩
  simp only [level, h, dite_true]
  exact middleDistance_eq_of_path_eq hρ h.choose_spec.choose_spec

/-- The level is invariant under the action. -/
theorem level_apply (σ : Γ) (z : b.support) : level hρ (ρ σ z) = level hρ z := by
  classical
  by_cases h : ∃ (c : PairIndex ρ) (i : Fin (2 * half hρ c)), path hρ c i = z
  · obtain ⟨c, i, rfl⟩ := h
    obtain ⟨i', hi', hd⟩ := exists_path_smul hρ σ c i
    rw [← hi', level_path, level_path, hd]
  · have h' : ¬ ∃ (c : PairIndex ρ) (i : Fin (2 * half hρ c)), path hρ c i = ρ σ z := by
      rintro ⟨c, i, hci⟩
      obtain ⟨i', hi', -⟩ := exists_path_smul hρ σ⁻¹ c i
      apply h
      refine ⟨_, i', ?_⟩
      rw [hi', hci]
      simp
    rw [level, level, dif_neg h, dif_neg h']

/-- A simple root is paired exactly when it is the selected root or the partner of some
pair. -/
theorem isPaired_iff_exists (z : b.support) :
    IsPaired ρ z ↔ ∃ c : PairIndex ρ, z = c.1 ∨ z = partner ρ c.1 := by
  classical
  constructor
  · intro h
    refine ⟨⟨pairRep ρ z, pairRep_spec hρ h⟩, ?_⟩
    change z = pairRep ρ z ∨ z = partner ρ (pairRep ρ z)
    unfold pairRep
    split_ifs
    · exact Or.inl rfl
    · exact Or.inr (h.partner_partner hρ).symm
  · rintro ⟨c, rfl | rfl⟩
    · exact c.2.1
    · exact c.2.1.partner_isPaired hρ

end Compatible

end Langlands.LinearAlgebra.RootDatumPairedPaths

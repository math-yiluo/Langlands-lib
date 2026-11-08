import Mathlib.LinearAlgebra.RootSystem.Finite.Lemmas
import Mathlib.LinearAlgebra.RootSystem.Finite.Nondegenerate

/-! # Orbit partners of roots under a finite group of root-datum automorphisms -/

noncomputable section

namespace RootPairing

namespace OrbitPartner

variable {J : Type*} {M N : Type*} [AddCommGroup M] [AddCommGroup N]
  (P : RootDatum J M N) {Γ : Type*} [Group Γ] [Fintype Γ] (ρ : Γ →* P.Aut)

/-- The sum, over a finite group acting by root-datum automorphisms, of the roots in the
orbit of a root index. -/
def orbitSum (i : J) : M :=
  ∑ g : Γ, P.root (ρ g • i)

/-- An orbit partner of `p` is a root index `q` in the orbit of `p`, different from `p`,
such that the sum of the roots of `p` and `q` is again a root. -/
def IsOrbitPartner (p q : J) : Prop :=
  (∃ g : Γ, ρ g • p = q) ∧ q ≠ p ∧ P.root p + P.root q ∈ Set.range P.root

omit [Fintype Γ] in
theorem root_smul (g : Γ) (i : J) : P.root (ρ g • i) = ρ g • P.root i :=
  RootPairing.Equiv.root_indexEquiv_eq_smul (i := i) (g := ρ g)

theorem orbitSum_eq_sum_smul (i : J) :
    orbitSum P ρ i = ∑ g : Γ, ρ g • P.root i := by
  unfold orbitSum
  exact Finset.sum_congr rfl fun g _ => root_smul P ρ g i

/-- The orbit sum is constant along the orbit. -/
theorem orbitSum_smul (g : Γ) (i : J) :
    orbitSum P ρ (ρ g • i) = orbitSum P ρ i := by
  unfold orbitSum
  simp_rw [← mul_smul, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl

/-- Orbit sums are additive along actual root differences. -/
theorem orbitSum_eq_sub_of_root_eq_sub {m a b : J}
    (h : P.root m = P.root a - P.root b) :
    orbitSum P ρ m = orbitSum P ρ a - orbitSum P ρ b := by
  simp only [orbitSum_eq_sum_smul, h, smul_sub, Finset.sum_sub_distrib]

/-- Root-datum automorphisms preserve pairings. -/
theorem pairing_smul_smul (w : P.Aut) (i j : J) :
    P.pairing (w • i) (w • j) = P.pairing i j :=
  w.toHom.pairing

/-- Pairing the orbit sum of `i` with the coroot of `j` sums the pairings of `i` with
the orbit of `j`. -/
theorem sum_pairing_smul_right (i j : J) :
    ∑ g : Γ, P.pairing i (ρ g • j) = P.toLinearMap (orbitSum P ρ i) (P.coroot j) := by
  unfold orbitSum
  rw [map_sum, LinearMap.sum_apply]
  simp only [root_coroot_eq_pairing]
  refine Fintype.sum_equiv (Equiv.inv Γ) _ _ fun g => ?_
  rw [← pairing_smul_smul P (ρ g⁻¹) i (ρ g • j), ← mul_smul, ← map_mul, inv_mul_cancel,
    map_one, one_smul]
  rfl

/-- The orbit sum of a root pairs with the coroots of all members of its orbit equally. -/
theorem toLinearMap_orbitSum_coroot_smul (g : Γ) (j : J) :
    P.toLinearMap (orbitSum P ρ j) (P.coroot (ρ g • j)) =
      P.toLinearMap (orbitSum P ρ j) (P.coroot j) := by
  rw [← sum_pairing_smul_right, ← sum_pairing_smul_right]
  simp_rw [← mul_smul, ← map_mul]
  exact Fintype.sum_equiv (Equiv.mulRight g) _ _ fun _ => rfl

variable {P ρ}

/-- If no orbit sum vanishes, the pairings of a root with the members of its orbit have
positive sum. -/
theorem sum_pairing_smul_pos [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0) (j : J) :
    0 < ∑ g : Γ, P.pairing j (ρ g • j) := by
  classical
  have _ : Fintype J := Fintype.ofFinite J
  set x := orbitSum P ρ j with hx
  set c := P.toLinearMap x (P.coroot j) with hc
  have hxspan : x ∈ P.rootSpan ℤ :=
    Submodule.sum_mem _ fun g _ => Submodule.subset_span ⟨_, rfl⟩
  have hBx : 0 < P.RootForm x x := P.rootForm_pos_of_ne_zero hxspan (hne j)
  have hterm : ∀ g : Γ, 2 * P.RootForm (P.root (ρ g • j)) x =
      P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j)) * c := by
    intro g
    have h := congrArg (fun y => P.toLinearMap x y) (P.rootForm_self_smul_coroot (ρ g • j))
    simp only [map_smul, map_nsmul, smul_eq_mul, nsmul_eq_mul,
      toLinearMap_apply_apply_Polarization] at h
    rw [toLinearMap_orbitSum_coroot_smul] at h
    push_cast at h
    linarith
  have hxx : 2 * P.RootForm x x =
      (∑ g : Γ, P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j))) * c := by
    have hx' : P.RootForm x x = ∑ g : Γ, P.RootForm (P.root (ρ g • j)) x := by
      change P.RootForm (∑ g : Γ, P.root (ρ g • j)) x = _
      rw [map_sum, LinearMap.sum_apply]
    rw [hx', Finset.mul_sum, Finset.sum_mul]
    exact Finset.sum_congr rfl fun g _ => hterm g
  have hS : 0 ≤ ∑ g : Γ, P.RootForm (P.root (ρ g • j)) (P.root (ρ g • j)) :=
    Finset.sum_nonneg fun g _ => P.zero_le_rootForm _
  have hcpos : 0 < c := by
    by_contra! hc'
    nlinarith
  rw [sum_pairing_smul_right]
  exact hcpos

/-- Distinct members of one orbit pair nonpositively. -/
theorem pairing_nonpos [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0) {p q : J}
    (hq : ∃ g : Γ, ρ g • p = q) (hpq : p ≠ q) : P.pairing p q ≤ 0 := by
  obtain ⟨g, rfl⟩ := hq
  by_contra! hpos
  have hpos' : 0 < P.pairingIn ℤ p (ρ g • p) := by
    have h := P.algebraMap_pairingIn ℤ p (ρ g • p)
    simp only [Algebra.algebraMap_self_apply] at h
    rwa [h]
  obtain ⟨m, hm⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos' hpq
  apply hne m
  rw [orbitSum_eq_sub_of_root_eq_sub P ρ hm, orbitSum_smul, sub_self]

omit [Fintype Γ] in
theorem IsOrbitPartner.symm {p q : J} (h : IsOrbitPartner P ρ p q) :
    IsOrbitPartner P ρ q p := by
  obtain ⟨⟨g, hg⟩, hqp, hm⟩ := h
  refine ⟨⟨g⁻¹, ?_⟩, hqp.symm, ?_⟩
  · rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · rwa [add_comm]

/-- An orbit partner pairs negatively. -/
theorem IsOrbitPartner.pairing_neg [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0) {p q : J}
    (h : IsOrbitPartner P ρ p q) : P.pairing p q < 0 := by
  obtain ⟨⟨g, hg⟩, hqp, ⟨m, hm⟩⟩ := h
  have hle := pairing_nonpos hne ⟨g, hg⟩ hqp.symm
  refine lt_of_le_of_ne hle fun h0 => ?_
  have hmq : P.pairing m q = 2 := by
    rw [pairing_eq_add_of_root_eq_add hm, h0, pairing_same, zero_add]
  have hr : P.root (P.reflectionPerm q m) = P.root p - P.root q := by
    rw [root_reflectionPerm, reflection_apply_root, hmq, hm, two_smul]
    abel
  apply hne (P.reflectionPerm q m)
  rw [orbitSum_eq_sub_of_root_eq_sub P ρ hr, ← hg, orbitSum_smul, sub_self]

/-- The members of `Γ` sending `i` to a given member of its orbit are as numerous as the
stabilizer of `i`. -/
theorem card_filter_smul_eq [DecidableEq J] (g : Γ) (i : J) :
    (Finset.univ.filter fun h : Γ => ρ h • i = ρ g • i).card =
      (Finset.univ.filter fun h : Γ => ρ h • i = i).card := by
  classical
  refine Finset.card_nbij' (fun h => g⁻¹ * h) (fun h => g * h) ?_ ?_ ?_ ?_
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
    rw [map_mul, mul_smul, hh, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  · intro h hh
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hh ⊢
    rw [map_mul, mul_smul, hh]
  · intro h _
    simp
  · intro h _
    simp

/-- A sum over `Γ` of a constant supported where `i` is sent to a given orbit member. -/
theorem sum_ite_smul_eq [DecidableEq J] (g : Γ) (i : J) (c : ℤ) :
    (∑ h : Γ, if ρ h • i = ρ g • i then c else 0) =
      c * ((Finset.univ.filter fun h : Γ => ρ h • i = i).card : ℤ) := by
  classical
  rw [← Finset.sum_filter, Finset.sum_const, card_filter_smul_eq, nsmul_eq_mul, mul_comm]

/-- Pairing bound: the pairing sum of `p` is at most `(2 + ⟨p, q^∨⟩)` times the stabilizer
order, when `q` is an orbit partner of `p`. -/
theorem sum_pairing_le_of_isOrbitPartner [Finite J] [DecidableEq J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q : J} (h : IsOrbitPartner P ρ p q) :
    ∑ g : Γ, P.pairing p (ρ g • p) ≤
      (2 + P.pairing p q) * ((Finset.univ.filter fun h : Γ => ρ h • p = p).card : ℤ) := by
  classical
  obtain ⟨⟨g₁, hg₁⟩, hqp, _⟩ := h
  have hb : ∀ g : Γ, P.pairing p (ρ g • p) ≤
      (if ρ g • p = ρ 1 • p then 2 else 0) + (if ρ g • p = ρ g₁ • p then P.pairing p q else 0) := by
    intro g
    rw [map_one, one_smul, hg₁]
    by_cases h1 : ρ g • p = p
    · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; exact hqp.symm), h1, pairing_same, add_zero]
    · by_cases h2 : ρ g • p = q
      · rw [ite_eq_right h1, ite_eq_left h2, h2, zero_add]
      · rw [ite_eq_right h1, ite_eq_right h2, add_zero]
        exact pairing_nonpos hne ⟨g, rfl⟩ (Ne.symm h1)
  refine (Finset.sum_le_sum fun g _ => hb g).trans (le_of_eq ?_)
  rw [Finset.sum_add_distrib, sum_ite_smul_eq, sum_ite_smul_eq, add_mul]

/-- An orbit partner pairs to exactly `-1`. -/
theorem IsOrbitPartner.pairing_eq_neg_one [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q : J} (h : IsOrbitPartner P ρ p q) : P.pairing p q = -1 := by
  classical
  have hpos := sum_pairing_smul_pos hne p
  have hle := sum_pairing_le_of_isOrbitPartner hne h
  have hneg := h.pairing_neg hne
  have hs : (0 : ℤ) ≤ ((Finset.univ.filter fun h : Γ => ρ h • p = p).card : ℤ) :=
    Nat.cast_nonneg _
  generalize ((Finset.univ.filter fun h : Γ => ρ h • p = p).card : ℤ) = s at hle hs
  have h2 : -2 < P.pairing p q := by
    by_contra! h'
    have : (2 + P.pairing p q) * s ≤ 0 :=
      mul_nonpos_of_nonpos_of_nonneg (by linarith) hs
    linarith
  lia

/-- **Uniqueness of orbit partners.** A root index has at most one orbit partner. -/
theorem IsOrbitPartner.unique [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q q' : J} (h : IsOrbitPartner P ρ p q) (h' : IsOrbitPartner P ρ p q') : q' = q := by
  classical
  by_contra hqq
  have hpos := sum_pairing_smul_pos hne p
  have e1 := h.pairing_eq_neg_one hne
  have e2 := h'.pairing_eq_neg_one hne
  obtain ⟨⟨g₁, hg₁⟩, hqp, _⟩ := h
  obtain ⟨⟨g₂, hg₂⟩, hqp', _⟩ := h'
  have hb : ∀ g : Γ, P.pairing p (ρ g • p) ≤
      (if ρ g • p = ρ 1 • p then 2 else 0) + (if ρ g • p = ρ g₁ • p then -1 else 0) +
        (if ρ g • p = ρ g₂ • p then -1 else 0) := by
    intro g
    rw [map_one, one_smul, hg₁, hg₂]
    by_cases h1 : ρ g • p = p
    · rw [ite_eq_left h1, ite_eq_right (by rw [h1]; exact hqp.symm), ite_eq_right (by rw [h1]; exact hqp'.symm),
        h1, pairing_same]
      norm_num
    · by_cases h2 : ρ g • p = q
      · rw [ite_eq_right h1, ite_eq_left h2, ite_eq_right (by rw [h2]; exact Ne.symm hqq), h2,
          e1]
        norm_num
      · by_cases h3 : ρ g • p = q'
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_left h3, h3, e2]
          norm_num
        · rw [ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]
          simpa using pairing_nonpos hne ⟨g, rfl⟩ (Ne.symm h1)
  have hle := Finset.sum_le_sum fun g (_ : g ∈ Finset.univ) => hb g
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, sum_ite_smul_eq, sum_ite_smul_eq,
    sum_ite_smul_eq] at hle
  linarith

omit [Fintype Γ] in
/-- Transport of orbit partners along the group action. -/
theorem IsOrbitPartner.smul {p q : J} (h : IsOrbitPartner P ρ p q) (g : Γ) :
    IsOrbitPartner P ρ (ρ g • p) (ρ g • q) := by
  obtain ⟨⟨g₁, hg₁⟩, hqp, ⟨m, hm⟩⟩ := h
  refine ⟨⟨g * g₁ * g⁻¹, ?_⟩, ?_, ⟨ρ g • m, ?_⟩⟩
  · rw [← hg₁, ← mul_smul, ← map_mul, inv_mul_cancel_right, map_mul, mul_smul]
  · intro hc
    exact hqp (smul_left_cancel _ hc)
  · rw [root_smul, root_smul, root_smul, hm, smul_add]

/-- The stabilizer of a root index fixes its orbit partner. -/
theorem IsOrbitPartner.smul_eq_of_smul_eq [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q : J} (h : IsOrbitPartner P ρ p q) {g : Γ} (hg : ρ g • p = p) : ρ g • q = q := by
  have h' := h.smul g
  rw [hg] at h'
  exact h.unique hne h'

/-- Every orbit partner relation is transported from a given one: if `q` is the partner of
`p` and `q₁` is the partner of `ρ g • p`, then `q₁ = ρ g • q`. -/
theorem IsOrbitPartner.eq_smul [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q q₁ : J} (h : IsOrbitPartner P ρ p q) (g : Γ) (h₁ : IsOrbitPartner P ρ (ρ g • p) q₁) :
    q₁ = ρ g • q :=
  (h.smul g).unique hne h₁

/-- Some element of `Γ` swaps a root index with its orbit partner. -/
theorem IsOrbitPartner.exists_swap [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q : J} (h : IsOrbitPartner P ρ p q) : ∃ g : Γ, ρ g • p = q ∧ ρ g • q = p := by
  obtain ⟨g, hg⟩ := h.1
  refine ⟨g, hg, ?_⟩
  have h' := h.smul g
  rw [hg] at h'
  exact h.symm.unique hne h'

/-- **Uniqueness of partner decompositions.** If the root of `m` is the sum of the roots of
two orbit partners `p, q`, and also of two orbit partners `p', q'` in the same orbit, then
`{p', q'} = {p, q}`. -/
theorem IsOrbitPartner.eq_or_eq_of_root_add_eq [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q p' q' : J} (h : IsOrbitPartner P ρ p q) (h' : IsOrbitPartner P ρ p' q')
    (hp' : ∃ g : Γ, ρ g • p = p') (hsum : P.root p + P.root q = P.root p' + P.root q') :
    (p' = p ∧ q' = q) ∨ (p' = q ∧ q' = p) := by
  obtain ⟨m, hm⟩ := h.2.2
  have hm' : P.root m = P.root p' + P.root q' := hm.trans hsum
  have hmp : P.pairing m p = 1 := by
    rw [pairing_eq_add_of_root_eq_add hm, pairing_same, h.symm.pairing_eq_neg_one hne]
    norm_num
  have hmp' : P.pairing m p = P.pairing p' p + P.pairing q' p :=
    pairing_eq_add_of_root_eq_add hm'
  have hpp' : ∃ g : Γ, ρ g • p' = p := by
    obtain ⟨g, hg⟩ := hp'
    refine ⟨g⁻¹, ?_⟩
    rw [← hg, ← mul_smul, ← map_mul, inv_mul_cancel, map_one, one_smul]
  have hqp' : ∃ g : Γ, ρ g • q' = p := by
    obtain ⟨g, hg⟩ := h'.symm.1
    obtain ⟨g', hg'⟩ := hpp'
    refine ⟨g' * g, ?_⟩
    rw [map_mul, mul_smul, hg, hg']
  by_cases h1 : p' = p
  · subst h1
    exact Or.inl ⟨rfl, P.root.injective (add_left_cancel hsum).symm⟩
  · by_cases h2 : q' = p
    · subst h2
      refine Or.inr ⟨P.root.injective ?_, rfl⟩
      have := hsum
      rw [add_comm (P.root p') (P.root q')] at this
      exact (add_left_cancel this).symm
    · exfalso
      have a1 := pairing_nonpos hne hpp' h1
      have a2 := pairing_nonpos hne hqp' h2
      lia

/-- The members of `Γ` fixing the sum of two orbit partners are exactly those fixing or
swapping the two partners. -/
theorem IsOrbitPartner.smul_eq_iff [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q m : J} (h : IsOrbitPartner P ρ p q) (hm : P.root m = P.root p + P.root q) (g : Γ) :
    ρ g • m = m ↔ (ρ g • p = p ∧ ρ g • q = q) ∨ (ρ g • p = q ∧ ρ g • q = p) := by
  have hgm : P.root (ρ g • m) = P.root (ρ g • p) + P.root (ρ g • q) := by
    rw [root_smul, root_smul, root_smul, hm, smul_add]
  constructor
  · intro hg
    rw [hg, hm] at hgm
    exact h.eq_or_eq_of_root_add_eq hne (h.smul g) ⟨g, rfl⟩ hgm
  · intro hg
    apply P.root.injective
    rw [hgm, hm]
    rcases hg with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, add_comm]

/-- The stabilizer of a root index fixes the sum of the root with its orbit partner. -/
theorem IsOrbitPartner.smul_eq_of_smul_eq_left [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q m : J} (h : IsOrbitPartner P ρ p q) (hm : P.root m = P.root p + P.root q) {g : Γ}
    (hg : ρ g • p = p) : ρ g • m = m :=
  (h.smul_eq_iff hne hm g).mpr (Or.inl ⟨hg, h.smul_eq_of_smul_eq hne hg⟩)

/-- Some element fixing the sum of two orbit partners moves the first partner. -/
theorem IsOrbitPartner.exists_smul_eq_ne [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q m : J} (h : IsOrbitPartner P ρ p q) (hm : P.root m = P.root p + P.root q) :
    ∃ g : Γ, ρ g • m = m ∧ ρ g • p ≠ p := by
  obtain ⟨g, hg1, hg2⟩ := h.exists_swap hne
  refine ⟨g, (h.smul_eq_iff hne hm g).mpr (Or.inr ⟨hg1, hg2⟩), ?_⟩
  rw [hg1]
  exact h.2.1

/-- Orbit sums are additive along actual root sums. -/
theorem orbitSum_eq_add_of_root_eq_add {m a b : J}
    (h : P.root m = P.root a + P.root b) :
    orbitSum P ρ m = orbitSum P ρ a + orbitSum P ρ b := by
  simp only [orbitSum_eq_sum_smul, h, smul_add, Finset.sum_add_distrib]

/-- The sum of two orbit partners has twice the orbit sum of either partner. -/
theorem IsOrbitPartner.orbitSum_eq {p q m : J} (h : IsOrbitPartner P ρ p q)
    (hm : P.root m = P.root p + P.root q) : orbitSum P ρ m = 2 • orbitSum P ρ p := by
  obtain ⟨g, hg⟩ := h.1
  rw [orbitSum_eq_add_of_root_eq_add hm, ← hg, orbitSum_smul, two_nsmul]

/-- **Existence of decompositions.** If no orbit sum vanishes, every root whose orbit sum is
twice the orbit sum of `p` is the sum of the root of a member of the orbit of `p` and a root
with the same orbit sum as `p`. -/
theorem exists_root_eq_add_of_orbitSum_eq_two_nsmul [Finite J]
    (hne : ∀ m, orbitSum P ρ m ≠ 0) {p m : J}
    (hm : orbitSum P ρ m = 2 • orbitSum P ρ p) :
    ∃ g : Γ, ∃ q : J, P.root m = P.root (ρ g • p) + P.root q ∧
      orbitSum P ρ q = orbitSum P ρ p := by
  have hsum : ∑ g : Γ, P.pairing m (ρ g • p) = 2 * ∑ g : Γ, P.pairing p (ρ g • p) := by
    rw [sum_pairing_smul_right, sum_pairing_smul_right, hm, map_nsmul, LinearMap.smul_apply,
      nsmul_eq_mul, Nat.cast_ofNat]
  have hpos : (∑ _g : Γ, (0 : ℤ)) < ∑ g : Γ, P.pairing m (ρ g • p) := by
    rw [hsum, Finset.sum_const_zero]
    have := sum_pairing_smul_pos hne p
    lia
  obtain ⟨g, -, hg⟩ := Finset.exists_lt_of_sum_lt hpos
  have hne' : m ≠ ρ g • p := by
    rintro rfl
    apply hne p
    have h2 := hm
    rw [orbitSum_smul, two_nsmul] at h2
    simpa using h2
  have hpos' : 0 < P.pairingIn ℤ m (ρ g • p) := by
    have h := P.algebraMap_pairingIn ℤ m (ρ g • p)
    simp only [Algebra.algebraMap_self_apply] at h
    rwa [h]
  obtain ⟨q, hq⟩ := P.root_sub_root_mem_of_pairingIn_pos hpos' hne'
  refine ⟨g, q, (eq_add_of_sub_eq' hq.symm), ?_⟩
  rw [orbitSum_eq_sub_of_root_eq_sub P ρ hq, orbitSum_smul, hm, two_nsmul, add_sub_cancel_right]

omit [Fintype Γ] in
/-- Under the reducedness condition that no root is twice a root, a member `q` of the orbit
of `p` whose root sum with `p` is a root is an orbit partner of `p`. -/
theorem isOrbitPartner_of_root_eq_add (hred : ∀ i, P.root i + P.root i ∉ Set.range P.root)
    {p q m : J} (hq : ∃ g : Γ, ρ g • p = q) (hm : P.root m = P.root p + P.root q) :
    IsOrbitPartner P ρ p q := by
  refine ⟨hq, ?_, ⟨m, hm⟩⟩
  rintro rfl
  exact hred q ⟨m, hm⟩

variable (P ρ) in
/-- The stabilizer in `Γ` of a root index. -/
def stabilizer (i : J) : Subgroup Γ :=
  (MulAction.stabilizer P.Aut i).comap ρ

omit [Fintype Γ] in
theorem mem_stabilizer_iff {i : J} {g : Γ} : g ∈ stabilizer P ρ i ↔ ρ g • i = i :=
  Iff.rfl

/-- The stabilizer of a root index lies in the stabilizer of the sum with its orbit
partner. -/
theorem IsOrbitPartner.stabilizer_le [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q m : J} (h : IsOrbitPartner P ρ p q) (hm : P.root m = P.root p + P.root q) :
    stabilizer P ρ p ≤ stabilizer P ρ m :=
  fun _ hg => h.smul_eq_of_smul_eq_left hne hm hg

/-- The stabilizer of a root index has index two in the stabilizer of the sum with its orbit
partner. -/
theorem IsOrbitPartner.relIndex_stabilizer [Finite J] (hne : ∀ m, orbitSum P ρ m ≠ 0)
    {p q m : J} (h : IsOrbitPartner P ρ p q) (hm : P.root m = P.root p + P.root q) :
    (stabilizer P ρ p).relIndex (stabilizer P ρ m) = 2 := by
  obtain ⟨s, hs1, hs2⟩ := h.exists_swap hne
  rw [Subgroup.relIndex_eq_two_iff]
  refine ⟨s, (h.smul_eq_iff hne hm s).mpr (Or.inr ⟨hs1, hs2⟩), fun b hb => ?_⟩
  rw [xor_iff_or_and_not_and, mem_stabilizer_iff, mem_stabilizer_iff, map_mul, mul_smul, hs1]
  rcases (h.smul_eq_iff hne hm b).mp hb with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h2, h1]
    exact ⟨Or.inr rfl, fun ha => h.2.1 ha.1⟩
  · rw [h2, h1]
    exact ⟨Or.inl rfl, fun ha => h.2.1 ha.2⟩

end OrbitPartner

end RootPairing

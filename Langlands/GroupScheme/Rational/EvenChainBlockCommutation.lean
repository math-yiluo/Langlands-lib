import Langlands.GroupScheme.Rational.OrthogonalSimpleRootCommutation
import Langlands.GroupScheme.Rational.EvenChainLocality

/-! # Blocks of distinct even paths commute -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.GroupScheme.SplitPinning

variable {k : Type u} [Field k]
    {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
    (p : SplitPinning G)

section Combinatorics

/-- An integral combination of simple roots with a positive and a negative coefficient is
neither zero nor a root. -/
theorem mixed_sum_ne_zero_not_root (d : p.base.support → ℤ) {s t : p.base.support}
    (hs : 0 < d s) (ht : d t < 0) :
    ∑ j, d j • p.rootDatum.root (j : p.rootIndex) ≠ 0 ∧
      ∑ j, d j • p.rootDatum.root (j : p.rootIndex) ∉ roots p.inclusion := by
  classical
  have hli : LinearIndependent ℤ (fun j : p.base.support => p.rootDatum.root j) :=
    p.base.linearIndepOn_root
  have hrange : Set.range (fun j : p.base.support => p.rootDatum.root j) =
      p.rootDatum.root '' (p.base.support : Set p.rootIndex) := by
    ext z
    simp
  constructor
  · intro h0
    have := Fintype.linearIndependent_iff.mp hli d h0 s
    omega
  · intro hr
    rw [← p.isRootDatum.2.1] at hr
    obtain ⟨i, hi⟩ := hr
    rcases p.base.root_mem_or_neg_mem i with h | h
    · rw [hi, ← hrange] at h
      obtain ⟨c, hc⟩ := AddSubmonoid.exists_of_mem_closure_range _ _ h
      have heq : ∑ j, ((c j : ℕ) : ℤ) • p.rootDatum.root (j : p.rootIndex) =
          ∑ j, d j • p.rootDatum.root (j : p.rootIndex) := by
        simp only [natCast_zsmul]
        exact hc.symm
      have := Fintype.linearIndependent_iffₛ.mp hli _ d heq t
      omega
    · rw [hi, ← hrange] at h
      obtain ⟨c, hc⟩ := AddSubmonoid.exists_of_mem_closure_range _ _ h
      have heq : ∑ j, ((c j : ℕ) : ℤ) • p.rootDatum.root (j : p.rootIndex) =
          ∑ j, (-d j) • p.rootDatum.root (j : p.rootIndex) := by
        simp only [natCast_zsmul, neg_smul, Finset.sum_neg_distrib]
        exact hc.symm
      have := Fintype.linearIndependent_iffₛ.mp hli _ _ heq s
      omega

variable {p}

/-- A nonzero nonnegative combination of two simple roots minus a nonzero nonnegative
combination of two other simple roots is neither zero nor a root. -/
theorem two_mixed_ne_zero_not_root {a b a' b' : p.base.support}
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (ha'b' : a' ≠ b') (n₁ n₂ m₁ m₂ : ℕ) (hn : 0 < n₁ + n₂) (hm : 0 < m₁ + m₂) :
    (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
        (m₁ • p.rootDatum.root (a' : p.rootIndex) + m₂ • p.rootDatum.root (b' : p.rootIndex))
        ≠ 0 ∧
      (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
        (m₁ • p.rootDatum.root (a' : p.rootIndex) + m₂ • p.rootDatum.root (b' : p.rootIndex))
        ∉ roots p.inclusion := by
  classical
  let d : p.base.support → ℤ := Pi.single a (n₁ : ℤ) + Pi.single b (n₂ : ℤ) -
    Pi.single a' (m₁ : ℤ) - Pi.single b' (m₂ : ℤ)
  have hd : ∑ j, d j • p.rootDatum.root (j : p.rootIndex) =
      (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
        (m₁ • p.rootDatum.root (a' : p.rootIndex) +
          m₂ • p.rootDatum.root (b' : p.rootIndex)) := by
    simp only [d, Pi.sub_apply, Pi.add_apply, sub_smul, add_smul, Finset.sum_sub_distrib,
      Finset.sum_add_distrib, Pi.single_apply, ite_smul, zero_smul, Finset.sum_ite_eq',
      Finset.mem_univ, ite_true, natCast_zsmul]
    abel
  have hda : d a = n₁ := by simp [d, hab, haa', hab']
  have hdb : d b = n₂ := by simp [d, hab.symm, hba', hbb']
  have hda' : d a' = -m₁ := by simp [d, haa'.symm, hba'.symm, ha'b']
  have hdb' : d b' = -m₂ := by simp [d, hab'.symm, hbb'.symm, ha'b'.symm]
  rw [← hd]
  obtain ⟨s, hs⟩ : ∃ s, 0 < d s := by
    rcases Nat.eq_zero_or_pos n₁ with h | h
    · exact ⟨b, by rw [hdb]; omega⟩
    · exact ⟨a, by rw [hda]; omega⟩
  obtain ⟨t, ht⟩ : ∃ t, d t < 0 := by
    rcases Nat.eq_zero_or_pos m₁ with h | h
    · exact ⟨b', by rw [hdb']; omega⟩
    · exact ⟨a', by rw [hda']; omega⟩
  exact p.mixed_sum_ne_zero_not_root d hs ht

/-- Applying a reflection does not change whether a character is zero or a root. -/
theorem ne_zero_not_root_of_reflection (i : p.rootIndex) {x : characterLattice p.torus}
    (h : p.rootDatum.reflection i x ≠ 0 ∧ p.rootDatum.reflection i x ∉ roots p.inclusion) :
    x ≠ 0 ∧ x ∉ roots p.inclusion := by
  refine ⟨fun hx => h.1 (by rw [hx, map_zero]), fun hx => h.2 ?_⟩
  rw [← p.isRootDatum.2.1] at hx ⊢
  exact p.rootDatum.mapsTo_reflection_root i hx

theorem neg_ne_zero_not_root {x : characterLattice p.torus}
    (h : x ≠ 0 ∧ x ∉ roots p.inclusion) : -x ≠ 0 ∧ -x ∉ roots p.inclusion := by
  refine ⟨neg_ne_zero.mpr h.1, ?_⟩
  rw [← p.isRootDatum.2.1, p.rootDatum.neg_mem_range_root_iff, p.isRootDatum.2.1]
  exact h.2

/-- A positive combination of two simple roots plus a positive multiple of a positive root of
an orthogonal `A₂` pair is neither zero nor a root. -/
theorem pos_add_ne_zero_not_root {a b a' b' : p.base.support}
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (ha'b' : a' ≠ b')
    (hoaa' : p.rootDatum.IsOrthogonal a a') (hoab' : p.rootDatum.IsOrthogonal a b')
    (hoba' : p.rootDatum.IsOrthogonal b a') (hobb' : p.rootDatum.IsOrthogonal b b')
    (hpair : p.rootDatum.pairing b' a' = -1)
    (n₁ n₂ m : ℕ) (hn : 0 < n₁ + n₂) (hm : 0 < m) (v : characterLattice p.torus)
    (hv : v = p.rootDatum.root a' ∨ v = p.rootDatum.root b' ∨
      v = p.rootDatum.root a' + p.rootDatum.root b') :
    (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) +
        m • v ≠ 0 ∧
      (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) +
        m • v ∉ roots p.inclusion := by
  have hmix := fun m₁ m₂ (hm' : 0 < m₁ + m₂) =>
    two_mixed_ne_zero_not_root (p := p) hab haa' hab' hba' hbb' ha'b' n₁ n₂ m₁ m₂ hn hm'
  have hra := p.rootDatum.reflection_apply_root (a' : p.rootIndex) (a : p.rootIndex)
  have hrb := p.rootDatum.reflection_apply_root (a' : p.rootIndex) (b : p.rootIndex)
  have hra₂ := p.rootDatum.reflection_apply_root (b' : p.rootIndex) (a : p.rootIndex)
  have hrb₂ := p.rootDatum.reflection_apply_root (b' : p.rootIndex) (b : p.rootIndex)
  have hrb' := p.rootDatum.reflection_apply_root (a' : p.rootIndex) (b' : p.rootIndex)
  rw [hoaa'.1, zero_smul, sub_zero] at hra
  rw [hoba'.1, zero_smul, sub_zero] at hrb
  rw [hoab'.1, zero_smul, sub_zero] at hra₂
  rw [hobb'.1, zero_smul, sub_zero] at hrb₂
  rw [hpair, neg_one_smul, sub_neg_eq_add] at hrb'
  have hsum : p.rootDatum.reflection (a' : p.rootIndex)
      (p.rootDatum.root (a' : p.rootIndex) + p.rootDatum.root (b' : p.rootIndex)) =
      p.rootDatum.root (b' : p.rootIndex) := by
    rw [map_add, p.rootDatum.reflection_apply_self, hrb']
    abel
  rcases hv with rfl | rfl | rfl
  · apply ne_zero_not_root_of_reflection (a' : p.rootIndex)
    have hcalc : p.rootDatum.reflection (a' : p.rootIndex)
        ((n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) +
          m • p.rootDatum.root (a' : p.rootIndex)) =
        (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
          (m • p.rootDatum.root (a' : p.rootIndex) +
            0 • p.rootDatum.root (b' : p.rootIndex)) := by
      simp only [map_add, map_nsmul, hra, hrb, p.rootDatum.reflection_apply_self, zero_smul,
        add_zero, smul_neg, sub_eq_add_neg]
    rw [hcalc]
    exact hmix m 0 (by omega)
  · apply ne_zero_not_root_of_reflection (b' : p.rootIndex)
    have hcalc : p.rootDatum.reflection (b' : p.rootIndex)
        ((n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) +
          m • p.rootDatum.root (b' : p.rootIndex)) =
        (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
          (0 • p.rootDatum.root (a' : p.rootIndex) +
            m • p.rootDatum.root (b' : p.rootIndex)) := by
      simp only [map_add, map_nsmul, hra₂, hrb₂, p.rootDatum.reflection_apply_self, zero_smul,
        zero_add, smul_neg, sub_eq_add_neg]
    rw [hcalc]
    exact hmix 0 m (by omega)
  · -- `s_{b'} s_{a'}` sends `a' + b'` to `-b'` and fixes `a`, `b`.
    apply ne_zero_not_root_of_reflection (a' : p.rootIndex)
    apply ne_zero_not_root_of_reflection (b' : p.rootIndex)
    have hcalc : p.rootDatum.reflection (b' : p.rootIndex)
        (p.rootDatum.reflection (a' : p.rootIndex)
        ((n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) +
          m • (p.rootDatum.root (a' : p.rootIndex) + p.rootDatum.root (b' : p.rootIndex)))) =
        (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
          (0 • p.rootDatum.root (a' : p.rootIndex) +
            m • p.rootDatum.root (b' : p.rootIndex)) := by
      rw [map_add (p.rootDatum.reflection (a' : p.rootIndex)), map_nsmul, hsum]
      simp only [map_add, map_nsmul, hra, hrb, hra₂, hrb₂, p.rootDatum.reflection_apply_self,
        zero_smul, zero_add, smul_neg, sub_eq_add_neg]
    rw [hcalc]
    exact hmix 0 m (by omega)

/-- A positive multiple of `a`, `b` or `a + b` is a nonnegative combination of `a` and `b`
with a positive coefficient. -/
theorem exists_nsmul_eq_of_pos {a b : p.base.support} {χ : characterLattice p.torus}
    (hχ : χ = p.rootDatum.root (a : p.rootIndex) ∨ χ = p.rootDatum.root (b : p.rootIndex) ∨
      χ = p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex))
    (n : ℕ) (hn : 0 < n) :
    ∃ n₁ n₂ : ℕ, 0 < n₁ + n₂ ∧
      n • χ = n₁ • p.rootDatum.root (a : p.rootIndex) +
        n₂ • p.rootDatum.root (b : p.rootIndex) := by
  rcases hχ with rfl | rfl | rfl
  · exact ⟨n, 0, by omega, by simp⟩
  · exact ⟨0, n, by omega, by simp⟩
  · exact ⟨n, n, by omega, smul_add _ _ _⟩

/-- Characters of the root subgroups attached to the middle pair `a, b` of a path: `a`, `b`
and `± (a + b)`. -/
def MiddleChar (a b : p.base.support) (χ : characterLattice p.torus) : Prop :=
  χ = p.rootDatum.root (a : p.rootIndex) ∨ χ = p.rootDatum.root (b : p.rootIndex) ∨
    χ = p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex) ∨
    χ = -(p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex))

/-- For two disjoint, mutually orthogonal pairs of simple roots `a, b` and `a', b'`, with
`⟨a', b'^∨⟩ = -1`, no positive combination of a middle character of the first pair with a
middle character of the second pair is zero or a root. -/
theorem middleChar_ne_zero_not_root {a b a' b' : p.base.support}
    (hab : a ≠ b) (haa' : a ≠ a') (hab' : a ≠ b') (hba' : b ≠ a') (hbb' : b ≠ b')
    (ha'b' : a' ≠ b')
    (hoaa' : p.rootDatum.IsOrthogonal a a') (hoab' : p.rootDatum.IsOrthogonal a b')
    (hoba' : p.rootDatum.IsOrthogonal b a') (hobb' : p.rootDatum.IsOrthogonal b b')
    (hpair : p.rootDatum.pairing b' a' = -1)
    {χ ψ : characterLattice p.torus} (hχ : MiddleChar a b χ) (hψ : MiddleChar a' b' ψ)
    (n m : ℕ) (hn : 0 < n) (hm : 0 < m) :
    n • χ + m • ψ ≠ 0 ∧ n • χ + m • ψ ∉ roots p.inclusion := by
  have hχ' : (χ = p.rootDatum.root (a : p.rootIndex) ∨
      χ = p.rootDatum.root (b : p.rootIndex) ∨
      χ = p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex)) ∨
      χ = -(p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex)) := by
    unfold MiddleChar at hχ
    tauto
  have hψ' : (ψ = p.rootDatum.root (a' : p.rootIndex) ∨
      ψ = p.rootDatum.root (b' : p.rootIndex) ∨
      ψ = p.rootDatum.root (a' : p.rootIndex) + p.rootDatum.root (b' : p.rootIndex)) ∨
      ψ = -(p.rootDatum.root (a' : p.rootIndex) + p.rootDatum.root (b' : p.rootIndex)) := by
    unfold MiddleChar at hψ
    tauto
  rcases hχ' with hχ | rfl <;> rcases hψ' with hψ | rfl
  · obtain ⟨n₁, n₂, hn', hχn⟩ := exists_nsmul_eq_of_pos hχ n hn
    rw [hχn]
    exact pos_add_ne_zero_not_root hab haa' hab' hba' hbb' ha'b' hoaa' hoab' hoba' hobb' hpair
      n₁ n₂ m hn' hm ψ hψ
  · obtain ⟨n₁, n₂, hn', hχn⟩ := exists_nsmul_eq_of_pos hχ n hn
    have h := two_mixed_ne_zero_not_root (p := p) hab haa' hab' hba' hbb' ha'b' n₁ n₂ m m hn'
      (by omega)
    have heq : n • χ + m • -(p.rootDatum.root (a' : p.rootIndex) +
        p.rootDatum.root (b' : p.rootIndex)) =
        (n₁ • p.rootDatum.root (a : p.rootIndex) + n₂ • p.rootDatum.root (b : p.rootIndex)) -
          (m • p.rootDatum.root (a' : p.rootIndex) +
            m • p.rootDatum.root (b' : p.rootIndex)) := by
      rw [hχn, smul_neg, smul_add, sub_eq_add_neg]
    rw [heq]
    exact h
  · obtain ⟨m₁, m₂, hm', hψm⟩ := exists_nsmul_eq_of_pos hψ m hm
    have h := two_mixed_ne_zero_not_root (p := p) ha'b' haa'.symm hba'.symm hab'.symm hbb'.symm
      hab m₁ m₂ n n hm' (by omega)
    have heq : n • -(p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex)) +
        m • ψ =
        (m₁ • p.rootDatum.root (a' : p.rootIndex) + m₂ • p.rootDatum.root (b' : p.rootIndex)) -
          (n • p.rootDatum.root (a : p.rootIndex) +
            n • p.rootDatum.root (b : p.rootIndex)) := by
      rw [hψm, smul_neg, smul_add]
      abel
    rw [heq]
    exact h
  · have h := pos_add_ne_zero_not_root hab haa' hab' hba' hbb' ha'b' hoaa' hoab' hoba' hobb'
      hpair n n m (by omega) hm _ (Or.inr (Or.inr rfl))
    have heq : n • -(p.rootDatum.root (a : p.rootIndex) + p.rootDatum.root (b : p.rootIndex)) +
        m • -(p.rootDatum.root (a' : p.rootIndex) + p.rootDatum.root (b' : p.rootIndex)) =
        -((n • p.rootDatum.root (a : p.rootIndex) + n • p.rootDatum.root (b : p.rootIndex)) +
          m • (p.rootDatum.root (a' : p.rootIndex) +
            p.rootDatum.root (b' : p.rootIndex))) := by
      rw [smul_neg, smul_neg, smul_add]
      abel
    rw [heq]
    exact neg_ne_zero_not_root h

end Combinatorics

section Groups

variable {p}

/-- The subgroup of rational points generated by the root subgroups of the two merged simple
roots `a`, `b` and of `± α`. It contains every block of the merged data. -/
abbrev SteinbergModifiedData.blockSubgroup (D : p.SteinbergModifiedData) :
    Subgroup (rationalPoints G) :=
  ((RelativeRoot.subgroup p.inclusion (p.rootDatum.root (D.a : p.rootIndex))).carrier
      (Over.mk (𝟙 _)) ⊔
    (RelativeRoot.subgroup p.inclusion (p.rootDatum.root (D.b : p.rootIndex))).carrier
      (Over.mk (𝟙 _))) ⊔
    p.rootSup D.alpha

theorem SteinbergModifiedData.middleChar_of_eq (D : p.SteinbergModifiedData)
    (χ : characterLattice p.torus)
    (hχ : χ = p.rootDatum.root (D.a : p.rootIndex) ∨ χ = p.rootDatum.root (D.b : p.rootIndex) ∨
      χ = p.rootDatum.root D.alpha ∨ χ = -p.rootDatum.root D.alpha) :
    MiddleChar D.a D.b χ := by
  rw [D.root_eq] at hχ
  exact hχ

theorem SteinbergModifiedData.middleChar_ne_zero (D : p.SteinbergModifiedData)
    {χ : characterLattice p.torus}
    (hχ : χ = p.rootDatum.root (D.a : p.rootIndex) ∨ χ = p.rootDatum.root (D.b : p.rootIndex) ∨
      χ = p.rootDatum.root D.alpha ∨ χ = -p.rootDatum.root D.alpha) :
    χ ≠ 0 := by
  rcases hχ with rfl | rfl | rfl | rfl
  · exact p.rootDatum.ne_zero _
  · exact p.rootDatum.ne_zero _
  · exact p.rootDatum.ne_zero _
  · exact neg_ne_zero.mpr (p.rootDatum.ne_zero _)

/-- The block subgroups of two merged data on disjoint, mutually orthogonal middle pairs
commute elementwise. -/
theorem SteinbergModifiedData.commute_of_mem_blockSubgroup {D D' : p.SteinbergModifiedData}
    (haa' : D.a ≠ D'.a) (hab' : D.a ≠ D'.b) (hba' : D.b ≠ D'.a) (hbb' : D.b ≠ D'.b)
    (hoaa' : p.rootDatum.IsOrthogonal D.a D'.a) (hoab' : p.rootDatum.IsOrthogonal D.a D'.b)
    (hoba' : p.rootDatum.IsOrthogonal D.b D'.a) (hobb' : p.rootDatum.IsOrthogonal D.b D'.b)
    (hpair' : p.rootDatum.pairing D'.b D'.a = -1)
    {g g' : rationalPoints G} (hg : g ∈ D.blockSubgroup) (hg' : g' ∈ D'.blockSubgroup) :
    Commute g g' := by
  have hchar : ∀ χ ψ : characterLattice p.torus,
      (χ = p.rootDatum.root (D.a : p.rootIndex) ∨ χ = p.rootDatum.root (D.b : p.rootIndex) ∨
        χ = p.rootDatum.root D.alpha ∨ χ = -p.rootDatum.root D.alpha) →
      (ψ = p.rootDatum.root (D'.a : p.rootIndex) ∨ ψ = p.rootDatum.root (D'.b : p.rootIndex) ∨
        ψ = p.rootDatum.root D'.alpha ∨ ψ = -p.rootDatum.root D'.alpha) →
      (RelativeRoot.subgroup p.inclusion χ).carrier (Over.mk (𝟙 _)) ≤
        Subgroup.centralizer ((RelativeRoot.subgroup p.inclusion ψ).carrier (Over.mk (𝟙 _))) := by
    intro χ ψ hχ hψ z hz w hw
    exact (p.commute_of_no_strict_root_combinations χ ψ (D.middleChar_ne_zero hχ)
      (D'.middleChar_ne_zero hψ)
      (fun n m hn hm => middleChar_ne_zero_not_root D.a_ne_b haa' hab' hba' hbb' D'.a_ne_b
        hoaa' hoab' hoba' hobb' hpair' (D.middleChar_of_eq χ hχ) (D'.middleChar_of_eq ψ hψ)
        n m hn hm) hz hw).symm.eq
  have hside : ∀ χ : characterLattice p.torus,
      (χ = p.rootDatum.root (D.a : p.rootIndex) ∨ χ = p.rootDatum.root (D.b : p.rootIndex) ∨
        χ = p.rootDatum.root D.alpha ∨ χ = -p.rootDatum.root D.alpha) →
      (RelativeRoot.subgroup p.inclusion χ).carrier (Over.mk (𝟙 _)) ≤
        Subgroup.centralizer (D'.blockSubgroup : Set (rationalPoints G)) := by
    intro χ hχ
    apply Subgroup.le_centralizer_iff.mpr
    exact sup_le
      (sup_le (Subgroup.le_centralizer_iff.mp (hchar χ _ hχ (Or.inl rfl)))
        (Subgroup.le_centralizer_iff.mp (hchar χ _ hχ (Or.inr (Or.inl rfl)))))
      (sup_le (Subgroup.le_centralizer_iff.mp (hchar χ _ hχ (Or.inr (Or.inr (Or.inl rfl)))))
        (Subgroup.le_centralizer_iff.mp (hchar χ _ hχ (Or.inr (Or.inr (Or.inr rfl))))))
  have htotal : D.blockSubgroup ≤
      Subgroup.centralizer (D'.blockSubgroup : Set (rationalPoints G)) :=
    sup_le (sup_le (hside _ (Or.inl rfl)) (hside _ (Or.inr (Or.inl rfl))))
      (sup_le (hside _ (Or.inr (Or.inr (Or.inl rfl))))
        (hside _ (Or.inr (Or.inr (Or.inr rfl)))))
  exact (htotal hg g' hg').symm

namespace EvenChainData

variable {J : Type u} (C : p.EvenChainData J) (x : p.NormalizedSimpleRootParametrizations)

/-- Every block of a path lies in the block subgroup of its merged data. -/
theorem block_mem (c : J) (b : Bool) (s : k) (t : kˣ) :
    C.block x c b s t ∈ (C.modified c).blockSubgroup := by
  unfold EvenChainData.block
  set D := C.modified c
  have hua : D.ua x ∈ D.blockSubgroup := Subgroup.mem_sup_left (Subgroup.mem_sup_left
    (((x D.a).toRootParametrization.mem_rootSubgroup_iff _ _).mpr ⟨_, rfl⟩))
  have hub : D.ub x ∈ D.blockSubgroup := Subgroup.mem_sup_left (Subgroup.mem_sup_right
    (((x D.b).toRootParametrization.mem_rootSubgroup_iff _ _).mpr ⟨_, rfl⟩))
  have hxα : D.xAlpha.rationalPoint s ∈ D.blockSubgroup := Subgroup.mem_sup_right
    (Subgroup.mem_sup_left ((D.xAlpha.mem_rootSubgroup_iff _ _).mpr ⟨_, rfl⟩))
  have hnα : D.nAlpha.point ∈ D.blockSubgroup := Subgroup.mem_sup_right (C.nAlpha_mem c)
  have hcor : corootRationalPoint p D.alpha t ∈ D.blockSubgroup :=
    Subgroup.mem_sup_right (corootRationalPoint_mem_rootSup _ t)
  split_ifs
  · exact mul_mem (mul_mem (mul_mem (mul_mem hub hua) hxα) hnα) hcor
  · exact mul_mem hxα hnα

theorem modified_a_mem (c : J) : ∃ i, (C.modified c).a = C.path c i := ⟨_, C.modified_a c⟩

theorem modified_b_mem (c : J) : ∃ i, (C.modified c).b = C.path c i := ⟨_, C.modified_b c⟩

theorem ne_of_mem_path {c c' : J} (hcc : c ≠ c') {z z' : p.base.support}
    (hz : ∃ i, z = C.path c i) (hz' : ∃ i, z' = C.path c' i) : z ≠ z' := by
  rintro rfl
  obtain ⟨i, hi⟩ := hz
  obtain ⟨i', hi'⟩ := hz'
  exact hcc (C.disjoint c c' i i' (hi.symm.trans hi'))

theorem isOrthogonal_of_mem_path {c c' : J} (hcc : c ≠ c') {z z' : p.base.support}
    (hz : ∃ i, z = C.path c i) (hz' : ∃ i, z' = C.path c' i) :
    p.rootDatum.IsOrthogonal z z' := by
  obtain ⟨i', rfl⟩ := hz'
  apply (C.isPathComponent c').isOrthogonal z _ i'
  rintro ⟨j, hj⟩
  obtain ⟨i, hi⟩ := hz
  exact hcc (C.disjoint c c' i j (hi.symm.trans hj.symm))

theorem pairing_modified_b_a (c : J) :
    p.rootDatum.pairing (C.modified c).b (C.modified c).a = -1 := by
  rw [← RootPairing.root_coroot_eq_pairing]
  exact C.pairing_b_a c

/-- Elements of the block subgroups of two distinct paths commute. -/
theorem commute_of_mem_blockSubgroup {c c' : J} (hcc : c ≠ c') {g g' : rationalPoints G}
    (hg : g ∈ (C.modified c).blockSubgroup) (hg' : g' ∈ (C.modified c').blockSubgroup) :
    Commute g g' :=
  SteinbergModifiedData.commute_of_mem_blockSubgroup
    (C.ne_of_mem_path hcc (C.modified_a_mem c) (C.modified_a_mem c'))
    (C.ne_of_mem_path hcc (C.modified_a_mem c) (C.modified_b_mem c'))
    (C.ne_of_mem_path hcc (C.modified_b_mem c) (C.modified_a_mem c'))
    (C.ne_of_mem_path hcc (C.modified_b_mem c) (C.modified_b_mem c'))
    (C.isOrthogonal_of_mem_path hcc (C.modified_a_mem c) (C.modified_a_mem c'))
    (C.isOrthogonal_of_mem_path hcc (C.modified_a_mem c) (C.modified_b_mem c'))
    (C.isOrthogonal_of_mem_path hcc (C.modified_b_mem c) (C.modified_a_mem c'))
    (C.isOrthogonal_of_mem_path hcc (C.modified_b_mem c) (C.modified_b_mem c'))
    (C.pairing_modified_b_a c') hg hg'

/-- Blocks of two distinct paths commute. -/
theorem commute_block {c c' : J} (hcc : c ≠ c') (b b' : Bool) (s s' : k) (t t' : kˣ) :
    Commute (C.block x c b s t) (C.block x c' b' s' t') :=
  C.commute_of_mem_blockSubgroup hcc (C.block_mem x c b s t) (C.block_mem x c' b' s' t')

end EvenChainData

end Groups


end Langlands.GroupScheme.SplitPinning

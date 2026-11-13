import Langlands.Geometry.Building.RealTorusInvariantForm
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.GroupScheme.Rational.ParabolicCorootLiftUniqueness
import Langlands.GroupScheme.Rational.PositiveRootInduction

/-! # Comparing two dominant real characters through a Weyl-invariant form -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct

namespace Langlands.GroupScheme

open RealTorusSpace Langlands.Aubert.General.RationalPointFamily

namespace RelativeRootReflectionData

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
  (D : RelativeRootReflectionData i)

/-- The supplied reflection of a relative root sends that root to its negative. -/
theorem fullRealAction_representative_root (α : relativeRoots i) :
    relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α))
      ((1 : ℝ) ⊗ₜ[ℤ] α.val) = -((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  rw [D.fullRealAction_representative, pair_tmul_tmul, D.pair_self]
  norm_num
  rw [two_smul]
  abel

section Form

variable [Fintype (relativeWeylGroup i)] (hT : IsSplitTorus T.toGrp)

/-- For the Weyl-invariant form, pairing with a relative root is the coroot
pairing times half the root's square length. -/
theorem two_mul_invariantForm_root (α : relativeRoots i) (x : Vstar T) :
    2 * relativeWeylInvariantForm i hT x ((1 : ℝ) ⊗ₜ[ℤ] α.val) =
      pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) *
        relativeWeylInvariantForm i hT ((1 : ℝ) ⊗ₜ[ℤ] α.val) ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have hinv := relativeWeylInvariantForm_invariant i hT
    (QuotientGroup.mk (D.representative α)) x ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  change relativeWeylInvariantForm i hT
      (relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α)) x)
      (relativeWeylFullRealAction i (QuotientGroup.mk (D.representative α))
        ((1 : ℝ) ⊗ₜ[ℤ] α.val)) = _ at hinv
  rw [D.fullRealAction_representative_root, D.fullRealAction_representative] at hinv
  simp only [map_neg, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply,
    smul_eq_mul, neg_sub] at hinv
  linarith

/-- A real character with nonnegative coroot pairing has nonnegative form pairing
with that root. -/
theorem invariantForm_root_nonneg (α : relativeRoots i) {y : Vstar T}
    (hy : 0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) :
    0 ≤ relativeWeylInvariantForm i hT y ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
  have h := D.two_mul_invariantForm_root hT α y
  have hαα := relativeWeylInvariantForm_nonneg i hT ((1 : ℝ) ⊗ₜ[ℤ] α.val)
  nlinarith [mul_nonneg hy hαα]

/-- A real character annihilating a coroot is orthogonal to the root. -/
theorem invariantForm_root_eq_zero (α : relativeRoots i) {y : Vstar T}
    (hy : pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0) :
    relativeWeylInvariantForm i hT y ((1 : ℝ) ⊗ₜ[ℤ] α.val) = 0 := by
  have h := D.two_mul_invariantForm_root hT α y
  rw [hy, zero_mul] at h
  linarith

variable (ν : cocharacterLattice T)

/-- A dominant real character has nonnegative form pairing with every positive
relative root. -/
theorem invariantForm_positiveRoot_nonneg {y : Vstar T}
    (hy : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    {β : characterLattice T} (hβ : β ∈ positiveRelativeRoots i ν) :
    0 ≤ relativeWeylInvariantForm i hT y ((1 : ℝ) ⊗ₜ[ℤ] β) := by
  refine positiveRelativeRoots_induction i ν
    (P := fun χ => 0 ≤ relativeWeylInvariantForm i hT y ((1 : ℝ) ⊗ₜ[ℤ] χ)) ?_ ?_ hβ
  · intro α hα
    exact D.invariantForm_root_nonneg hT ⟨α, hα.1.1⟩ (hy ⟨α, hα.1.1⟩ hα)
  · intro α _ γ _ hα hγ
    simp only [tmul_add, map_add]
    exact add_nonneg hα hγ

/-- For two dominant real characters `x, y` and any actual relative Weyl class `w`,
the form pairing of `y` with `w x` is at most its pairing with `x`. -/
theorem invariantForm_weyl_le [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) {x y : Vstar T}
    (hx : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hy : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (w : relativeWeylGroup i) :
    relativeWeylInvariantForm i hT y (relativeWeylFullRealAction i w x) ≤
      relativeWeylInvariantForm i hT y x := by
  obtain ⟨hW, _, C, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  have hfin := hT.finite_relativeRoots i
  have hs (α : Langlands.Aubert.General.RationalPointFamily.SimpleRoot i ν) :
      (QuotientGroup.mk (D.representative ⟨α.val, α.property.1.1⟩) :
        relativeWeylGroup i) = cs.simple α :=
    hcs.eq_simple_of_isRelativeReflection hT α
      (D.isRelativeReflection_representative hT hfin ⟨α.val, α.property.1.1⟩)
  suffices h : ∀ n (v : relativeWeylGroup i), cs.length v = n →
      0 ≤ relativeWeylInvariantForm i hT y (relativeWeylDisplacement v x) by
    have h' := h _ w rfl
    rw [relativeWeylDisplacement_apply, map_sub] at h'
    linarith
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    by_cases hv1 : v = 1
    · subst v
      simp [relativeWeylDisplacement]
    obtain ⟨α, hα⟩ := cs.exists_rightDescent_of_ne_one hv1
    change cs.length (v * cs.simple α) < cs.length v at hα
    let v' := v * cs.simple α
    have hv' : cs.length v' < n := by
      simpa only [v', ← hv] using hα
    have hv's : v' * cs.simple α = v := cs.simple_mul_simple_cancel_right α
    have hstep : cs.length v' < cs.length (v' * cs.simple α) := by
      rw [hv's, hv]
      exact hv'
    have hpos := (hcs.2.2.1 v' α).mp hstep
    have hroot : 0 ≤ relativeWeylInvariantForm i hT y
        (relativeWeylFullRealAction i v' ((1 : ℝ) ⊗ₜ[ℤ] α.val)) := by
      change 0 ≤ relativeWeylInvariantForm i hT y
        ((1 : ℝ) ⊗ₜ[ℤ] schemeWeylCharacterAction i v' α.val)
      exact D.invariantForm_positiveRoot_nonneg hT ν hy hpos
    have hsimple : relativeWeylDisplacement (cs.simple α) x =
        pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot ⟨α.val, α.property.1.1⟩) •
          ((1 : ℝ) ⊗ₜ[ℤ] α.val) := by
      rw [← hs α, relativeWeylDisplacement_apply, D.fullRealAction_representative]
      abel
    rw [← hv's, relativeWeylDisplacement_mul, hsimple, map_smul, map_add, map_smul,
      smul_eq_mul]
    exact add_nonneg (ih _ hv' v' rfl)
      (mul_nonneg (hx ⟨α.val, α.property.1.1⟩ α.property) hroot)

/-- One half of the comparison. Let `y₁, y₂` be dominant real characters, with `y₂`
annihilating the coroots of the selected set `J₂` of simple roots, and suppose the
kernel of restriction along `f₂` lies in the real span of `J₂`. If the restriction of
`w y₁` differs from that of `y₂` by an element of the restricted nonnegative root
cone of `(J₂, f₂)`, then `B(y₂, y₂) ≤ B(y₂, y₁)` for the Weyl-invariant form `B`. -/
theorem invariantForm_self_le_of_mem_restrictedRootNonnegCone [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hfin : (simpleRelativeRoots i ν).Finite)
    {A : CommGroupScheme (Spec (CommRingCat.of k))} (f : A ⟶ T)
    {J : Set (characterLattice T)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {x y : Vstar T}
    (hx : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T x ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hy : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hyJ : ∀ α : relativeRoots i, α.val ∈ J → pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hspan : ∀ z : Vstar T, rationalCharacterRestrictReal (CommGroupScheme.groupHom f) z = 0 →
      z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J))
    (w : relativeWeylGroup i)
    (hcone : rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
        (relativeWeylFullRealAction i w x) -
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f) y ∈
          restrictedRootNonnegCone i ν J f hfin) :
    relativeWeylInvariantForm i hT y y ≤ relativeWeylInvariantForm i hT y x := by
  classical
  let B := relativeWeylInvariantForm i hT
  let res := rationalCharacterRestrictReal (CommGroupScheme.groupHom f)
  let s : Finset (characterLattice T) := (hfin.subset Set.sdiff_subset : (simpleRelativeRoots i ν \ J).Finite).toFinset
  have hs : (↑s : Set (characterLattice T)) = simpleRelativeRoots i ν \ J :=
    Set.Finite.coe_toFinset _
  obtain ⟨c, hc, hsum⟩ := (mem_restrictedRootNonnegCone_iff_roots i ν J f hfin s hs).mp hcone
  let ĉ : Vstar T := ∑ α ∈ s, c α • ((1 : ℝ) ⊗ₜ[ℤ] α)
  have hresĉ : res ĉ = res (relativeWeylFullRealAction i w x) - res y := by
    rw [← hsum]
    simp only [ĉ, map_sum, map_smul]
    rfl
  let z : Vstar T := relativeWeylFullRealAction i w x - y - ĉ
  have hz : res z = 0 := by
    simp only [z, map_sub, hresĉ]
    abel
  have hzspan := hspan z hz
  have hBz : B y z = 0 := by
    have hle : Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J) ≤
        LinearMap.ker (B y) := by
      rw [Submodule.span_le]
      rintro _ ⟨α, hα, rfl⟩
      have hαs := hJ hα
      exact D.invariantForm_root_eq_zero hT ⟨α, hαs.1.1⟩ (hyJ ⟨α, hαs.1.1⟩ hα)
    exact hle hzspan
  have hBĉ : 0 ≤ B y ĉ := by
    simp only [ĉ, map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_nonneg fun α hα => ?_
    have hα' : α ∈ simpleRelativeRoots i ν \ J := by
      rw [← hs]
      exact hα
    exact mul_nonneg (hc α hα)
      (D.invariantForm_root_nonneg hT ⟨α, hα'.1.1.1⟩ (hy ⟨α, hα'.1.1.1⟩ hα'.1))
  have hweyl := D.invariantForm_weyl_le hT ν hG hi hν hx hy w
  have hdecomp : relativeWeylFullRealAction i w x = y + ĉ + z := by
    simp only [z]
    abel
  have hexp : B y (relativeWeylFullRealAction i w x) = B y y + B y ĉ + B y z := by
    rw [hdecomp, map_add, map_add]
  change B y y ≤ B y x
  linarith

omit [Fintype (relativeWeylGroup i)] in
/-- Renard's comparison of dominant exponents in VII.4.2 (ii), in its two-sided form:
if each of two dominant real characters `y₁, y₂`, annihilating the coroots of
`J₁, J₂` respectively, dominates a Weyl conjugate of the other modulo the restricted
nonnegative root cone of the other index, then `y₁ = y₂`. -/
theorem eq_of_mutual_mem_restrictedRootNonnegCone [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) (hfin : (simpleRelativeRoots i ν).Finite)
    {A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of k))} (f₁ : A₁ ⟶ T) (f₂ : A₂ ⟶ T)
    {J₁ J₂ : Set (characterLattice T)}
    (hJ₁ : J₁ ⊆ simpleRelativeRoots i ν) (hJ₂ : J₂ ⊆ simpleRelativeRoots i ν)
    {y₁ y₂ : Vstar T}
    (hy₁ : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T y₁ ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hy₂ : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν →
      0 ≤ pair T y₂ ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hy₁J : ∀ α : relativeRoots i, α.val ∈ J₁ → pair T y₁ ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hy₂J : ∀ α : relativeRoots i, α.val ∈ J₂ → pair T y₂ ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hspan₁ : ∀ z : Vstar T,
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₁) z = 0 →
        z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J₁))
    (hspan₂ : ∀ z : Vstar T,
      rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂) z = 0 →
        z ∈ Submodule.span ℝ ((fun α : characterLattice T => (1 : ℝ) ⊗ₜ[ℤ] α) '' J₂))
    (w₁ w₂ : relativeWeylGroup i)
    (h₁ : rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂)
        (relativeWeylFullRealAction i w₁ y₁) -
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f₂) y₂ ∈
          restrictedRootNonnegCone i ν J₂ f₂ hfin)
    (h₂ : rationalCharacterRestrictReal (CommGroupScheme.groupHom f₁)
        (relativeWeylFullRealAction i w₂ y₂) -
        rationalCharacterRestrictReal (CommGroupScheme.groupHom f₁) y₁ ∈
          restrictedRootNonnegCone i ν J₁ f₁ hfin) :
    y₁ = y₂ := by
  obtain ⟨hW, -⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  have hT : IsSplitTorus T.toGrp := hi.isSplitSubtorus.1
  have e₂ := D.invariantForm_self_le_of_mem_restrictedRootNonnegCone hT ν hG hi hν hfin f₂
    hJ₂ hy₁ hy₂ hy₂J hspan₂ w₁ h₁
  have e₁ := D.invariantForm_self_le_of_mem_restrictedRootNonnegCone hT ν hG hi hν hfin f₁
    hJ₁ hy₂ hy₁ hy₁J hspan₁ w₂ h₂
  have hsymm := relativeWeylInvariantForm_symm i hT y₁ y₂
  by_contra hne
  have hpos := relativeWeylInvariantForm_pos i hT (sub_ne_zero.mpr hne)
  simp only [map_sub, LinearMap.sub_apply] at hpos
  linarith

omit [Fintype (relativeWeylGroup i)] in
/-- The selected index of a dominant real character is determined by the character:
if `y` annihilates exactly the coroots of `J₁` among the simple coroots, and also
annihilates those of `J₂` while being positive off `J₂`, then `J₁ = J₂`. -/
theorem selected_eq_of_pair {J₁ J₂ : Set (characterLattice T)}
    (hJ₁ : J₁ ⊆ simpleRelativeRoots i ν) (hJ₂ : J₂ ⊆ simpleRelativeRoots i ν) {y : Vstar T}
    (hy₁J : ∀ α : relativeRoots i, α.val ∈ J₁ → pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hy₂J : ∀ α : relativeRoots i, α.val ∈ J₂ → pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α) = 0)
    (hy₁pos : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν → α.val ∉ J₁ →
      0 < pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α))
    (hy₂pos : ∀ α : relativeRoots i, α.val ∈ simpleRelativeRoots i ν → α.val ∉ J₂ →
      0 < pair T y ((1 : ℝ) ⊗ₜ[ℤ] D.coroot α)) :
    J₁ = J₂ := by
  ext α
  constructor
  · intro hα
    by_contra hα₂
    have h := hy₂pos ⟨α, (hJ₁ hα).1.1⟩ (hJ₁ hα) hα₂
    rw [hy₁J ⟨α, (hJ₁ hα).1.1⟩ hα] at h
    exact lt_irrefl _ h
  · intro hα
    by_contra hα₁
    have h := hy₁pos ⟨α, (hJ₂ hα).1.1⟩ (hJ₂ hα) hα₁
    rw [hy₂J ⟨α, (hJ₂ hα).1.1⟩ hα] at h
    exact lt_irrefl _ h

end Form

end RelativeRootReflectionData

end Langlands.GroupScheme

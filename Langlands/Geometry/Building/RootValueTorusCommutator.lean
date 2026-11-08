import Langlands.Geometry.Building.RootValueTorusRestriction
import Langlands.GroupScheme.Rational.TwoCharacterPositiveCocharacter
import Langlands.GroupTheory.GeneratedCommutator

/-! # Actual commutator bounds under restriction between split tori -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj commutatorElement
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

set_option backward.isDefEq.respectTransparency false

variable {k : Type u} [Field k]
  {S T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [IsAffineHom G.X.hom] [Mono i.hom.hom.left]
  {φ : RootFunctionFamily T G}

private abbrev RootFibreIndex (f : S ⟶ T) (a : characterLattice S) :=
  {x : characterLattice T × ℕ //
    x.1 ∈ relativeRoots i ∧ 0 < x.2 ∧ f ≫ x.1 = x.2 • a}

private abbrev MixedFibreIndex (f : S ⟶ T) (a b : characterLattice S) :=
  {x : characterLattice T × ℕ × ℕ //
    x.1 ∈ relativeRoots i ∧ 0 < x.2.1 ∧ 0 < x.2.2 ∧
      f ≫ x.1 = x.2.1 • a + x.2.2 • b}

/-- The actual upper filtrations whose restrictions are strictly positive
integral combinations of the two supplied lower characters. -/
def torusRestrictedMixedRootDepthSubgroup (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (a b : characterLattice S) (r s : ℝ) :
    Subgroup (rationalPoints G) :=
  ⨆ x : MixedFibreIndex (i := i) f a b,
    hφ.filtrationSubgroup x.val.1 (x.val.2.1 * r + x.val.2.2 * s)

private theorem rootDepth_eq_iSup (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T) (a : characterLattice S) (r : ℝ) :
    torusRestrictedRootDepthSubgroup hφ f a r =
      ⨆ x : RootFibreIndex (i := i) f a,
        hφ.filtrationSubgroup x.val.1 (x.val.2 * r) := by
  apply le_antisymm
  · refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
      iSup_le fun hm => iSup_le fun heq => ?_
    exact le_iSup (fun x : RootFibreIndex (i := i) f a =>
      hφ.filtrationSubgroup x.val.1 (x.val.2 * r)) ⟨⟨χ, m⟩, hχ, hm, heq⟩
  · refine iSup_le fun x => ?_
    exact le_iSup_of_le x.val.1 (le_iSup_of_le x.property.1
      (le_iSup_of_le x.val.2 (le_iSup_of_le x.property.2.1
        (le_iSup_of_le x.property.2.2 le_rfl))))

/-- Restriction preserves the pairing of a positive integral combination
with the transported cocharacter. -/
theorem latticePairing_comp_torusHom_of_restrict_eq_combination
    (f : S ⟶ T) (a b : characterLattice S) (ν : cocharacterLattice S)
    {χ : characterLattice T} {m n : ℕ}
    (hχ : f ≫ χ = m • a + n • b) :
    latticePairing T χ (ν ≫ f) =
      m • latticePairing S a ν + n • latticePairing S b ν := by
  rw [latticePairing_apply, Category.assoc, hχ]
  change latticePairing S (m • a + n • b) ν = _
  rw [map_add, map_nsmul, map_nsmul]
  rfl

private theorem pairing_pos_of_combination
    (f : S ⟶ T) (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    {χ : characterLattice T} {m n : ℕ} (hmn : 0 < m + n)
    (hχ : f ≫ χ = m • a + n • b) :
    0 < latticePairing T χ (ν ≫ f) := by
  rw [latticePairing_comp_torusHom_of_restrict_eq_combination f a b ν hχ,
    nsmul_eq_mul, nsmul_eq_mul]
  by_cases hm : m = 0
  · have hn : 0 < (n : ℤ) := by exact_mod_cast (by omega : 0 < n)
    simpa only [hm, Nat.cast_zero, zero_mul, zero_add] using mul_pos hn hb
  · have hm' : 0 < (m : ℤ) := by exact_mod_cast (Nat.pos_of_ne_zero hm)
    exact add_pos_of_pos_of_nonneg (mul_pos hm' ha)
      (mul_nonneg (Nat.cast_nonneg n) (le_of_lt hb))

private theorem pos_weighted_sum {p q m n : ℕ}
    (hp : 0 < p) (hq : 0 < q) (hmn : 0 < m + n) :
    0 < p * m + q * n := by
  by_cases hm : m = 0
  · have hn : 0 < n := by omega
    exact lt_of_lt_of_le (Nat.mul_pos hq hn) (Nat.le_add_left _ _)
  · exact lt_of_lt_of_le (Nat.mul_pos hp (Nat.pos_of_ne_zero hm))
      (Nat.le_add_right _ _)

/-- Upper V3 bounds commutators of any two nonzero positive-cone fibres
whose combined supports use both lower characters. -/
theorem filtrationSubgroup_commutator_le_torusRestrictedMixed
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    {χ θ : characterLattice T}
    (hχ : χ ∈ relativeRoots i) (hθ : θ ∈ relativeRoots i)
    {m n p q : ℕ}
    (hχres : f ≫ χ = m • a + n • b)
    (hθres : f ≫ θ = p • a + q • b)
    (hχpos : 0 < m + n) (hθpos : 0 < p + q)
    (hapos : 0 < m + p) (hbpos : 0 < n + q) (r s : ℝ) :
    ⁅hφ.filtrationSubgroup χ (m * r + n * s),
      hφ.filtrationSubgroup θ (p * r + q * s)⁆ ≤
      torusRestrictedMixedRootDepthSubgroup hφ f a b r s := by
  have hχν := pairing_pos_of_combination f a b ν ha hb hχpos hχres
  have hθν := pairing_pos_of_combination f a b ν ha hb hθpos hθres
  refine (hφ.filtrationSubgroup_commutator_le hχ hθ
    (KPApartmentData.positiveRoots_nonopposite (ν ≫ f) ⟨hχ, hχν⟩ ⟨hθ, hθν⟩)
    (m * r + n * s) (p * r + q * s)).trans ?_
  refine iSup_le fun v => iSup_le fun w => iSup_le fun hv =>
    iSup_le fun hw => iSup_le fun hroot => ?_
  have hres : f ≫ (v • χ + w • θ) =
      (v * m + w * p) • a + (v * n + w * q) • b := by
    simp only [Preadditive.comp_add, Preadditive.comp_nsmul, hχres, hθres,
      smul_add, smul_smul, add_smul]
    abel
  let hmem : MixedFibreIndex (i := i) f a b :=
    ⟨⟨v • χ + w • θ, v * m + w * p, v * n + w * q⟩,
      hroot, pos_weighted_sum hv hw hapos, pos_weighted_sum hv hw hbpos, hres⟩
  have hd : (v : ℝ) * (m * r + n * s) + w * (p * r + q * s) =
      (v * m + w * p : ℕ) * r + (v * n + w * q : ℕ) * s := by
    push_cast
    ring
  rw [hd]
  unfold torusRestrictedMixedRootDepthSubgroup
  exact le_iSup (fun x : MixedFibreIndex (i := i) f a b =>
    hφ.filtrationSubgroup x.val.1 (x.val.2.1 * r + x.val.2.2 * s)) hmem

/-- Every positive-cone upper filtration normalizes the strictly mixed target.
This includes each generator of either lower root filtration. -/
theorem filtrationSubgroup_le_normalizer_torusRestrictedMixed
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    {χ : characterLattice T} (hχ : χ ∈ relativeRoots i)
    {m n : ℕ} (hχres : f ≫ χ = m • a + n • b)
    (hχpos : 0 < m + n) (r s : ℝ) :
    hφ.filtrationSubgroup χ (m * r + n * s) ≤
      Subgroup.normalizer
        (torusRestrictedMixedRootDepthSubgroup hφ f a b r s : Set (rationalPoints G)) := by
  unfold torusRestrictedMixedRootDepthSubgroup
  apply Langlands.GroupTheory.le_normalizer_iSup_of_commutator_le
  intro x
  exact filtrationSubgroup_commutator_le_torusRestrictedMixed hφ f a b ν ha hb
    hχ x.property.1 hχres x.property.2.2.2 hχpos
    (by omega) (by omega) (by omega) r s

/-- Commutators of the two generated lower filtrations lie in the actual
mixed upper-filtration subgroup. -/
theorem torusRestrictedRootDepthSubgroup_commutator_le_mixed
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    (r s : ℝ) :
    ⁅torusRestrictedRootDepthSubgroup hφ f a r,
      torusRestrictedRootDepthSubgroup hφ f b s⁆ ≤
      torusRestrictedMixedRootDepthSubgroup hφ f a b r s := by
  rw [rootDepth_eq_iSup, rootDepth_eq_iSup]
  apply Langlands.GroupTheory.commutator_iSup_le_of_normalizes
  · intro x
    have hres : f ≫ x.val.1 = x.val.2 • a + 0 • b := by
      simpa only [zero_smul, add_zero] using x.property.2.2
    simpa only [Nat.cast_zero, zero_mul, add_zero] using
      filtrationSubgroup_le_normalizer_torusRestrictedMixed hφ f a b ν ha hb
        x.property.1 hres (by simpa only [add_zero] using x.property.2.1) r s
  · intro x
    have hres : f ≫ x.val.1 = 0 • a + x.val.2 • b := by
      simpa only [zero_smul, zero_add] using x.property.2.2
    simpa only [Nat.cast_zero, zero_mul, zero_add] using
      filtrationSubgroup_le_normalizer_torusRestrictedMixed hφ f a b ν ha hb
        x.property.1 hres (by simpa only [zero_add] using x.property.2.1) r s
  · intro x y
    have hx : f ≫ x.val.1 = x.val.2 • a + 0 • b := by
      simpa only [zero_smul, add_zero] using x.property.2.2
    have hy : f ≫ y.val.1 = 0 • a + y.val.2 • b := by
      simpa only [zero_smul, zero_add] using y.property.2.2
    simpa only [Nat.cast_zero, zero_mul, zero_add, add_zero] using
      filtrationSubgroup_commutator_le_torusRestrictedMixed hφ f a b ν ha hb
        x.property.1 y.property.1 hx hy
        (by simpa only [add_zero] using x.property.2.1)
        (by simpa only [zero_add] using y.property.2.1)
        (by simpa only [add_zero] using x.property.2.1)
        (by simpa only [zero_add] using y.property.2.1) r s

/-- Every mixed upper generator belongs to the canonical lower filtration
for its actual restricted root. -/
theorem torusRestrictedMixedRootDepthSubgroup_le
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    (r s : ℝ) :
    torusRestrictedMixedRootDepthSubgroup hφ f a b r s ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)),
        torusRestrictedRootDepthSubgroup hφ f (p • a + q • b) (p * r + q * s) := by
  refine iSup_le fun x => ?_
  have hpos := pairing_pos_of_combination (𝟙 S) a b ν ha hb
    (show 0 < x.val.2.1 + x.val.2.2 by omega)
    (show (𝟙 S) ≫ (x.val.2.1 • a + x.val.2.2 • b) =
      x.val.2.1 • a + x.val.2.2 • b by simp)
  have hnz : x.val.2.1 • a + x.val.2.2 • b ≠ 0 := by
    intro hz
    simp [hz] at hpos
  have hroot : x.val.2.1 • a + x.val.2.2 • b ∈
      relativeRoots (CommGroupScheme.groupHom f ≫ i) := by
    have h := (rootRestriction f i
      ⟨x.val.1, x.property.1, by rw [x.property.2.2.2]; exact hnz⟩).property
    simpa only [relativeRoots_eq_roots, rootRestriction_val, x.property.2.2.2] using h
  refine le_iSup_of_le x.val.2.1 (le_iSup_of_le x.val.2.2
    (le_iSup_of_le x.property.2.1 (le_iSup_of_le x.property.2.2.1
      (le_iSup_of_le hroot ?_))))
  unfold torusRestrictedRootDepthSubgroup
  refine le_iSup_of_le x.val.1 (le_iSup_of_le x.property.1
    (le_iSup_of_le 1 (le_iSup_of_le (by omega : 0 < (1 : ℕ))
      (le_iSup_of_le (by simpa only [one_smul] using x.property.2.2.2) ?_))))
  simp only [Nat.cast_one, one_mul]
  exact le_rfl

/-- Expanding each canonical lower mixed filtration gives upper mixed fibres,
with both coefficients multiplied by its positive restriction multiplier. -/
theorem iSup_torusRestrictedRootDepthSubgroup_le_mixed
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (r s : ℝ) :
    (⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
      (_ : p • a + q • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)),
      torusRestrictedRootDepthSubgroup hφ f (p • a + q • b) (p * r + q * s)) ≤
      torusRestrictedMixedRootDepthSubgroup hφ f a b r s := by
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
    iSup_le fun hq => iSup_le fun _ => ?_
  refine iSup_le fun χ => iSup_le fun hχ => iSup_le fun m =>
    iSup_le fun hm => iSup_le fun hres => ?_
  let x : MixedFibreIndex (i := i) f a b :=
    ⟨⟨χ, m * p, m * q⟩, hχ, Nat.mul_pos hm hp, Nat.mul_pos hm hq,
      by simpa only [smul_add, smul_smul] using hres⟩
  have hd : (m : ℝ) * (p * r + q * s) =
      (m * p : ℕ) * r + (m * q : ℕ) * s := by
    push_cast
    ring
  rw [hd]
  exact le_iSup (fun x : MixedFibreIndex (i := i) f a b =>
    hφ.filtrationSubgroup x.val.1 (x.val.2.1 * r + x.val.2.2 * s)) x

/-- A common positive cocharacter identifies the actual upper mixed target
with exactly the canonical filtrations on actual lower mixed roots. -/
theorem torusRestrictedMixedRootDepthSubgroup_eq_iSup
    (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a b : characterLattice S) (ν : cocharacterLattice S)
    (ha : 0 < latticePairing S a ν) (hb : 0 < latticePairing S b ν)
    (r s : ℝ) :
    torusRestrictedMixedRootDepthSubgroup hφ f a b r s =
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)),
        torusRestrictedRootDepthSubgroup hφ f (p • a + q • b) (p * r + q * s) :=
  le_antisymm (torusRestrictedMixedRootDepthSubgroup_le hφ f a b ν ha hb r s)
    (iSup_torusRestrictedRootDepthSubgroup_le_mixed hφ f a b r s)

/-- Full canonical subgroup V3 under restriction to a split torus.
The two lower roots need only lie outside opposite real rays. -/
theorem torusRestrictedRootDepthSubgroup_commutator_le
    (hS : IsSplitTorus S.toGrp) (hφ : IsRootDatumValuation i φ) (f : S ⟶ T)
    (a : characterLattice S) (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (b : characterLattice S) (hb : b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (hab : ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a))
    (r s : ℝ) :
    ⁅torusRestrictedRootDepthSubgroup hφ f a r,
      torusRestrictedRootDepthSubgroup hφ f b s⁆ ≤
      ⨆ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)),
        torusRestrictedRootDepthSubgroup hφ f (p • a + q • b) (p * r + q * s) := by
  obtain ⟨ν, haν, hbν⟩ :=
    hS.exists_cocharacter_pos_pair_of_not_opposite a b ha.1 hb.1 hab
  rw [← torusRestrictedMixedRootDepthSubgroup_eq_iSup hφ f a b ν haν hbν r s]
  exact torusRestrictedRootDepthSubgroup_commutator_le_mixed hφ f a b ν haν hbν r s

section ScalarV3

variable [Smooth G.X.hom]

/-- The actual restricted scalar family satisfies precisely axiom V3 of
IsRootDatumValuation, including all positive integral mixed-root factors. -/
theorem torusRestrictedRootFunctionFamily_commutator
    (hS : IsSplitTorus S.toGrp) (hT : IsSplitTorus T.toGrp)
    (hE : RelativeRoot.HasOppositeFactorPairs i) (hφ : IsRootDatumValuation i φ)
    (f : S ⟶ T)
    (a : characterLattice S) (ha : a ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (b : characterLattice S) (hb : b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i))
    (hab : ∀ t : ℝ, 0 < t →
      ((1 : ℝ) ⊗ₜ[ℤ] b : Vstar S) ≠ -(t • (1 : ℝ) ⊗ₜ[ℤ] a))
    (r s : ℝ) :
    ⁅Subgroup.closure (rootFiltration (CommGroupScheme.groupHom f ≫ i)
        (torusRestrictedRootFunctionFamily hS hT hE hφ f) a r),
      Subgroup.closure (rootFiltration (CommGroupScheme.groupHom f ≫ i)
        (torusRestrictedRootFunctionFamily hS hT hE hφ f) b s)⁆ ≤
      Subgroup.closure (⋃ (p : ℕ) (q : ℕ) (_ : 0 < p) (_ : 0 < q)
        (_ : p • a + q • b ∈ relativeRoots (CommGroupScheme.groupHom f ≫ i)),
        rootFiltration (CommGroupScheme.groupHom f ≫ i)
          (torusRestrictedRootFunctionFamily hS hT hE hφ f)
          (p • a + q • b) (p * r + q * s)) := by
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f a ha r,
    rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f b hb s,
    Subgroup.closure_eq, Subgroup.closure_eq]
  refine (torusRestrictedRootDepthSubgroup_commutator_le hS hφ f a ha b hb hab r s).trans ?_
  simp only [Subgroup.closure_iUnion]
  refine iSup_le fun p => iSup_le fun q => iSup_le fun hp =>
    iSup_le fun hq => iSup_le fun hroot => ?_
  refine le_iSup_of_le p (le_iSup_of_le q (le_iSup_of_le hp
    (le_iSup_of_le hq (le_iSup_of_le hroot ?_))))
  rw [rootFiltration_torusRestrictedRootFunctionFamily hS hT hE hφ f
    (p • a + q • b) hroot (p * r + q * s), Subgroup.closure_eq]

end ScalarV3

end Langlands.Geometry.Building

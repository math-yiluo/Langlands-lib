import Langlands.GroupScheme.Reductive.TitsIndexRelativeStatement
import Langlands.GroupScheme.Rational.FaceSimpleRootRestriction
import Langlands.GroupScheme.Rational.CharacterBaseChange
import Langlands.GroupScheme.Torus.WeilRestrictionNormOneCharacters
import Langlands.GroupScheme.Torus.LatticeGaloisContinuityProof
import Langlands.GroupScheme.Torus.LargestSplitGaloisFixed

/-! # Star invariance and relative simple roots of the actual Tits index -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.LinearAlgebra

namespace Langlands.GroupScheme.TitsIndexStarProof

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] (d : TitsIndexData G)

local notation "bK" => algebraBaseMap k (SeparableClosure k)

/-- The base change to the separable closure of the positive cocharacter,
viewed as a cocharacter of the extended torus of the pinning. -/
def nuK : cocharacterLattice
    ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus) :=
  cocharacterLattice.baseChange (algebraBaseMap k (SeparableClosure k)) d.pinning.torus
    (d.positiveCocharacter ≫ d.torusMap)

theorem baseChange_rootRestriction (i : d.pinning.rootIndex) :
    characterLattice.baseChange bK d.splitTorus (d.rootRestriction i) =
      (CommGroupScheme.baseChange bK).map d.torusMap ≫ d.pinning.rootDatum.root i := by
  unfold TitsIndexData.rootRestriction absoluteRootRestriction
  rw [← characterLattice.baseChangeEquiv_apply bK d.splitTorus d.maximalSplit.1.1,
    AddEquiv.apply_symm_apply]

theorem root'_nuK (i : d.pinning.rootIndex) :
    d.pinning.rootDatum.root' i (nuK d) =
      latticePairing d.splitTorus (d.rootRestriction i) d.positiveCocharacter := by
  change d.pinning.rootDatum.toLinearMap (d.pinning.rootDatum.root i) (nuK d) = _
  rw [d.pinning.isRootDatum.1, nuK, FaceSimpleRootRestriction.latticePairing_baseChange_comp,
    ← baseChange_rootRestriction, latticePairing_baseChange]

theorem mem_relativeRoots_of_ne_zero (i : d.pinning.rootIndex) (h : d.rootRestriction i ≠ 0) :
    d.rootRestriction i ∈ relativeRoots d.splitInclusion := by
  rw [← d.square]
  exact (mem_roots_iff_exists_splittingField_restriction d.maximalSplit.1.1
    d.pinning.isSplitTorus d.torusMap d.pinning.inclusion _).mpr
    ⟨h, d.pinning.rootDatum.root i, by rw [← d.pinning.isRootDatum.2.1]; exact ⟨i, rfl⟩,
      (baseChange_rootRestriction d i).symm⟩

theorem exists_of_mem_relativeRoots {α : characterLattice d.splitTorus}
    (hα : α ∈ relativeRoots d.splitInclusion) :
    ∃ i, d.rootRestriction i = α := by
  rw [← d.square] at hα
  obtain ⟨-, β, hβ, hβα⟩ := (mem_roots_iff_exists_splittingField_restriction
    d.maximalSplit.1.1 d.pinning.isSplitTorus d.torusMap d.pinning.inclusion α).mp hα
  rw [← d.pinning.isRootDatum.2.1] at hβ
  obtain ⟨i, rfl⟩ := hβ
  refine ⟨i, (d.maximalSplit.1.1.characterLattice_baseChange_bijective bK d.splitTorus).injective ?_⟩
  rw [baseChange_rootRestriction, hβα]

theorem rootRestriction_eq_zero_iff (i : d.pinning.rootIndex) :
    d.rootRestriction i = 0 ↔ d.pinning.rootDatum.root' i (nuK d) = 0 := by
  rw [root'_nuK]
  constructor
  · intro h
    rw [h, map_zero]
    rfl
  · intro h
    by_contra hne
    exact d.generic _ (mem_relativeRoots_of_ne_zero d i hne) h

theorem isPos_iff_of_ne_zero (i : d.pinning.rootIndex)
    (h : d.pinning.rootDatum.root' i (nuK d) ≠ 0) :
    d.pinning.base.IsPos i ↔ 0 < d.pinning.rootDatum.root' i (nuK d) := by
  rw [root'_nuK]
  exact d.compatible i (fun h0 => h ((rootRestriction_eq_zero_iff d i).mp h0))

theorem nonneg_of_isPos {i : d.pinning.rootIndex} (hi : d.pinning.base.IsPos i) :
    0 ≤ d.pinning.rootDatum.root' i (nuK d) := by
  by_cases h : d.pinning.rootDatum.root' i (nuK d) = 0
  · exact h.ge
  · exact ((isPos_iff_of_ne_zero d i h).mp hi).le

theorem isPos_of_pos {i : d.pinning.rootIndex}
    (hi : 0 < d.pinning.rootDatum.root' i (nuK d)) : d.pinning.base.IsPos i :=
  (isPos_iff_of_ne_zero d i hi.ne').mpr hi

theorem dominant : ∀ i ∈ d.pinning.base.support, 0 ≤ d.pinning.rootDatum.root' i (nuK d) :=
  fun _ hi => nonneg_of_isPos d (RootPairing.Base.isPos_of_mem_support hi)

theorem dominant' : ∀ i ∈ d.pinning.toSplitPinning.base.support,
    0 ≤ d.pinning.toSplitPinning.rootDatum.root' i (nuK d) :=
  dominant d

theorem coweightEquiv_nuK (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (d.pinning.galoisAction σ).coweightEquiv (nuK d) = nuK d := by
  change cocharacterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ⁻¹ _ = _
  exact cocharacterLattice.galoisRepresentation_baseChange k (SeparableClosure k) _ σ⁻¹ _

/-- The star automorphism is the ordinary Galois automorphism corrected by an
element of the reflection subgroup of the roots vanishing on `nuK d`. -/
theorem exists_star_correction (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    ∃ w ∈ RootDatumWeylChambers.reflectionSubgroup d.pinning.toSplitPinning.rootDatum
        {i | d.pinning.rootDatum.root' i (nuK d) = 0},
      (d.pinning.starAction σ).val = w * d.pinning.galoisAction σ := by
  classical
  let p := d.pinning.toSplitPinning
  let := Fintype.ofFinite p.rootIndex
  let := p.finite_rootDatum_weylGroup
  have hposc (i : d.pinning.rootIndex) :
      0 < p.rootDatum.root' i p.positiveCocharacter ↔ p.base.IsPos i := by
    change 0 < p.rootDatum.toLinearMap (p.rootDatum.root i) p.positiveCocharacter ↔ _
    rw [p.isRootDatum.1]
    exact p.latticePairing_root_positiveCocharacter_pos_iff i
  have hf (i : d.pinning.rootIndex) : p.rootDatum.root' i p.positiveCocharacter ≠ 0 := by
    change p.rootDatum.toLinearMap (p.rootDatum.root i) p.positiveCocharacter ≠ 0
    rw [p.isRootDatum.1]
    exact p.latticePairing_root_positiveCocharacter_ne_zero i
  have hface : ∀ i, p.rootDatum.root' i (nuK d) ≠ 0 →
      (0 < p.rootDatum.root' i p.positiveCocharacter ↔ 0 < p.rootDatum.root' i (nuK d)) := by
    intro i hi
    rw [hposc]
    exact isPos_iff_of_ne_zero d i hi
  obtain ⟨w, hpos, -⟩ := RootDatumBasedCorrection.exists_positive_correction p.rootDatum
    (nuK d) p.positiveCocharacter hf hface (d.pinning.galoisAction σ) (coweightEquiv_nuK d σ)
  have hb : w.val * d.pinning.galoisAction σ ∈ p.basedRootDatumAut := by
    intro i
    apply (p.base.mem_support_equiv_iff_of_isPos p.rootDatum
      (w.val * d.pinning.galoisAction σ).indexEquiv
      (w.val * d.pinning.galoisAction σ).weightEquiv
      (fun j => ((w.val * d.pinning.galoisAction σ).root_weightMap_apply p.rootDatum
        p.rootDatum j).symm) ?_ i).symm
    intro j
    rw [← hposc, ← hposc]
    exact (hpos j).symm
  have hθ : (⟨_, hb⟩ : p.basedRootDatumAut) = d.pinning.starAction σ := by
    apply p.basedRootDatum_representative_unique (d.pinning.galoisAction σ)
    · simpa only [mul_inv_cancel_right] using
        RootDatumWeylChambers.reflectionSubgroup_le p.rootDatum _ w.property
    · exact d.pinning.starAction_mul_galoisAction_inv_mem σ
  exact ⟨w.val, w.property, by rw [← hθ]⟩

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- A correction in the zero-root reflection subgroup of an automorphism fixing
a coweight preserves all root values on that coweight. -/
theorem root'_mul_eq {J M N : Type*} [AddCommGroup M] [AddCommGroup N]
    (P : RootDatum J M N) (ν : N) {w : P.Aut}
    (hw : w ∈ RootDatumWeylChambers.reflectionSubgroup P {i | P.root' i ν = 0})
    {δ : P.Aut} (hδ : δ.coweightEquiv ν = ν) (i : J) :
    P.root' ((w * δ).indexEquiv i) ν = P.root' i ν := by
  have h1 : w.coweightEquiv ν = ν := RootDatumBasedCorrection.fixes_coweight P ν ⟨w, hw⟩
  have hθ : (w * δ).coweightEquiv ν = ν := by
    change δ.coweightEquiv (w.coweightEquiv ν) = ν
    rw [h1, hδ]
  exact RootDatumBasedCorrection.root_evaluation_eq P _ _ hθ i

/-- The star automorphisms preserve the values of the roots on `nuK d`. -/
theorem star_root' (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (i : d.pinning.rootIndex) :
    d.pinning.toSplitPinning.rootDatum.root' ((d.pinning.starAction σ).val.indexEquiv i) (nuK d) =
      d.pinning.toSplitPinning.rootDatum.root' i (nuK d) := by
  obtain ⟨w, hw, h⟩ := exists_star_correction d σ
  rw [h]
  exact root'_mul_eq _ _ hw (coweightEquiv_nuK d σ) i

/-! ### Restriction to the split torus over the separable closure -/

/-- Restriction of characters of the extended torus to the extended split torus. -/
def resK : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus) →+
    characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.splitTorus) where
  toFun χ := (CommGroupScheme.baseChange bK).map d.torusMap ≫ χ
  map_zero' := Limits.comp_zero
  map_add' _ _ := Preadditive.comp_add _ _ _ _ _ _

theorem resK_apply (χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus)) :
    resK d χ = (CommGroupScheme.baseChange bK).map d.torusMap ≫ χ := rfl

theorem resK_root (i : d.pinning.rootIndex) :
    resK d (d.pinning.rootDatum.root i) =
      characterLattice.baseChange bK d.splitTorus (d.rootRestriction i) :=
  (baseChange_rootRestriction d i).symm

theorem resK_root_eq_zero (j : d.pinning.rootIndex)
    (hj : d.pinning.rootDatum.root' j (nuK d) = 0) :
    resK d (d.pinning.rootDatum.root j) = 0 := by
  rw [resK_root, (rootRestriction_eq_zero_iff d j).mpr hj, map_zero]

/-- Restriction to the split torus is invariant under the Galois action. -/
theorem resK_galois (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (χ : characterLattice
      ((CommGroupScheme.baseChange (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus)) :
    resK d (characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ χ) =
      resK d χ := by
  rw [resK_apply, resK_apply, ← characterLattice.galoisRepresentation_precompose]
  obtain ⟨c, hc⟩ := (d.maximalSplit.1.1.characterLattice_baseChange_bijective bK
    d.splitTorus).surjective ((CommGroupScheme.baseChange bK).map d.torusMap ≫ χ)
  rw [← hc, characterLattice.galoisRepresentation_baseChange]

omit [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] in
/-- An additive map killing the roots vanishing on `ν` is invariant under the
zero-root reflection subgroup. -/
theorem map_smul_eq_of_mem {J M N A : Type*} [AddCommGroup M] [AddCommGroup N]
    [AddCommGroup A] (P : RootDatum J M N) (ν : N) (r : M →+ A)
    (hr : ∀ j, P.root' j ν = 0 → r (P.root j) = 0) {w : P.Aut}
    (hw : w ∈ RootDatumWeylChambers.reflectionSubgroup P {i | P.root' i ν = 0}) :
    ∀ x, r (w • x) = r x := by
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    intro x
    rw [RootPairing.Equiv.reflection_smul, RootPairing.reflection_apply, map_sub, map_zsmul,
      hr j hj, smul_zero, sub_zero]
  | one => intro x; rw [one_smul]
  | mul a b _ _ ia ib => intro x; rw [mul_smul, ia, ib]
  | inv a _ ia =>
    intro x
    have h := ia (a⁻¹ • x)
    rw [smul_inv_smul] at h
    exact h.symm

/-- Restriction to the split torus is invariant under the star action on roots. -/
theorem resK_star (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) (i : d.pinning.rootIndex) :
    resK d (d.pinning.rootDatum.root ((d.pinning.starAction σ).val.indexEquiv i)) =
      resK d (d.pinning.rootDatum.root i) := by
  obtain ⟨w, hw, h⟩ := exists_star_correction d σ
  have h1 : d.pinning.toSplitPinning.rootDatum.root
      ((d.pinning.starAction σ).val.indexEquiv i) =
      w.weightEquiv ((d.pinning.galoisAction σ).weightEquiv
        (d.pinning.toSplitPinning.rootDatum.root i)) := by
    rw [RootPairing.Equiv.root_indexEquiv_eq_smul, h, mul_smul]
    rfl
  calc resK d (d.pinning.rootDatum.root ((d.pinning.starAction σ).val.indexEquiv i))
      = resK d (w.weightEquiv ((d.pinning.galoisAction σ).weightEquiv
          (d.pinning.toSplitPinning.rootDatum.root i))) := congrArg (resK d) h1
    _ = resK d ((d.pinning.galoisAction σ).weightEquiv
          (d.pinning.toSplitPinning.rootDatum.root i)) :=
        map_smul_eq_of_mem d.pinning.toSplitPinning.rootDatum (nuK d) (resK d)
          (resK_root_eq_zero d) hw _
    _ = resK d (characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ
          (d.pinning.rootDatum.root i)) := rfl
    _ = resK d (d.pinning.rootDatum.root i) := resK_galois d σ _

theorem rootRestriction_star (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k)
    (i : d.pinning.rootIndex) :
    d.rootRestriction ((d.pinning.starAction σ).val.indexEquiv i) = d.rootRestriction i := by
  apply (d.maximalSplit.1.1.characterLattice_baseChange_bijective bK d.splitTorus).injective
  rw [← resK_root, ← resK_root, resK_star]

/-! ### Simple indicator forms on the root span -/

section Forms

variable {J M N : Type*} [AddCommGroup M] [AddCommGroup N] {P : RootDatum J M N}

open RootDatumFaceHeight

open scoped Classical in
/-- The linear form on the root span sending a simple root to `1` if it lies in
`O` and to `0` otherwise. -/
def simpleForm (B : P.Base) (O : Set J) : P.rootSpan ℤ →ₗ[ℤ] ℤ :=
  B.toWeightBasisInt.constr ℤ fun i => if (i : J) ∈ O then 1 else 0

open scoped Classical in
theorem simpleForm_simple (B : P.Base) (O : Set J) (i : J) (hi : i ∈ B.support) :
    simpleForm B O (P.rootSpanMem ℤ i) = if i ∈ O then 1 else 0 := by
  have h : P.rootSpanMem ℤ i = B.toWeightBasisInt ⟨i, hi⟩ := by
    ext
    simp
  rw [h, simpleForm, Module.Basis.constr_basis]

open scoped Classical in
theorem simpleForm_eq_sum (B : P.Base) (O : Set J) (x : P.rootSpan ℤ) (f : J → ℤ)
    (hx : (x : M) = ∑ j ∈ B.support, f j • P.root j) :
    simpleForm B O x = ∑ j ∈ B.support, f j * if j ∈ O then 1 else 0 := by
  have hx' : x = ∑ j ∈ B.support, f j • P.rootSpanMem ℤ j := by
    ext
    simp [hx]
  rw [hx', map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [map_zsmul, simpleForm_simple B O j hj, smul_eq_mul]

open scoped Classical in
private theorem sum_indicator_eq_zero {B : P.Base} {ν : N} {O : Set J}
    (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (hO : ∀ i ∈ B.support, i ∈ O → P.root' i ν ≠ 0)
    (f : J → ℤ) (hf : ∀ i ∈ B.support, 0 ≤ f i)
    (hsum : ∑ i ∈ B.support, f i * P.root' i ν = 0) :
    ∑ i ∈ B.support, f i * (if i ∈ O then 1 else 0) = 0 := by
  have hterm := (Finset.sum_eq_zero_iff_of_nonneg
    (fun i hi => mul_nonneg (hf i hi) (hdom i hi))).mp hsum
  refine Finset.sum_eq_zero fun i hi => ?_
  by_cases h : i ∈ O
  · rcases mul_eq_zero.mp (hterm i hi) with h' | h'
    · simp [h']
    · exact absurd h' (hO i hi h)
  · simp [h]

/-- If `ν` is dominant and `O` avoids the simple roots vanishing on `ν`, the
indicator form of `O` vanishes on every root vanishing on `ν`. -/
theorem simpleForm_root_of_eq_zero {B : P.Base} {ν : N} {O : Set J}
    (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (hO : ∀ i ∈ B.support, i ∈ O → P.root' i ν ≠ 0)
    (j : J) (hj : P.root' j ν = 0) :
    simpleForm B O (P.rootSpanMem ℤ j) = 0 := by
  classical
  obtain ⟨f, -, hf | hf⟩ := B.exists_root_eq_sum_nat_or_neg j
  · have hz : P.root j = ∑ i ∈ B.support, (f i : ℤ) • P.root i := by
      simp [hf]
    rw [simpleForm_eq_sum B O _ _ hz]
    apply sum_indicator_eq_zero hdom hO _ (fun i _ => Int.natCast_nonneg _)
    rw [← root'_eq_sum B ν _ hz, hj]
  · have hz : P.root j = ∑ i ∈ B.support, (-(f i : ℤ)) • P.root i := by
      simp [hf, neg_smul, Finset.sum_neg_distrib]
    rw [simpleForm_eq_sum B O _ _ hz]
    have h := sum_indicator_eq_zero hdom hO (fun i => (f i : ℤ))
      (fun i _ => Int.natCast_nonneg _) (by
        have h' := root'_eq_sum B ν _ hz
        rw [hj] at h'
        simp only [neg_mul, Finset.sum_neg_distrib] at h'
        linarith)
    simp only [neg_mul, Finset.sum_neg_distrib, h, neg_zero]

/-- Under the same hypotheses, the indicator form is invariant under the
zero-root reflection subgroup. -/
theorem simpleForm_comp_rootSpanMap_of_mem {B : P.Base} {ν : N} {O : Set J}
    (hdom : ∀ i ∈ B.support, 0 ≤ P.root' i ν)
    (hO : ∀ i ∈ B.support, i ∈ O → P.root' i ν ≠ 0)
    {w : P.Aut} (hw : w ∈ RootDatumWeylChambers.reflectionSubgroup P {i | P.root' i ν = 0}) :
    (simpleForm B O).comp (rootSpanMap w) = simpleForm B O := by
  induction hw using Subgroup.closure_induction with
  | mem a ha =>
    obtain ⟨j, hj, rfl⟩ := ha
    ext x
    have hx : rootSpanMap (RootPairing.Equiv.reflection P j) x =
        x - (P.toLinearMap (x : M) (P.coroot j)) • P.rootSpanMem ℤ j := by
      ext
      simp [RootPairing.reflection_apply]
    simp only [LinearMap.comp_apply, hx, map_sub, map_zsmul,
      simpleForm_root_of_eq_zero hdom hO j hj, smul_zero, sub_zero]
  | one => rw [rootSpanMap_one, LinearMap.comp_id]
  | mul a b _ _ ha hb => rw [rootSpanMap_mul, ← LinearMap.comp_assoc, ha, hb]
  | inv a _ ha =>
    calc (simpleForm B O).comp (rootSpanMap a⁻¹)
        = ((simpleForm B O).comp (rootSpanMap a)).comp (rootSpanMap a⁻¹) := by rw [ha]
      _ = simpleForm B O := by
        rw [LinearMap.comp_assoc, ← rootSpanMap_mul, mul_inv_cancel, rootSpanMap_one,
          LinearMap.comp_id]

/-- A based automorphism preserving `O` preserves its indicator form. -/
theorem simpleForm_comp_rootSpanMap_of_based {B : P.Base} {O : Set J} {θ : P.Aut}
    (hθ : ∀ i ∈ B.support, θ.indexEquiv i ∈ B.support)
    (hO : ∀ i ∈ B.support, θ.indexEquiv i ∈ O ↔ i ∈ O) :
    (simpleForm B O).comp (rootSpanMap θ) = simpleForm B O := by
  classical
  apply B.toWeightBasisInt.ext
  intro i
  have hb : B.toWeightBasisInt i = P.rootSpanMem ℤ i := by
    ext
    simp
  rw [LinearMap.comp_apply, hb, rootSpanMap_rootSpanMem,
    simpleForm_simple B O _ (hθ i i.2), simpleForm_simple B O _ i.2]
  by_cases h : (i : J) ∈ O
  · simp [h, (hO i i.2).mpr h]
  · have h' : θ.indexEquiv i ∉ O := fun h' => h ((hO i i.2).mp h')
    simp [h, h']

/-- The face height is the indicator form of the simple roots not vanishing on `ν`. -/
theorem faceHeight_eq_simpleForm (B : P.Base) (ν : N) :
    faceHeight B ν = simpleForm B {i | P.root' i ν ≠ 0} := by
  classical
  apply B.toWeightBasisInt.ext
  intro i
  have hb : B.toWeightBasisInt i = P.rootSpanMem ℤ i := by
    ext
    simp
  rw [hb, faceHeight_simple B ν _ i.2, simpleForm_simple B _ _ i.2]
  by_cases h : P.root' i ν = 0 <;> simp [h]

end Forms

/-- A star-stable set of simple roots avoiding the zero-restriction vertices
defines a Galois-invariant indicator form. -/
theorem simpleForm_galois (O : Set d.pinning.toSplitPinning.rootIndex)
    (hO0 : ∀ i ∈ d.pinning.toSplitPinning.base.support, i ∈ O →
      d.pinning.toSplitPinning.rootDatum.root' i (nuK d) ≠ 0)
    (hOstar : ∀ (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
      ∀ i ∈ d.pinning.toSplitPinning.base.support,
        (d.pinning.starAction σ).val.indexEquiv i ∈ O ↔ i ∈ O)
    (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (simpleForm d.pinning.toSplitPinning.base O).comp
        (RootDatumFaceHeight.rootSpanMap (d.pinning.galoisAction σ)) =
      simpleForm d.pinning.toSplitPinning.base O := by
  obtain ⟨w, hw, h⟩ := exists_star_correction d σ
  have hg : d.pinning.galoisAction σ = w⁻¹ * (d.pinning.starAction σ).val := by
    rw [h, inv_mul_cancel_left]
  have h1 : (simpleForm d.pinning.toSplitPinning.base O).comp
      (RootDatumFaceHeight.rootSpanMap w⁻¹) = simpleForm d.pinning.toSplitPinning.base O :=
    simpleForm_comp_rootSpanMap_of_mem (dominant' d) hO0 (inv_mem hw)
  rw [hg, RootDatumFaceHeight.rootSpanMap_mul, ← LinearMap.comp_assoc, h1]
  exact simpleForm_comp_rootSpanMap_of_based
    (fun i hi => ((d.pinning.starAction σ).property i).mp hi) (hOstar σ)

/-! ### Galois-invariant forms vanish on zero-restriction root-span elements -/

/-- Let `h` be a linear form on the root span invariant under the Galois
action. Assuming Galois-fixed characters with zero split restriction vanish,
`h` vanishes on every root-span element with zero split restriction. The proof
sums over the finitely many cosets of an open subgroup acting trivially. -/
theorem form_eq_zero_of_resK_eq_zero
    (hfix : ∀ ψ : characterLattice ((CommGroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus),
      (∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ ψ = ψ) →
      resK d ψ = 0 → ψ = 0)
    (h : d.pinning.toSplitPinning.rootDatum.rootSpan ℤ →ₗ[ℤ] ℤ)
    (hh : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      h.comp (RootDatumFaceHeight.rootSpanMap (d.pinning.galoisAction σ)) = h)
    (x : d.pinning.toSplitPinning.rootDatum.rootSpan ℤ) (hx : resK d x.1 = 0) :
    h x = 0 := by
  classical
  obtain ⟨L, hL, hLtriv⟩ := torusLatticeGaloisContinuity k (SeparableClosure k)
    d.pinning.torus d.pinning.isSplitTorus
  have := hL
  let H : Subgroup (SeparableClosure k ≃ₐ[k] SeparableClosure k) := L.fixingSubgroup
  have : H.FiniteIndex := ⟨by
    rw [← IntermediateField.finrank_eq_fixingSubgroup_index]
    exact Module.finrank_pos.ne'⟩
  let := Fintype.ofFinite ((SeparableClosure k ≃ₐ[k] SeparableClosure k) ⧸ H)
  let ρ := characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus
  have hH (g : SeparableClosure k ≃ₐ[k] SeparableClosure k) (hg : g ∈ H) : ρ g = 1 :=
    (hLtriv g ((IntermediateField.mem_fixingSubgroup_iff L g).mp hg)).1
  set y : d.pinning.toSplitPinning.rootDatum.rootSpan ℤ :=
    ∑ q : (SeparableClosure k ≃ₐ[k] SeparableClosure k) ⧸ H,
      RootDatumFaceHeight.rootSpanMap (d.pinning.galoisAction q.out) x with hydef
  have hy : y.1 =
      ∑ q : (SeparableClosure k ≃ₐ[k] SeparableClosure k) ⧸ H, ρ q.out x.1 := by
    rw [hydef, Submodule.coe_sum]
    rfl
  have hyfix (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
      ρ σ y.1 = y.1 := by
    rw [hy, map_sum]
    have hq (q : (SeparableClosure k ≃ₐ[k] SeparableClosure k) ⧸ H) :
        ρ σ (ρ q.out x.1) = ρ (σ • q).out x.1 := by
      obtain ⟨g, hg⟩ := QuotientGroup.mk_out_eq_mul H (σ * q.out)
      have hmk : (QuotientGroup.mk (σ * q.out) :
          (SeparableClosure k ≃ₐ[k] SeparableClosure k) ⧸ H) = σ • q :=
        MulAction.Quotient.mk_smul_out H σ q
      rw [← hmk, hg, map_mul, hH g g.2, mul_one, map_mul, Module.End.mul_apply]
    simp only [hq]
    exact Fintype.sum_equiv (MulAction.toPerm σ) _ _ (fun q => rfl)
  have hyres : resK d y.1 = 0 := by
    rw [hy, map_sum]
    exact Finset.sum_eq_zero fun q _ => (resK_galois d q.out _).trans hx
  have hy0 : y = 0 := Subtype.ext (hfix _ hyfix hyres)
  have hterm (g : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
      h (RootDatumFaceHeight.rootSpanMap (d.pinning.galoisAction g) x) = h x :=
    LinearMap.congr_fun (hh g) x
  have hsum := congrArg h hy0
  rw [hydef, map_sum, map_zero] at hsum
  simp only [hterm, Finset.sum_const, Finset.card_univ] at hsum
  exact (smul_eq_zero.mp hsum).resolve_left Fintype.card_ne_zero

/-! ### Restrictions of distinguished simple roots -/

/-- The face height is invariant under the Galois action. -/
theorem faceHeight_comp_galois (σ : SeparableClosure k ≃ₐ[k] SeparableClosure k) :
    (RootDatumFaceHeight.faceHeight d.pinning.toSplitPinning.base (nuK d)).comp
        (RootDatumFaceHeight.rootSpanMap (d.pinning.galoisAction σ)) =
      RootDatumFaceHeight.faceHeight d.pinning.toSplitPinning.base (nuK d) := by
  rw [faceHeight_eq_simpleForm]
  exact simpleForm_galois d {i | d.pinning.toSplitPinning.rootDatum.root' i (nuK d) ≠ 0}
    (fun _ _ hi => hi) (fun τ i _ => by
      show d.pinning.toSplitPinning.rootDatum.root' _ (nuK d) ≠ 0 ↔
        d.pinning.toSplitPinning.rootDatum.root' i (nuK d) ≠ 0
      rw [star_root']) σ


section Fix

variable (hfix : ∀ ψ : characterLattice ((CommGroupScheme.baseChange
    (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus),
  (∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
    characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ ψ = ψ) →
  resK d ψ = 0 → ψ = 0)

include hfix

/-- A distinguished simple root restricts to a simple relative root. -/
theorem rootRestriction_mem_simpleRelativeRoots {a : d.pinning.rootIndex}
    (ha : a ∈ d.pinning.base.support) (hne : d.rootRestriction a ≠ 0) :
    d.rootRestriction a ∈ simpleRelativeRoots d.splitInclusion d.positiveCocharacter := by
  have hroot0 : d.pinning.rootDatum.root' a (nuK d) ≠ 0 :=
    fun h => hne ((rootRestriction_eq_zero_iff d a).mpr h)
  have hpos : 0 < d.pinning.rootDatum.root' a (nuK d) :=
    lt_of_le_of_ne (dominant d a ha) (Ne.symm hroot0)
  refine ⟨⟨mem_relativeRoots_of_ne_zero d a hne, by rw [← root'_nuK]; exact hpos⟩, ?_⟩
  rintro ⟨β, ⟨hβ, hβp⟩, γ, ⟨hγ, hγp⟩, hsum⟩
  obtain ⟨m₁, rfl⟩ := exists_of_mem_relativeRoots d hβ
  obtain ⟨m₂, rfl⟩ := exists_of_mem_relativeRoots d hγ
  rw [← root'_nuK] at hβp hγp
  have hdom : ∀ i ∈ d.pinning.toSplitPinning.base.support,
      0 ≤ d.pinning.toSplitPinning.rootDatum.root' i (nuK d) := dominant d
  have h₁ := RootDatumFaceHeight.one_le_faceHeight_root_of_pos hdom m₁ hβp
  have h₂ := RootDatumFaceHeight.one_le_faceHeight_root_of_pos hdom m₂ hγp
  have hah := RootDatumFaceHeight.faceHeight_simple d.pinning.toSplitPinning.base (nuK d) a ha
  have hroot0' : d.pinning.toSplitPinning.rootDatum.root' a (nuK d) ≠ 0 := hroot0
  simp only [hroot0', ↓reduceIte] at hah
  have hy := form_eq_zero_of_resK_eq_zero d hfix
    (RootDatumFaceHeight.faceHeight d.pinning.toSplitPinning.base (nuK d))
    (faceHeight_comp_galois d)
    (d.pinning.toSplitPinning.rootDatum.rootSpanMem ℤ a -
      d.pinning.toSplitPinning.rootDatum.rootSpanMem ℤ m₁ -
      d.pinning.toSplitPinning.rootDatum.rootSpanMem ℤ m₂) (by
      change resK d (d.pinning.rootDatum.root a - d.pinning.rootDatum.root m₁ -
        d.pinning.rootDatum.root m₂) = 0
      rw [map_sub, map_sub, resK_root, resK_root, resK_root, hsum, map_add]
      abel)
  rw [map_sub, map_sub, hah] at hy
  omega

/-- Distinguished simple vertices with equal restriction lie in one star orbit. -/
theorem exists_star_of_rootRestriction_eq (a b : d.Vertex) (ha : d.rootRestriction a.val ≠ 0)
    (hab : d.rootRestriction a.val = d.rootRestriction b.val) :
    ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a = b := by
  classical
  let O : Set d.pinning.toSplitPinning.rootIndex := {i | ∃ σ, (d.star σ a).val = i}
  have hO0 : ∀ i ∈ d.pinning.toSplitPinning.base.support, i ∈ O →
      d.pinning.toSplitPinning.rootDatum.root' i (nuK d) ≠ 0 := by
    rintro i - ⟨σ, rfl⟩
    rw [show (d.star σ a).val = (d.pinning.starAction σ).val.indexEquiv a.val from rfl,
      star_root']
    exact fun h => ha ((rootRestriction_eq_zero_iff d _).mpr h)
  have hOstar : ∀ (τ : SeparableClosure k ≃ₐ[k] SeparableClosure k),
      ∀ i ∈ d.pinning.toSplitPinning.base.support,
        (d.pinning.starAction τ).val.indexEquiv i ∈ O ↔ i ∈ O := by
    intro τ i hi
    have hiv : (d.pinning.starAction τ).val.indexEquiv i = (d.star τ ⟨i, hi⟩).val := rfl
    rw [hiv]
    constructor
    · rintro ⟨σ, hσ⟩
      refine ⟨τ⁻¹ * σ, ?_⟩
      rw [d.star_mul, show d.star σ a = d.star τ ⟨i, hi⟩ from Subtype.ext hσ, ← d.star_mul,
        inv_mul_cancel, d.star_one]
    · rintro ⟨σ, hσ⟩
      refine ⟨τ * σ, ?_⟩
      rw [d.star_mul, show d.star σ a = ⟨i, hi⟩ from Subtype.ext hσ]
  have hx := form_eq_zero_of_resK_eq_zero d hfix (simpleForm d.pinning.toSplitPinning.base O)
    (simpleForm_galois d O hO0 hOstar)
    (d.pinning.toSplitPinning.rootDatum.rootSpanMem ℤ a.val -
      d.pinning.toSplitPinning.rootDatum.rootSpanMem ℤ b.val) (by
      change resK d (d.pinning.rootDatum.root a.val - d.pinning.rootDatum.root b.val) = 0
      rw [map_sub, resK_root, resK_root, hab, sub_self])
  rw [map_sub, simpleForm_simple d.pinning.toSplitPinning.base O a.val a.2,
    simpleForm_simple d.pinning.toSplitPinning.base O b.val b.2] at hx
  have haO : a.val ∈ O := ⟨1, by rw [d.star_one]⟩
  simp only [haO, ↓reduceIte] at hx
  by_cases hbO : b.val ∈ O
  · obtain ⟨σ, hσ⟩ := hbO
    exact ⟨σ, Subtype.ext hσ⟩
  · simp [hbO] at hx

end Fix

/-- Every simple relative root is the restriction of a simple absolute root. -/
theorem exists_simple_of_mem_simpleRelativeRoots {α : characterLattice d.splitTorus}
    (hα : α ∈ simpleRelativeRoots d.splitInclusion d.positiveCocharacter) :
    ∃ a ∈ d.pinning.base.support, d.rootRestriction a = α := by
  obtain ⟨⟨hαrel, hαpos⟩, hαsimple⟩ := hα
  obtain ⟨m, rfl⟩ := exists_of_mem_relativeRoots d hαrel
  have hm : d.pinning.base.IsPos m := isPos_of_pos d (by rw [root'_nuK]; exact hαpos)
  have hpos_rel (i : d.pinning.rootIndex) (hi : d.pinning.base.IsPos i)
      (hi0 : d.rootRestriction i ≠ 0) :
      d.rootRestriction i ∈ positiveRelativeRoots d.splitInclusion d.positiveCocharacter := by
    have hr : d.pinning.rootDatum.root' i (nuK d) ≠ 0 :=
      fun h => hi0 ((rootRestriction_eq_zero_iff d i).mpr h)
    refine ⟨mem_relativeRoots_of_ne_zero d i hi0, ?_⟩
    rw [← root'_nuK]
    exact (isPos_iff_of_ne_zero d i hr).mp hi
  have key : ∀ j, d.pinning.base.IsPos j → d.rootRestriction j = d.rootRestriction m →
      ∃ a ∈ d.pinning.base.support, d.rootRestriction a = d.rootRestriction m := by
    intro j hj
    refine hj.induction_on_add (p := fun j => d.pinning.base.IsPos j →
      d.rootRestriction j = d.rootRestriction m →
        ∃ a ∈ d.pinning.base.support, d.rootRestriction a = d.rootRestriction m)
      (fun i hi _ hr => ⟨i, hi, hr⟩) ?_ hj
    intro i j' l hl hpi hj' hlpos hlr
    have hipos : d.pinning.base.IsPos i := hlpos.sub hj' (by rw [hl]; abel)
    have hrest : d.rootRestriction l = d.rootRestriction i + d.rootRestriction j' := by
      apply (d.maximalSplit.1.1.characterLattice_baseChange_bijective bK d.splitTorus).injective
      rw [map_add, ← resK_root, ← resK_root, ← resK_root, hl, map_add]
    by_cases hj0 : d.rootRestriction j' = 0
    · rw [hrest, hj0, add_zero] at hlr
      exact hpi hipos hlr
    by_cases hi0 : d.rootRestriction i = 0
    · rw [hrest, hi0, zero_add] at hlr
      exact ⟨j', hj', hlr⟩
    exfalso
    exact hαsimple ⟨_, hpos_rel i hipos hi0, _,
      hpos_rel j' (RootPairing.Base.isPos_of_mem_support hj') hj0, by rw [← hlr, hrest]⟩
  exact key m hm rfl

/-- The second conjunct for one index, assuming that Galois-fixed characters of
the extended torus with zero split restriction vanish. -/
theorem relativeSimpleRoots_of_fix
    (hfix : ∀ ψ : characterLattice ((CommGroupScheme.baseChange
        (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus),
      (∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
        characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ ψ = ψ) →
      resK d ψ = 0 → ψ = 0) :
    (∀ a b : d.distinguishedVertices,
      d.rootRestriction a.val.val = d.rootRestriction b.val.val ↔
        ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
          d.star σ a.val = b.val) ∧
    ∃ e : d.DistinguishedOrbit ≃
        simpleRelativeRoots d.splitInclusion d.positiveCocharacter,
      ∀ a : d.distinguishedVertices,
        (e (d.orbitClass a)).val = d.rootRestriction a.val.val := by
  have hiff : ∀ a b : d.distinguishedVertices,
      d.rootRestriction a.val.val = d.rootRestriction b.val.val ↔
        ∃ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k, d.star σ a.val = b.val := by
    intro a b
    constructor
    · exact exists_star_of_rootRestriction_eq d hfix a.val b.val a.2
    · rintro ⟨σ, hσ⟩
      rw [← hσ]
      exact (rootRestriction_star d σ a.val.val).symm
  refine ⟨hiff, ?_⟩
  let f : d.distinguishedVertices →
      simpleRelativeRoots d.splitInclusion d.positiveCocharacter := fun a =>
    ⟨d.rootRestriction a.val.val, rootRestriction_mem_simpleRelativeRoots d hfix a.val.2 a.2⟩
  let F : d.DistinguishedOrbit → simpleRelativeRoots d.splitInclusion d.positiveCocharacter :=
    Quotient.lift f (fun a b hab => Subtype.ext ((hiff a b).mpr hab))
  have hF : Function.Bijective F := by
    constructor
    · intro x y hxy
      induction x using Quotient.inductionOn with
      | h a =>
        induction y using Quotient.inductionOn with
        | h b => exact Quotient.sound ((hiff a b).mp (congrArg Subtype.val hxy))
    · rintro ⟨α, hα⟩
      obtain ⟨a, ha, hrest⟩ := exists_simple_of_mem_simpleRelativeRoots d hα
      have hne : d.rootRestriction a ≠ 0 := by
        rw [hrest]
        exact (mem_relativeRoots.mp hα.1.1).1
      exact ⟨d.orbitClass ⟨⟨a, ha⟩, hne⟩, Subtype.ext hrest⟩
  exact ⟨Equiv.ofBijective F hF, fun a => rfl⟩

/-- Galois-fixed characters of the extended torus with zero restriction to the
extended split torus vanish. -/
theorem fixed_eq_zero_of_resK_eq_zero (ψ : characterLattice ((CommGroupScheme.baseChange
      (algebraBaseMap k (SeparableClosure k))).obj d.pinning.torus))
    (hψ : ∀ σ : SeparableClosure k ≃ₐ[k] SeparableClosure k,
      characterLattice.galoisRepresentation k (SeparableClosure k) d.pinning.torus σ ψ = ψ)
    (hres : resK d ψ = 0) : ψ = 0 := by
  have : IsClosedImmersion d.pinning.inclusion.hom.hom.left := d.maximalTorus.2.1
  have : IsAffineHom d.pinning.torus.toGrp.X.hom := by
    rw [← Over.w d.pinning.inclusion.hom.hom]
    infer_instance
  have : LocallyOfFiniteType d.pinning.torus.toGrp.X.hom := by
    rw [← Over.w d.pinning.inclusion.hom.hom]
    infer_instance
  have : IsAffine d.pinning.torus.toGrp.X.left :=
    isAffine_of_isAffineHom d.pinning.torus.toGrp.X.hom
  have hmax : IsMaximalSplitTorus (CommGroupScheme.groupHom d.torusMap) :=
    IsMaximalSplitTorus.of_comp d.maximalTorus.2.1 (by rw [d.square]; exact d.maximalSplit)
  exact IsLargestSplitSubtorus.galoisFixed_character_eq_zero d.maximalTorus.1
    hmax.isLargestSplitSubtorus ψ hψ hres

end Langlands.GroupScheme.TitsIndexStarProof

namespace Langlands.GroupScheme

open TitsIndexStarProof in
/-- Zero-restriction vertices are invariant under every actual star automorphism. -/
theorem titsIndexStarInvariant : TitsIndexStarInvariantStatement.{u} := by
  intro k _ G _ _ d σ a
  change d.rootRestriction (d.star σ a).val = 0 ↔ d.rootRestriction a.val = 0
  rw [rootRestriction_eq_zero_iff, rootRestriction_eq_zero_iff]
  exact (star_root' d σ a.val).symm ▸ Iff.rfl

open TitsIndexStarProof in
/-- Restriction fibers of distinguished vertices are star orbits, and restriction
identifies distinguished star orbits with the actual simple relative roots. -/
theorem titsIndexRelativeSimpleRoots : TitsIndexRelativeSimpleRootsStatement.{u} :=
  fun _ _ _ _ _ d => relativeSimpleRoots_of_fix d (fixed_eq_zero_of_resK_eq_zero d)

/-- **Star invariance and relative simple roots of the actual Tits index.** -/
theorem titsIndexStarRelativeRoots : TitsIndexStarRelativeRootsStatement.{u} :=
  ⟨titsIndexStarInvariant, titsIndexRelativeSimpleRoots⟩

end Langlands.GroupScheme

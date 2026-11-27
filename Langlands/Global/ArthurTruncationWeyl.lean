import Langlands.Global.ArthurTruncationCutoffCovariance
import Langlands.GroupScheme.Rational.DominantWeylDisplacementRoots
import Langlands.GroupScheme.Rational.ParabolicWeylDisplacement
import Langlands.GroupScheme.Rational.RelativeFundamentalWeightProof
import Langlands.GroupScheme.Rational.LanglandsInvariantForm

/-! # Fundamental weights and regular Weyl displacement for Arthur truncation -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Classical

namespace Langlands.Global.ArthurTruncation.Idempotence

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
  Langlands.Aubert.General.RationalPointFamily Langlands.Group.RelativeWeylIndexing

variable {k : Type u} [Field k] {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {i : T.toGrp ⟶ G} [Mono i.hom.hom.left] {ν : cocharacterLattice T}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (D : RelativeRootReflectionData i)

/-- The full fundamental weights as elements of the real character space. -/
def fundamentalWeight (β : simpleRelativeRoots i ν) : Vstar T :=
  ((relativeFundamentalWeight k G hG T i hi ν hν D).2.1.choose β : relativeRootSpanReal i)

theorem isRealFundamentalWeight (β : simpleRelativeRoots i ν) :
    D.IsRealFundamentalWeight ν β (fundamentalWeight hG hi hν D β) :=
  (relativeFundamentalWeight k G hG T i hi ν hν D).2.1.choose_spec β

theorem pair_fundamentalWeight_coroot (β α : simpleRelativeRoots i ν) :
    pair T (fundamentalWeight hG hi hν D β) (D.realCoroot (simpleToRelativeRoot i ν α)) =
      if β = α then 1 else 0 := by
  have h := isRealFundamentalWeight hG hi hν D β
  rcases eq_or_ne β α with rfl | hne
  · simp only [↓reduceIte, h.2.1]
  · rw [ite_eq_right hne]
    exact h.2.2 α (Ne.symm hne)

omit [Mono i.hom.hom.left] in
private theorem pair_eq_zero_of_mem_centralDirections {x : Vstar T} {y : V T}
    (hx : x ∈ relativeRootSpanReal i) (hy : y ∈ relativeCentralDirections i) :
    pair T x y = 0 := by
  refine (Submodule.span_le.mpr ?_ :
      relativeRootSpanReal i ≤ ((pair T).flip y).ker) hx
  rintro _ ⟨a, ha, rfl⟩
  apply LinearMap.mem_ker.mpr
  rw [LinearMap.flip_apply, ← eval_eq_pair]
  exact (mem_relativeCentralDirections i y).mp hy a ha

/-- The full cutoff weight of the truncation formula is evaluation by the
corresponding real fundamental weight. -/
theorem pair_fundamentalWeight (β : simpleRelativeRoots i ν) (H : V T) :
    pair T (fundamentalWeight hG hi hν D β) H =
      ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1 H := by
  classical
  let x := fundamentalWeight hG hi hν D β
  let L := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.val
  have hspan : Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) ≤ (pair T x - L).ker := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨a, ha, rfl⟩
    let α : simpleRelativeRoots i ν := ⟨a.val, ha⟩
    have hα : simpleToRelativeRoot i ν α = a := Subtype.ext rfl
    apply LinearMap.mem_ker.mpr
    rw [LinearMap.sub_apply, sub_eq_zero]
    change pair T x (D.realCoroot a) =
      ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) β.1 (D.realCoroot a)
    rw [ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl β.2 a ha,
      ← hα, pair_fundamentalWeight_coroot hG hi hν D]
    exact if_congr (Subtype.ext_iff.trans (show β.val = α.val ↔ β.val = (simpleToRelativeRoot i ν α).val from
      Iff.rfl)) rfl rfl
  obtain ⟨Hc, hc, Hz, hz, h⟩ := Submodule.mem_sup.mp
    ((ArthurRelative.isCompl_corootSubspace_aSpace hG hi hν D Set.Subset.rfl).sup_eq_top ▸
      (Submodule.mem_top : H ∈ (⊤ : Submodule ℝ (V T))))
  have hHz : Hz ∈ relativeCentralDirections i := by
    rw [← ArthurRelative.aSpace_simpleRelativeRoots hG hi hν]
    exact hz
  have hc' := LinearMap.mem_ker.mp (hspan hc)
  rw [LinearMap.sub_apply, sub_eq_zero] at hc'
  have hz' := pair_eq_zero_of_mem_centralDirections (isRealFundamentalWeight hG hi hν D β).1 hHz
  have hL := ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator
    hG hi ν D (simpleRelativeRoots i ν) β.val hz
  change pair T x H = L H
  rw [← h, map_add, map_add, hc', hz', hL]

include hν in
/-- Evaluation of a real root-span character in the basis of full cutoff weights. -/
theorem pair_rootSpan_eq_sum_fullWeights [Fintype (SimpleRoot i ν)]
    {ξ : Vstar T} (hξ : ξ ∈ relativeRootSpanReal i) (H : V T) :
    pair T ξ H = ∑ a : SimpleRoot i ν,
      pair T ξ (D.realCoroot (simpleToRelativeRoot i ν a)) *
        ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.val H := by
  classical
  let c (a : SimpleRoot i ν) := pair T ξ (D.realCoroot (simpleToRelativeRoot i ν a))
  let W (a : SimpleRoot i ν) := ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) a.val
  let L : V T →ₗ[ℝ] ℝ := ∑ a, c a • W a
  have hL (y : V T) : L y = ∑ a, c a * W a y := by
    simp only [L, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have hc : Submodule.span ℝ (D.realCorootsOf (simpleRelativeRoots i ν)) ≤ (pair T ξ - L).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, ha, rfl⟩
    apply LinearMap.mem_ker.mpr
    rw [LinearMap.sub_apply, sub_eq_zero, hL]
    let a₀ : SimpleRoot i ν := ⟨a.val, ha⟩
    rw [Finset.sum_eq_single a₀]
    · change c a₀ = c a₀ * W a₀ (D.realCoroot a)
      rw [show W a₀ (D.realCoroot a) = 1 by
        rw [ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl a₀.2 a ha]
        simp [a₀], mul_one]
    · intro b _ hb
      change c b * ArthurRelative.weight hG hi ν D (simpleRelativeRoots i ν) b.val (D.realCoroot a) = 0
      rw [ArthurRelative.weight_coroot hG hi D hν Set.Subset.rfl b.2 a ha]
      have hne : b.val ≠ a.val := fun he => hb (Subtype.ext he)
      simp [hne]
    · simp
  obtain ⟨Hc, hc', Hz, hz, h⟩ := Submodule.mem_sup.mp
    ((ArthurRelative.isCompl_corootSubspace_aSpace hG hi hν D Set.Subset.rfl).sup_eq_top ▸
      (Submodule.mem_top : H ∈ (⊤ : Submodule ℝ (V T))))
  have hz' : Hz ∈ relativeCentralDirections i := by
    rw [← ArthurRelative.aSpace_simpleRelativeRoots hG hi hν]
    exact hz
  have hLH : L Hz = 0 := by
    rw [hL]
    apply Finset.sum_eq_zero
    intro a _
    exact mul_eq_zero_of_right _
      (ArthurRelative.weight_eq_zero_of_mem_rootAnnihilator hG hi ν D
        (simpleRelativeRoots i ν) a.val hz)
  have hch := LinearMap.mem_ker.mp (hc hc')
  rw [LinearMap.sub_apply, sub_eq_zero] at hch
  change pair T ξ H = ∑ a, c a * W a H
  rw [← hL, ← h, map_add, map_add, hch, pair_eq_zero_of_mem_centralDirections hξ hz', hLH]

private theorem fundamentalWeight_displacement_simple
    {M : CoxeterMatrix (SimpleRoot i ν)} (cs : CoxeterSystem M (relativeWeylGroup i))
    (hcs : IsRelativeWeylCoxeterRealization i ν cs) (β a : SimpleRoot i ν) :
    relativeWeylDisplacement (cs.simple a) (fundamentalWeight hG hi hν D β) =
      (if β = a then 1 else 0 : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] a.val) := by
  classical
  let := ArthurRelative.finite_relativeWeylGroup hG hi
  have hs : (QuotientGroup.mk (D.representative (simpleToRelativeRoot i ν a)) :
      relativeWeylGroup i) = cs.simple a :=
    hcs.eq_simple_of_isRelativeReflection hi.isSplitSubtorus.1 a
      (D.isRelativeReflection_representative hi.isSplitSubtorus.1
        (ArthurRelative.finite_relativeRoots hG hi) (simpleToRelativeRoot i ν a))
  rw [← hs, relativeWeylDisplacement_apply, D.fullRealAction_representative]
  change _ - (_ - pair T (fundamentalWeight hG hi hν D β)
    (D.realCoroot (simpleToRelativeRoot i ν a)) • ((1 : ℝ) ⊗ₜ[ℤ] a.val)) = _
  rw [pair_fundamentalWeight_coroot hG hi hν D]
  abel

/-- A full fundamental weight is fixed by the Weyl subgroup of its maximal parabolic. -/
theorem fundamentalWeight_fixed_of_mem_maximalWeyl (β : SimpleRoot i ν)
    {w : relativeWeylGroup i}
    (hw : w ∈ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {β.val})) :
    relativeWeylFullRealAction i w (fundamentalWeight hG hi hν D β) =
      fundamentalWeight hG hi hν D β := by
  classical
  obtain ⟨hW, hΔ, M, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  rw [DominantDisplacement.standardRelativeWeylGroup_complement_eq hcs β] at hw
  let x := fundamentalWeight hG hi hν D β
  refine DominantDisplacement.standardSubgroup_complement_induction (cs := cs) β
    (P := fun w => relativeWeylFullRealAction i w x = x) ?_ ?_ ?_ ?_ hw
  · intro a ha
    have h := fundamentalWeight_displacement_simple hG hi hν D cs hcs β a
    rw [relativeWeylDisplacement_apply, ite_eq_right (Ne.symm ha), zero_smul, sub_eq_zero] at h
    exact h.symm
  · rw [map_one]
    rfl
  · intro v w hv hw
    rw [map_mul, LinearEquiv.mul_apply, hw, hv]
  · intro v hv
    have he : (relativeWeylFullRealAction i v).symm (relativeWeylFullRealAction i v x) = x :=
      LinearEquiv.symm_apply_apply _ _
    rw [hv] at he
    rwa [map_inv]

omit [Mono i.hom.hom.left] in
private theorem rootCombination_nonneg_or_large (Cp : ℝ) (hC : 0 ≤ Cp)
    (H : V T) (hH : ∀ β ∈ simpleRelativeRoots i ν, Cp < eval T β H)
    {χ : characterLattice T} (hχ : χ ∈ AddSubmonoid.closure (simpleRelativeRoots i ν)) :
    χ = 0 ∨ Cp < eval T χ H := by
  induction hχ using AddSubmonoid.closure_induction with
  | mem a ha => exact Or.inr (hH a ha)
  | zero => exact Or.inl rfl
  | add a b _ _ ha hb =>
    rcases ha with rfl | ha
    · simpa only [zero_add] using hb
    rcases hb with rfl | hb
    · simpa only [add_zero] using Or.inr ha
    right
    rw [eval_eq_pair, tmul_add, map_add, LinearMap.add_apply, ← eval_eq_pair, ← eval_eq_pair]
    linarith

omit [Mono i.hom.hom.left] in
theorem eval_gt_of_positiveRelativeRoot (Cp : ℝ) (hC : 0 ≤ Cp) (H : V T)
    (hH : ∀ β ∈ simpleRelativeRoots i ν, Cp < eval T β H)
    {χ : characterLattice T} (hχ : χ ∈ positiveRelativeRoots i ν) :
    Cp < eval T χ H := by
  rcases rootCombination_nonneg_or_large Cp hC H hH
      (DominantDisplacement.positive_mem_closure hχ) with h | h
  · have h' := hχ.2
    rw [h, map_zero, LinearMap.zero_apply] at h'
    exact (lt_irrefl _ h').elim
  · exact h

/-- For a parameter with every simple-root value greater than `Cp ≥ 0`,
the fundamental-weight displacement has nonnegative value. Its value exceeds `Cp`
outside the Weyl group of the associated maximal parabolic. -/
theorem fundamentalWeight_displacement (β : simpleRelativeRoots i ν) (Tp : V T)
    (Cp : ℝ) (hC : 0 ≤ Cp) (hTp : ∀ a ∈ simpleRelativeRoots i ν, Cp < eval T a Tp)
    (w : relativeWeylGroup i) :
    let val := pair T (relativeWeylDisplacement w (fundamentalWeight hG hi hν D β)) Tp
    0 ≤ val ∧
      (w ∉ standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {β.1}) → Cp < val) := by
  classical
  obtain ⟨hW, hΔ, M, cs, hcs⟩ := relativeWeylCoxeter k G hG T i hi ν hν
  let : Fintype (SimpleRoot i ν) := Fintype.ofFinite _
  let x := fundamentalWeight hG hi hν D β
  let WJ := standardRelativeWeylGroup i ν (simpleRelativeRoots i ν \ {β.1})
  let f (v : relativeWeylGroup i) := pair T (relativeWeylDisplacement v x) Tp
  suffices h : ∀ n (v : relativeWeylGroup i), cs.length v = n →
      0 ≤ f v ∧ (v ∉ WJ → Cp < f v) from h _ w rfl
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro v hv
    by_cases hv1 : v = 1
    · subst v
      refine ⟨by simp [f], fun h => (h WJ.one_mem).elim⟩
    obtain ⟨a, ha⟩ := cs.exists_rightDescent_of_ne_one hv1
    let v' := v * cs.simple a
    have hv' : cs.length v' < n := by
      rw [← hv]
      exact ha
    have hv's : v' * cs.simple a = v := cs.simple_mul_simple_cancel_right a
    have hstep : cs.length v' < cs.length (v' * cs.simple a) := by rwa [hv's, hv]
    have hpos := (hcs.2.2.1 v' a).mp hstep
    have hsimple : relativeWeylDisplacement (cs.simple a) x =
        (if β = a then 1 else 0 : ℝ) • ((1 : ℝ) ⊗ₜ[ℤ] a.val) :=
      fundamentalWeight_displacement_simple hG hi hν D cs hcs β a
    have hval : f v = f v' + (if β = a then 1 else 0 : ℝ) *
        eval T (schemeWeylCharacterAction i v' a.val) Tp := by
      change pair T (relativeWeylDisplacement v x) Tp = _
      rw [← hv's, relativeWeylDisplacement_mul, hsimple]
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
        relativeWeylFullRealAction_tmul]
      rw [eval_eq_pair]
      rfl
    obtain ⟨hnonneg, hlarge⟩ := ih _ hv' v' rfl
    by_cases hβa : β = a
    · simp only [hβa, ↓reduceIte, one_mul] at hval
      have hroot := eval_gt_of_positiveRelativeRoot Cp hC Tp hTp hpos
      exact ⟨by linarith, fun _ => by linarith⟩
    · simp only [hβa, ↓reduceIte, zero_mul, add_zero] at hval
      refine ⟨hval.symm ▸ hnonneg, fun h ↦ hval.symm ▸ hlarge ?_⟩
      intro hw
      apply h
      rw [← hv's]
      refine WJ.mul_mem hw ?_
      rw [show WJ = standardSubgroup cs (DominantDisplacement.complementLabels β) from
        DominantDisplacement.standardRelativeWeylGroup_complement_eq hcs β]
      exact Subgroup.subset_closure
        ⟨a, DominantDisplacement.mem_complementLabels.mpr (Ne.symm hβa), rfl⟩

omit [IsAffineHom G.X.hom] in
private theorem fullAction_tmul_scheme (w : relativeWeylGroup i) (t : ℝ) (χ : characterLattice T) :
    relativeWeylFullRealAction i w (t ⊗ₜ[ℤ] χ) =
      t ⊗ₜ[ℤ] schemeWeylCharacterAction i w χ := by
  induction w using QuotientGroup.induction_on with
  | _ n => rfl

private theorem schemeAction_mem_roots (w : relativeWeylGroup i) {α : characterLattice T}
    (hα : α ∈ relativeRoots i) : schemeWeylCharacterAction i w α ∈ relativeRoots i := by
  induction w using QuotientGroup.induction_on with
  | _ n => exact weylAction_mapsTo_relativeRoots i n hα

/-- The real root span is invariant under the full Weyl action. -/
theorem fullAction_mem_rootSpan (w : relativeWeylGroup i)
    {x : Vstar T} (hx : x ∈ relativeRootSpanReal i) :
    relativeWeylFullRealAction i w x ∈ relativeRootSpanReal i := by
  induction hx using Submodule.span_induction with
  | mem root hr =>
    obtain ⟨α, hα, rfl⟩ := hr
    rw [fullAction_tmul_scheme]
    exact Submodule.subset_span ⟨_, schemeAction_mem_roots w hα, rfl⟩
  | zero => simp
  | add z y _ _ hz hy => simpa only [map_add] using Submodule.add_mem _ hz hy
  | smul t y _ hy => simpa only [map_smul] using Submodule.smul_mem _ t hy

/-- The coefficients of a translated fundamental weight in the fundamental
weight basis have the signs of the inverse-translated simple roots.
A positive inverse-translated root in the specified Levi gives zero
when the original fundamental weight is indexed outside that Levi. -/
theorem fundamentalWeight_weyl_coroot_sign (β α : simpleRelativeRoots i ν)
    (w : relativeWeylGroup i) {J : Set (characterLattice T)} {ζ : cocharacterLattice T}
    (hζ : IsStandardCocharacter i ν J ζ) (hβ : β.1 ∉ J) :
    let r := schemeWeylCharacterAction i w⁻¹ α.1
    let c := pair T (relativeWeylFullRealAction i w (fundamentalWeight hG hi hν D β))
      (D.realCoroot (simpleToRelativeRoot i ν α))
    (r ∈ positiveRelativeRoots i ν → 0 ≤ c) ∧ (r ∉ positiveRelativeRoots i ν → c ≤ 0) ∧
      (r ∈ positiveRelativeRoots i ν → latticePairing T r ζ = 0 → c = 0) := by
  let x := fundamentalWeight hG hi hν D β
  let r := schemeWeylCharacterAction i w⁻¹ α.1
  let A := simpleToRelativeRoot i ν α
  let c := pair T (relativeWeylFullRealAction i w x) (D.realCoroot A)
  let := ArthurRelative.finite_relativeWeylGroup hG hi
  let : Fintype (relativeWeylGroup i) := Fintype.ofFinite _
  let B := relativeWeylInvariantForm i hi.isSplitSubtorus.1
  have hB : IsWeylInvariantInnerProduct i B :=
    ⟨relativeWeylInvariantForm_symm i hi.isSplitSubtorus.1,
      fun _ => relativeWeylInvariantForm_pos i hi.isSplitSubtorus.1,
      relativeWeylInvariantForm_invariant i hi.isSplitSubtorus.1⟩
  let L (χ : characterLattice T) := B x ((1 : ℝ) ⊗ₜ[ℤ] χ)
  have hsum (s : Set (characterLattice T)) (h : ∀ χ ∈ s, 0 ≤ L χ) :
      ∀ χ ∈ AddSubmonoid.closure s, 0 ≤ L χ := by
    intro χ hχ
    induction hχ using AddSubmonoid.closure_induction with
    | mem a ha => exact h a ha
    | zero => simp [L]
    | add a b _ _ ha hb => simpa only [L, tmul_add, map_add] using add_nonneg ha hb
  have hlarge (a : characterLattice T) (ha : a ∈ simpleRelativeRoots i ν) : 0 ≤ L a := by
    let a' : simpleRelativeRoots i ν := ⟨a, ha⟩
    change 0 ≤ B x ((1 : ℝ) ⊗ₜ[ℤ] (simpleToRelativeRoot i ν a').val)
    apply (D.coroot_nonneg_iff i B hB _ _).mp
    change 0 ≤ pair T x (D.realCoroot (simpleToRelativeRoot i ν a'))
    rw [show x = fundamentalWeight hG hi hν D β from rfl,
      pair_fundamentalWeight_coroot hG hi hν D]
    split <;> norm_num
  have hzero (χ : characterLattice T) (hχ : χ ∈ AddSubmonoid.closure J)
      (hJ : J ⊆ simpleRelativeRoots i ν) : L χ = 0 := by
    induction hχ using AddSubmonoid.closure_induction with
    | mem a ha =>
      let a' : simpleRelativeRoots i ν := ⟨a, hJ ha⟩
      have hne : β ≠ a' := fun h => hβ ((congrArg Subtype.val h).symm ▸ ha)
      change B x ((1 : ℝ) ⊗ₜ[ℤ] (simpleToRelativeRoot i ν a').val) = 0
      apply (D.coroot_eq_zero_iff i B hB _ _).mp
      exact (isRealFundamentalWeight hG hi hν D β).2.2 a' (Ne.symm hne)
    | zero => simp [L]
    | add a b _ _ ha hb => simp only [L, tmul_add, map_add, ha, hb, add_zero]
  have hform : B (relativeWeylFullRealAction i w x) ((1 : ℝ) ⊗ₜ[ℤ] A.val) = L r := by
    have h := hB.2.2 w x (relativeWeylFullRealAction i w⁻¹ ((1 : ℝ) ⊗ₜ[ℤ] A.val))
    rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one, fullAction_tmul_scheme] at h
    simpa only [LinearEquiv.coe_one, id_eq] using h
  change (r ∈ positiveRelativeRoots i ν → 0 ≤ c) ∧ (r ∉ positiveRelativeRoots i ν → c ≤ 0) ∧
    (r ∈ positiveRelativeRoots i ν → latticePairing T r ζ = 0 → c = 0)
  refine ⟨?_, ?_, ?_⟩
  · intro hr
    change 0 ≤ pair T (relativeWeylFullRealAction i w x) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot A)
    rw [D.coroot_nonneg_iff i B hB, hform]
    exact hsum _ hlarge _ (DominantDisplacement.positive_mem_closure hr)
  · intro hnr
    have hr := schemeAction_mem_roots w⁻¹ (simpleRelativeRoots_subset_relativeRoots i ν α.2)
    have hneg : 0 < latticePairing T (-r) ν := by
      have hn : ¬ 0 < latticePairing T r ν := fun h => hnr ⟨hr, h⟩
      have hz : latticePairing T r ν ≠ 0 := hν r hr
      rw [map_neg, LinearMap.neg_apply]
      omega
    have hnr' : -r ∈ positiveRelativeRoots i ν := ⟨D.neg_mem_relativeRoots i hr, hneg⟩
    have hn := hsum _ hlarge _ (DominantDisplacement.positive_mem_closure hnr')
    have hLneg : L (-r) = -L r := by simp [L, tmul_neg]
    rw [hLneg] at hn
    have hnegL : L r ≤ 0 := by linarith
    change pair T (relativeWeylFullRealAction i w x) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot A) ≤ 0
    rw [D.coroot_formula i B hB, hform]
    apply div_nonpos_of_nonpos_of_nonneg (by linarith) (hB.2.1 _ (D.one_tmul_ne_zero i A)).le
  · intro hr hp
    change pair T (relativeWeylFullRealAction i w x) ((1 : ℝ) ⊗ₜ[ℤ] D.coroot A) = 0
    rw [D.coroot_eq_zero_iff i B hB, hform]
    exact hzero r ((hζ.pairing_eq_zero_iff_mem_closure i ν hr).mp hp) hζ.1

end Langlands.Global.ArthurTruncation.Idempotence

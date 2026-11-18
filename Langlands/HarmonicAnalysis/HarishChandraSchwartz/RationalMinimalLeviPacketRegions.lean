import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalMinimalLeviHeight
import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalCartanCentralHeight
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.Geometry.Building.RealTorusDuality

/-! # Cartan regions for the wave-packet estimates -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal
open Langlands.GroupScheme Langlands.LinearAlgebra Langlands.LinearAlgebra.RationalSpan
open Langlands.Plancherel Langlands.Aubert.General.RationalPointFamily

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {S : CommGroupScheme (Spec (CommRingCat.of F))}
  {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
  {i : S.toGrp ⟶ G} {ν : cocharacterLattice S}
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν)

/-- The largest absolute simple-root value at the actual `H₀(m)`, with value zero in rank zero. -/
def rationalMinimalSimpleRootSize (m : standardLeviPoints i ν ∅) : ℝ≥0 :=
  letI := hG.smooth
  letI : Fintype (SimpleRoot i ν) := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  Finset.univ.sup fun a : SimpleRoot i ν =>
    Real.toNNReal |RealTorusSpace.eval S a.1 (rationalMinimalH0 hG hi hν m)|

/-- Every simple-root evaluation is bounded in absolute value by the root size. -/
theorem abs_eval_rationalMinimalH0_le_simpleRootSize (m : standardLeviPoints i ν ∅)
    (a : SimpleRoot i ν) :
    |RealTorusSpace.eval S a.1 (rationalMinimalH0 hG hi hν m)| ≤
      rationalMinimalSimpleRootSize hG hi hν m := by
  let := hG.smooth
  let : Fintype (SimpleRoot i ν) := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  have hb := Finset.le_sup (f := fun b : SimpleRoot i ν =>
    Real.toNNReal |RealTorusSpace.eval S b.1 (rationalMinimalH0 hG hi hν m)|) (Finset.mem_univ a)
  have hb' : (Real.toNNReal |RealTorusSpace.eval S a.1 (rationalMinimalH0 hG hi hν m)| : ℝ) ≤
      rationalMinimalSimpleRootSize hG hi hν m := by exact_mod_cast hb
  rwa [Real.coe_toNNReal _ (abs_nonneg _)] at hb'

/-- The ambient rational-character valuation is its restricted evaluation on `H₀`. -/
theorem eval_torusCharacterRestrict_rationalMinimalH0
    (χ : rationalCharacters G) (m : standardLeviPoints i ν ∅) :
    RealTorusSpace.eval S (torusCharacterRestrict i χ) (rationalMinimalH0 hG hi hν m) =
      ((rationalCharacterValuation G (m : rationalPoints G)).toAdd χ : ℝ) := by
  let j := Standard.leviHom i ν ∅
  let s := Standard.leviTorusHom i ν ∅
  have hchar : BruhatTits.Cartan.characterRestriction s (characterRestrict j χ) =
      torusCharacterRestrict i χ := by
    change rationalCharacters.equivCharacterLattice S (characterRestrict s (characterRestrict j χ)) =
      rationalCharacters.equivCharacterLattice S (characterRestrict i χ)
    rw [← AddMonoidHom.comp_apply,
      ← characterRestrict_comp, Standard.leviTorusHom_comp]
  have hm : rationalPoints.map j ((Standard.leviPointsEquiv i ν ∅).symm m) =
      (m : rationalPoints G) :=
    congrArg Subtype.val ((Standard.leviPointsEquiv i ν ∅).apply_symm_apply m)
  rw [← hchar, rationalMinimalH0, BruhatTits.Cartan.centralizerValuation_spec,
    rationalCharacterValuation_characterRestrict, hm]

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
include hG hi hν in
private theorem span_simpleRoots_torusCharacterRestrict_real :
    Submodule.span ℝ
      ((fun a : characterLattice S => (1 : ℝ) ⊗ₜ[ℤ] a) ''
        (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i))) = ⊤ := by
  have := hi.isSplitSubtorus.mono
  have hroots := ratSpan_simpleRelativeRoots_eq_relativeRootSpan i ν hν
    (fun _ hα => (relativeRootSystem F G hG S i hi).neg_mem_relativeRoots i
      hi.isSplitSubtorus.1 hα)
  have hspan := relativeRootsRestrictedCharactersSpan F G hG S i hi
  change ratSpan (relativeRoots i ∪ Set.range (torusCharacterRestrict i)) = ⊤ at hspan
  have hjoint : ratSpan (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i)) = ⊤ := by
    simp only [ratSpan, Set.image_union, Submodule.span_union] at hspan ⊢
    change ratSpan (simpleRelativeRoots i ν) ⊔ ratSpan (Set.range (torusCharacterRestrict i)) = ⊤
    rwa [hroots]
  rw [← map_ratSpan_baseChange, hjoint, Submodule.baseChange_top, Submodule.map_top]
  exact LinearMap.range_eq_top.mpr (rationalRealTensorEquiv (characterLattice S)).surjective

/-- The largest simple-root value and the ambient valuation coordinates together bound any
seminorm of the actual `H₀(m)` on the minimal Levi. -/
theorem exists_rationalMinimalH0_seminorm_le_simpleRootSize_add_coordinates
    (N : Seminorm ℝ (RealTorusSpace.V S)) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ m : standardLeviPoints i ν ∅,
      N (rationalMinimalH0 hG hi hν m) ≤
        C * (rationalMinimalSimpleRootSize hG hi hν m + ‖rationalValuationCoordinates G hG m‖) := by
  classical
  let H (m : standardLeviPoints i ν ∅) := rationalMinimalH0 hG hi hν m
  let R (m : standardLeviPoints i ν ∅) : ℝ := rationalMinimalSimpleRootSize hG hi hν m
  let Z (m : standardLeviPoints i ν ∅) := ‖rationalValuationCoordinates G hG m‖
  have hsize (m : standardLeviPoints i ν ∅) : 0 ≤ R m + Z m :=
    add_nonneg (NNReal.coe_nonneg _) (norm_nonneg _)
  have hform (x : RealTorusSpace.Vstar S) :
      ∃ C : ℝ, 0 ≤ C ∧ ∀ m, |RealTorusSpace.pair S x (H m)| ≤ C * (R m + Z m) := by
    have hx : x ∈ Submodule.span ℝ
        ((fun a : characterLattice S => (1 : ℝ) ⊗ₜ[ℤ] a) ''
          (simpleRelativeRoots i ν ∪ Set.range (torusCharacterRestrict i))) := by
      rw [span_simpleRoots_torusCharacterRestrict_real hG hi hν]
      exact Submodule.mem_top
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, ha, rfl⟩ := hx
      rcases ha with ha | ⟨χ, rfl⟩
      · refine ⟨1, zero_le_one, fun m => ?_⟩
        rw [one_mul, ← RealTorusSpace.eval_eq_pair]
        exact (abs_eval_rationalMinimalH0_le_simpleRootSize hG hi hν m ⟨a, ha⟩).trans
          (le_add_of_nonneg_right (norm_nonneg _))
      · obtain ⟨C, hC, hb⟩ := exists_abs_rationalCharacterValuation_le_coordinates hG χ
        refine ⟨C, hC, fun m => ?_⟩
        rw [← RealTorusSpace.eval_eq_pair, eval_torusCharacterRestrict_rationalMinimalH0 hG hi hν]
        exact (hb m).trans (mul_le_mul_of_nonneg_left (le_add_of_nonneg_left (NNReal.coe_nonneg _)) hC)
    | zero => exact ⟨0, le_rfl, fun m => by simp⟩
    | add x y _ _ hx hy =>
      obtain ⟨Cx, hCx, hx⟩ := hx
      obtain ⟨Cy, hCy, hy⟩ := hy
      refine ⟨Cx + Cy, add_nonneg hCx hCy, fun m => ?_⟩
      rw [map_add, LinearMap.add_apply, add_mul]
      exact (abs_add_le _ _).trans (add_le_add (hx m) (hy m))
    | smul t x _ hx =>
      obtain ⟨C, hC, hx⟩ := hx
      refine ⟨|t| * C, mul_nonneg (abs_nonneg _) hC, fun m => ?_⟩
      rw [map_smul, LinearMap.smul_apply, smul_eq_mul, abs_mul, mul_assoc]
      exact mul_le_mul_of_nonneg_left (hx m) (abs_nonneg _)
  let := hi.isSplitSubtorus.1.finite_realCocharacterSpace
  let b := Module.finBasis ℝ (RealTorusSpace.V S)
  let e := RealTorusSpace.characterDualEquiv hi.isSplitSubtorus.1
  choose C hC hb using fun k => hform (e.symm (b.coord k))
  have hcoord (k) (m : standardLeviPoints i ν ∅) : |b.repr (H m) k| ≤ C k * (R m + Z m) := by
    have hk := hb k m
    change |e (e.symm (b.coord k)) (H m)| ≤ C k * (R m + Z m) at hk
    simpa only [LinearEquiv.apply_symm_apply, Module.Basis.coord_apply] using hk
  let A := ∑ k, C k * N (b k)
  have hA : 0 ≤ A := Finset.sum_nonneg fun k _ => mul_nonneg (hC k) (apply_nonneg N _)
  refine ⟨1 + A, le_add_of_nonneg_right hA, fun m => ?_⟩
  have hsum : N (H m) ≤ A * (R m + Z m) := by
    conv_lhs => rw [← b.sum_repr (H m)]
    rw [show A * (R m + Z m) = ∑ k, (C k * N (b k)) * (R m + Z m) from
      Finset.sum_mul ..]
    refine (Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _).trans
      (Finset.sum_le_sum fun k _ => ?_)
    rw [map_smul_eq_mul, Real.norm_eq_abs, mul_right_comm]
    exact mul_le_mul_of_nonneg_right (hcoord k m) (apply_nonneg N _)
  exact hsum.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left zero_le_one) (hsize m))

/-- On the closed minimal-Levi chamber, either central Fourier control applies at
scale `max 1 t`, or the point belongs to the threshold and positive-part regions of a
proper standard Levi. One positive-part parameter works for every threshold. -/
theorem exists_rationalMinimalLevi_packetRegions (N : Seminorm ℝ (RealTorusSpace.V S)) :
    ∃ δ > 0, ∀ (t : ℝ) (m : standardLeviPoints i ν ∅),
      m ∈ rationalMinimalClosedChamber hG hi hν →
      (rationalMinimalSimpleRootSize hG hi hν m : ℝ) ≤
        max 1 t * (1 + ‖rationalValuationCoordinates G hG m‖) ∨
      ∃ J : Finset (SimpleRoot i ν), rootSet i ν J ⊂ simpleRelativeRoots i ν ∧
        m ∈ rationalConstantTermThresholdRegion hG hi hν (rootSet i ν J) t ∧
        m ∈ rationalPositivePartRegion hG hi hν N (rootSet i ν J) δ := by
  classical
  let := hG.smooth
  let : Fintype (SimpleRoot i ν) := (hi.isSplitSubtorus.1.finite_simpleRelativeRoots i ν).fintype
  obtain ⟨C, hC, hb⟩ := exists_rationalMinimalH0_seminorm_le_simpleRootSize_add_coordinates hG hi hν N
  have hCpos : 0 < C := zero_lt_one.trans_le hC
  refine ⟨(2 * C)⁻¹, inv_pos.mpr (mul_pos (by norm_num) hCpos), fun t m hm => ?_⟩
  let H := rationalMinimalH0 hG hi hν m
  let R : ℝ≥0 := rationalMinimalSimpleRootSize hG hi hν m
  let Z := ‖rationalValuationCoordinates G hG m‖
  by_cases h : (R : ℝ) ≤ max 1 t * (1 + Z)
  · exact Or.inl h
  right
  have hZ : 0 ≤ Z := norm_nonneg _
  have hmax : (1 : ℝ) ≤ max 1 t := le_max_left _ _
  have honeZ : 1 ≤ 1 + Z := le_add_of_nonneg_right hZ
  have hscale : 1 + Z ≤ max 1 t * (1 + Z) := le_mul_of_one_le_left (by linarith) hmax
  have hRpos : 0 < (R : ℝ) := (zero_lt_one.trans_le (honeZ.trans hscale)).trans (lt_of_not_ge h)
  have ht : t ≤ (R : ℝ) := (le_max_right _ _).trans
    ((le_mul_of_one_le_right (zero_le_one.trans hmax) honeZ).trans (le_of_not_ge h))
  have hN : (2 * C)⁻¹ * N H ≤ (R : ℝ) := by
    have hval : Z ≤ (R : ℝ) := by linarith [hscale.trans (le_of_not_ge h)]
    have hbound : N H ≤ (2 * C) * (R : ℝ) := by
      calc N H ≤ C * ((R : ℝ) + Z) := hb m
        _ ≤ C * ((R : ℝ) + R) := mul_le_mul_of_nonneg_left (add_le_add_right hval _) hCpos.le
        _ = (2 * C) * R := by ring
    rw [← div_eq_inv_mul, div_le_iff₀ (show 0 < 2 * C by positivity)]
    simpa only [mul_comm] using hbound
  let J := Finset.univ.filter fun a : SimpleRoot i ν => RealTorusSpace.eval S a.1 H ≠ R
  have hmaxroot : ∃ a : SimpleRoot i ν, RealTorusSpace.eval S a.1 H = R := by
    have hRpos' : (⊥ : ℝ≥0) < R := hRpos
    obtain ⟨a, _, ha⟩ := (Finset.le_sup_iff hRpos').mp (show R ≤
      Finset.univ.sup (fun b : SimpleRoot i ν => Real.toNNReal |RealTorusSpace.eval S b.1 H|)
      from le_rfl)
    have hab : 0 ≤ RealTorusSpace.eval S a.1 H := hm _ a.2
    have habs := abs_eval_rationalMinimalH0_le_simpleRootSize hG hi hν m a
    rw [abs_of_nonneg hab] at habs
    refine ⟨a, habs.antisymm ?_⟩
    exact (show (R : ℝ) ≤ (Real.toNNReal |RealTorusSpace.eval S a.1 H| : ℝ) from ha).trans_eq
      (by rw [abs_of_nonneg hab, Real.coe_toNNReal _ hab])
  obtain ⟨a, ha⟩ := hmaxroot
  have hproper : rootSet i ν J ⊂ simpleRelativeRoots i ν := by
    refine Set.ssubset_iff_subset_ne.mpr ⟨rootSet_subset i ν J, fun he => ?_⟩
    have hamem : (a : characterLattice S) ∈ rootSet i ν J := he.symm ▸ a.2
    exact (Finset.mem_filter.mp ((val_mem_rootSet i ν J a).mp hamem)).2 ha
  have hout (a : characterLattice S) (ha : a ∈ simpleRelativeRoots i ν \ rootSet i ν J) :
      RealTorusSpace.eval S a H = R := by
    by_contra hne
    exact ha.2 ((val_mem_rootSet i ν J ⟨a, ha.1⟩).mpr
      (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hne⟩))
  exact ⟨J, hproper, ⟨hm, fun a ha => (hout a ha).symm ▸ ht⟩,
    ⟨hm, fun a ha => (hout a ha).symm ▸ hN⟩⟩

/-- Under minimal-Levi Cartan covering, the central branch gives a comparison
with full matrix height. The other branch lies in the threshold and positive-part
regions for a proper standard Levi. -/
theorem exists_rationalMinimalLevi_height_or_packetRegions [LocallyOfFiniteType G.X.hom]
    {K0 : Subgroup (rationalPoints G)} (hK0 : IsCompact (K0 : Set (rationalPoints G)))
    (hcover : StandardLeviCartanCovering F i ν ∅ K0)
    (N : Seminorm ℝ (RealTorusSpace.V S)) (hN : ∀ v, N v = 0 → v = 0)
    {n : Type} [Fintype n] [DecidableEq n] [Nonempty n] (ρ : MatrixRepresentation G n) :
    ∃ δ > 0, ∀ t : ℝ, ∃ D ≥ 1, ∀ m : standardLeviPoints i ν ∅,
      m ∈ rationalMinimalClosedChamber hG hi hν →
      1 + rationalHeight (F := F) ρ (m : rationalPoints G) ≤
        D * (1 + ‖rationalValuationCoordinates G hG m‖) ∨
      ∃ J : Finset (SimpleRoot i ν), rootSet i ν J ⊂ simpleRelativeRoots i ν ∧
        m ∈ rationalConstantTermThresholdRegion hG hi hν (rootSet i ν J) t ∧
        m ∈ rationalPositivePartRegion hG hi hν N (rootSet i ν J) δ := by
  obtain ⟨δ, hδ, hregions⟩ := exists_rationalMinimalLevi_packetRegions hG hi hν N
  obtain ⟨C, hC, hnorm⟩ :=
    exists_rationalMinimalH0_seminorm_le_simpleRootSize_add_coordinates hG hi hν N
  obtain ⟨A, hA, hheight⟩ := hasMinimalLeviHeightComparison_of_cartanCovering
    hG hi hν hK0 hcover N hN ρ
  refine ⟨δ, hδ, fun t => ?_⟩
  let T := max 1 t
  let D := 1 + A * (1 + C * (T + 1))
  have hC0 : 0 ≤ C := zero_le_one.trans hC
  have hT : 1 ≤ T := le_max_left _ _
  refine ⟨D, le_add_of_nonneg_right (by positivity), fun m hm => ?_⟩
  rcases hregions t m hm with hcentral | hunbounded
  · left
    let Z := ‖rationalValuationCoordinates G hG m‖
    have hZ : 0 ≤ Z := norm_nonneg _
    have hsum : (rationalMinimalSimpleRootSize hG hi hν m : ℝ) + Z ≤ (T + 1) * (1 + Z) := by
      calc (rationalMinimalSimpleRootSize hG hi hν m : ℝ) + Z
        ≤ T * (1 + Z) + Z := add_le_add_left hcentral Z
      _ ≤ (T + 1) * (1 + Z) := by
        rw [add_mul, one_mul]
        linarith
    have hcompare : N (rationalMinimalH0 hG hi hν m) ≤ C * (T + 1) * (1 + Z) := by
      rw [mul_assoc]
      exact (hnorm m).trans (mul_le_mul_of_nonneg_left hsum hC0)
    calc 1 + rationalHeight (F := F) ρ (m : rationalPoints G)
        ≤ A * (1 + N (rationalMinimalH0 hG hi hν m)) := hheight m
      _ ≤ A * (1 + C * (T + 1) * (1 + Z)) :=
        mul_le_mul_of_nonneg_left (add_le_add_right hcompare 1) hA.le
      _ ≤ D * (1 + Z) := by
        dsimp only [D]
        nlinarith only [hZ, mul_nonneg hA.le hZ]
  · exact Or.inr hunbounded

end Langlands.HarishChandraSchwartz

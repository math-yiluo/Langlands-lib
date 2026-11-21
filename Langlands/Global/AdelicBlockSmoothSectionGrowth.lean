import Langlands.Global.AdelicBlockCoefficientGrowth
import Langlands.Global.AdelicBlockSmoothFiniteDeformation
import Langlands.Automorphic.FiniteLevelSlices
import Langlands.Global.EisensteinEvaluationMatrix

/-! # Full adelic growth of the smooth block sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Classical BigOperators Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.GeneralLinear
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints
open EisensteinJet

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "std" => GroupScheme.MatrixRepresentation.standard (Fin n) (CommRingCat.of F)
local notation "J" => standardCompact F n
local notation "KI" => standardInfiniteCompact F n
local notation "KF" => FiniteAdelicGL.standardIntegral F n
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "W" => smoothCompactFiniteSections F B S
local notation "M" => FullLevi F B
local notation "mH" => AdelicMatrixHeight.blockProductHeight B F
local notation "H" => AdelicMatrixHeight.height F n
local notation "R" => finiteSmoothAction F B S
local notation "C" => finiteSmoothCompactAction F B S

local instance sectionGrowthGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)
local instance sectionGrowthVAGroup : AddCommGroup V := Submodule.addCommGroup _
local instance sectionGrowthWAGroup : AddCommGroup W := Submodule.addCommGroup _

private theorem smoothCompactFiniteAction_fixed
    (f : W) {L : OpenSubgroup (FiniteAdelicGL F n)}
    (hL : ∀ l : L, RealizedSections.finiteAction F B S l.val f.val.val = f.val.val) (l : L) :
    smoothCompactFiniteAction F B S l.val f = f :=
  Subtype.ext (Subtype.ext (hL l))

/-- Smooth infinite slices and the one finite level give continuity on the
whole adelic group. -/
theorem continuous_smoothBlockSection (f : W) : Continuous f.val.val.val := by
  obtain ⟨L, hL⟩ := f.val.property
  have h := continuous_evaluateSmoothSlices F n (fun d => smoothScalarSlice F B S d f) L (by
    intro b l
    rw [← smoothScalarSlice_finiteAction F B S l.val b f, smoothCompactFiniteAction_fixed F B S f hL l])
  have he : evaluateSmoothSlices F n (fun d => smoothScalarSlice F B S d f) = f.val.val.val := by
    funext x
    rw [evaluateSmoothSlices, smoothScalarSlice_apply, AdelicGL.pair_projections]
  rwa [he] at h

namespace SchemeSection

open Langlands.Automorphic.GroupSchemeFunctions

/-- The smooth block section is adelically smooth in the specified scheme
atlas, including the common open finite stabilizer. -/
theorem isAdelicSmoothFunction (f : W) {d : ℕ}
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom) :
    IsAdelicSmoothFunction F GLG (smoothSectionOnScheme F B S f) := by
  refine ⟨(continuous_smoothBlockSection F B S f).comp (adelicHomeomorph F n).continuous, ?_, ?_⟩
  · let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    let := smoothChartedSpace F GLG hsmooth
    intro b
    rw [show InfinitePlotSmoothFunctions F GLG = manifoldSmoothFunctions F GLG hsmooth from
      plotSmoothFunctions_eq_manifoldSmoothFunctions F GLG hsmooth]
    exact smoothSectionOnScheme_hasSmoothSlices F B S hsmooth f b
  · obtain ⟨L, hL⟩ := f.val.property
    let e := finiteHomeomorph F n
    let L' := L.comap e.toMonoidHom e.continuous
    refine ⟨L'.toSubgroup, L'.isOpen, fun l hl g => ?_⟩
    have hd := hL ⟨e l, hl⟩
    have he := congrArg (fun v : RealizedSections F B S => v.val (adelicHomeomorph F n g)) hd
    change f.val.val.val (adelicHomeomorph F n (g * ofFinite F GLG l)) =
      f.val.val.val (adelicHomeomorph F n g)
    rw [map_mul, adelicHomeomorph_ofFinite]
    exact he

end SchemeSection

/-- The polynomial growth algebra on the compact picture, with a bound
uniform over the full standard compact. -/
abbrev compactLeviPolynomialGrowth : Subalgebra ℂ (J × M → ℂ) :=
  polynomialGrowthAlgebra (fun z => mH z.2) (fun z => AdelicMatrixHeight.one_le_blockProductHeight B F z.2)

private def normalizedSliceAtOne : V →ₗ[ℂ] (M → ℂ) where
  toFun f := normalizedSlice F B f.val.val 1
  map_add' f g := by
    funext m
    exact mul_add _ _ _
  map_smul' a f := by
    funext m
    exact mul_left_comm _ _ _

private theorem normalizedSliceAtOne_translate (f : V) (k : J) (a : KI)
    (ha : a.val = AdelicGL.infinite F n k.val) :
    normalizedSliceAtOne F B S (R (AdelicGL.finite F n k.val) (C a f)) =
      normalizedSlice F B f.val.val k := by
  funext m
  change (leviHalfCharacter F B m : ℂ)⁻¹ * f.val.val
    ((B.leviEmbedding (Adeles F) m * (1 : AdelicGL F n)) *
      AdelicGL.ofFinite F n (AdelicGL.finite F n k.val) * AdelicGL.ofInfinite F n a.val) = _
  rw [mul_one, mul_assoc, AdelicGL.ofFinite_eq_pair, AdelicGL.ofInfinite_eq_pair,
    AdelicGL.pair_mul, one_mul, mul_one, ha, AdelicGL.pair_projections]
  rfl

/-- Compact finiteness and finite smoothness give a finite-dimensional
common span of the normalized Levi coefficients of a fixed section. -/
theorem exists_finiteDimensional_compactSlices (f : W) :
    ∃ U : Submodule ℂ (M → ℂ), FiniteDimensional ℂ U ∧ U ≤ coefficientValues F B S ∧
      ∀ k : J, normalizedSlice F B f.val.val.val k ∈ U := by
  obtain ⟨L, hL⟩ := f.val.property
  obtain ⟨D, hD⟩ := GroupSchemeFunctions.exists_finset_mem_leftCoset L (FiniteAdelicGL.standardIntegralCompact F n)
  let T := FiniteVectors.orbitSpan C f.val
  let : FiniteDimensional ℂ T := ((mem_smoothCompactFiniteSections F B S f.val).mp f.property).1
  let U₀ : Submodule ℂ V := ⨆ d : D, T.map (R d.val)
  let : FiniteDimensional ℂ U₀ := by
    have (d : D) : Module.Finite ℂ (T.map (R d.val)) := inferInstance
    exact Submodule.finite_iSup _
  let U := U₀.map (normalizedSliceAtOne F B S)
  refine ⟨U, inferInstance, ?_, fun k => ?_⟩
  · rintro _ ⟨u, _, rfl⟩
    exact u.val.property.2 1
  let a : KI := ⟨_, ((mem_standardCompact_iff F n k.val).mp k.property).1⟩
  let b := AdelicGL.finite F n k.val
  obtain ⟨d, hd, hdL⟩ := hD b ((mem_standardCompact_iff F n k.val).mp k.property).2
  let l : L := ⟨d⁻¹ * b, hdL⟩
  have hfix : R l.val f.val = f.val := Subtype.ext (hL l)
  have hcomm : R l.val (C a f.val) = C a (R l.val f.val) :=
    Subtype.ext (RealizedSections.finiteAction_infiniteCompactAction F B S l.val a f.val.val)
  have hbl : b = d * l.val := (mul_inv_cancel_left d b).symm
  refine ⟨R b (C a f.val), ?_, normalizedSliceAtOne_translate F B S f.val k a rfl⟩
  rw [hbl, map_mul, Module.End.mul_apply, hcomm, hfix]
  exact Submodule.mem_iSup_of_mem (i := (⟨d, hd⟩ : D))
    ⟨C a f.val, FiniteVectors.action_mem_orbitSpan C a f.val, rfl⟩

/-- The compact picture has one polynomial bound on all of its normalized
Levi slices. Finite point evaluations bound its basis coordinates. -/
theorem normalizedSlice_mem_compactLeviPolynomialGrowth (f : W) :
    (fun z : J × M => normalizedSlice F B f.val.val.val z.1 z.2) ∈ compactLeviPolynomialGrowth F B := by
  obtain ⟨U, hU, hCoeff, hMem⟩ := exists_finiteDimensional_compactSlices F B S f
  let u (k : J) : U := ⟨normalizedSlice F B f.val.val.val k, hMem k⟩
  obtain ⟨x, e, he⟩ := exists_evaluationEquiv U.subtype (Submodule.injective_subtype U)
  let P := compactLeviPolynomialGrowth F B
  let c (j : Fin (Module.finrank ℂ U)) : U := e.symm (Pi.single j 1)
  have hEq (k : J) : u k = ∑ j, e (u k) j • c j := by
    apply e.injective
    rw [map_sum]
    simp only [map_smul, c, LinearEquiv.apply_symm_apply]
    funext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply, mul_ite, mul_one, mul_zero,
      Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  have hcont (j : Fin (Module.finrank ℂ U)) : Continuous (fun k => e (u k) j) := by
    simp only [he]
    exact continuous_const.mul ((continuous_smoothBlockSection F B S f).comp
      (continuous_const.mul continuous_subtype_val))
  have hcoef (j : Fin (Module.finrank ℂ U)) :
      (fun z : J × M => e (u z.1) j) ∈ P := by
    let : CompactSpace J := isCompact_iff_compactSpace.mp (isCompact_standardCompact F n)
    obtain ⟨D, hD⟩ := isCompact_univ.exists_bound_of_continuousOn (hcont j).continuousOn
    refine ⟨max 1 D, le_max_left _ _, 0, fun z => ?_⟩
    simpa only [pow_zero, mul_one] using (hD z.1 (Set.mem_univ _)).trans (le_max_right 1 D)
  have hbasis (j : Fin (Module.finrank ℂ U)) :
      (fun z : J × M => (c j).val z.2) ∈ P := by
    obtain ⟨D, hD, d, hb⟩ := coefficientValues_le_leviPolynomialGrowth F B S (hCoeff (c j).property)
    exact ⟨D, hD, d, fun z => hb z.2⟩
  have hf : (fun z : J × M => normalizedSlice F B f.val.val.val z.1 z.2) =
      ∑ j, (fun z : J × M => e (u z.1) j) * (fun z : J × M => (c j).val z.2) := by
    funext z
    have hz := congrArg (fun v : U => v.val z.2) (hEq z.1)
    simpa only [Finset.sum_apply, Pi.mul_apply, Submodule.coe_sum, Submodule.coe_smul,
      Pi.smul_apply, smul_eq_mul] using hz
  rw [hf]
  exact P.sum_mem fun j _ => P.mul_mem (hcoef j) (hbasis j)

/-- The full adelic polynomial bound follows from the compact picture
bound, the half modulus and the block projection bound. -/
theorem smoothBlockSection_polynomialGrowth (hn : 0 < n) (f : W) :
    f.val.val.val ∈ polynomialGrowthAlgebra H (AdelicMatrixHeight.one_le_height F n hn) := by
  let P := compactLeviPolynomialGrowth F B
  have hhalf : (fun z : J × M => (leviHalfCharacter F B z.2 : ℂ)) ∈ P := by
    obtain ⟨D, hD, d, h⟩ := AdelicMatrixHeight.leviHalfCharacter_polynomialGrowth B F
    exact ⟨D, hD, d, fun z => h z.2⟩
  obtain ⟨D, hD, d, hb⟩ := P.mul_mem hhalf (normalizedSlice_mem_compactLeviPolynomialGrowth F B S f)
  obtain ⟨A, hA⟩ := (isCompact_standardCompact F n).bddAbove_image
    (AdelicMatrixHeight.continuous_height F hn).continuousOn
  let A₀ := max 1 A
  have hA₀ : 1 ≤ A₀ := le_max_left _ _
  refine ⟨D * A₀ ^ (B.length * d), one_le_mul_of_one_le_of_one_le hD (one_le_pow₀ hA₀),
    B.length * d, fun x => ?_⟩
  obtain ⟨p, k, hpk⟩ := exists_parabolic_mul_standardCompact F B x
  let m := B.leviProjection (Adeles F) p
  have hkinv : H k.val⁻¹ ≤ A₀ := by
    rw [AdelicMatrixHeight.height_inv]
    exact (hA ⟨k.val, k.property, rfl⟩).trans (le_max_right _ _)
  have hp : p.val = x * k.val⁻¹ := by rw [hpk, mul_inv_cancel_right]
  have hpH : H p.val ≤ H x * A₀ := by
    rw [hp]
    exact (AdelicMatrixHeight.height_mul_le F n hn _ _).trans
      (mul_le_mul_of_nonneg_left hkinv (zero_le_one.trans (AdelicMatrixHeight.one_le_height F n hn x)))
  have hmH := AdelicMatrixHeight.blockProductHeight_leviProjection_le B F p
  calc
    ‖f.val.val.val x‖ = ‖(leviHalfCharacter F B m : ℂ) * normalizedSlice F B f.val.val.val k m‖ := by
      rw [hpk, scalarSection_apply_mul F B _ f.val.val p k]
      rfl
    _ ≤ D * mH m ^ d := hb (k, m)
    _ ≤ D * ((H x * A₀) ^ B.length) ^ d := mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (zero_le_one.trans (AdelicMatrixHeight.one_le_blockProductHeight B F m))
        (hmH.trans (pow_le_pow_left₀ (zero_le_one.trans (AdelicMatrixHeight.one_le_height F n hn p.val)) hpH _)) d)
      (zero_le_one.trans hD)
    _ = _ := by rw [← pow_mul, mul_pow]; ring

namespace SchemeSection

open Langlands.Automorphic.GroupSchemeFunctions

/-- Full moderate growth measured in the exact norm for the standard
matrix embedding. -/
theorem hasModerateGrowthFunction (hn : 0 < n) (f : W) :
    HasModerateGrowthFunction F GLG std (smoothSectionOnScheme F B S f) := by
  obtain ⟨D, hD, d, h⟩ := smoothBlockSection_polynomialGrowth F B S hn f
  let a : ℝ := (n : ℝ) ^ (∑ v : InfinitePlace F, v.mult)
  have ha : 0 < a := pow_pos (by exact_mod_cast hn) _
  refine ⟨D * a ^ d, mul_pos (zero_lt_one.trans_le hD) (pow_pos ha d), d, fun g => ?_⟩
  rw [Real.rpow_natCast, RepresentationGrowth.adelicSourceNorm_standard]
  change ‖f.val.val.val (adelicHomeomorph F n g)‖ ≤ _
  have hg := h (adelicHomeomorph F n g)
  rw [AdelicMatrixHeight.height_eq_scalar_mul_sourceNorm] at hg
  simpa only [mul_pow, ← mul_assoc, a] using hg

end SchemeSection

end Langlands.Global.AdelicBlockScalarSections

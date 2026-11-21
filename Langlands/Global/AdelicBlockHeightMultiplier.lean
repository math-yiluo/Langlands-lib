import Langlands.Global.AdelicBlockFiniteSectionDeformation
import Langlands.Global.AdelicEisensteinHeightDifferential
import Langlands.Global.GeneralLinearInfiniteAdelicEnveloping
import Mathlib.RingTheory.Finiteness.Subalgebra

/-! # Multiplying a block section by a differentiated height pairing -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj Manifold ContDiff

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints InfiniteAdelicGroupPoints AdelicBlockEisensteinGeometry
open Langlands.Geometry.Manifold AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight
open Langlands.FiniteVectors

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "baseRing" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) baseRing
local notation "wt" => GroupScheme.GeneralLinear.blockShapeWeight B
local notation "P" => GroupScheme.GeneralLinear.blockParabolicScheme (Fin n) baseRing wt
local notation "pB" => GroupScheme.GeneralLinear.blockParabolicHom (Fin n) baseRing wt
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "AdelicMatrix" => AdelicGL F n
local notation "W" => RealizedSections F B S
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "A" => CompactFiniteRealizedSections F B S
local notation "KI" => standardInfiniteCompact F n
local notation "points" => adelicHomeomorph F n

local instance heightMultiplierGLAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) baseRing
local instance heightMultiplierParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance heightMultiplierSmoothAddCommGroup : AddCommGroup V := Submodule.addCommGroup _
local instance heightMultiplierCompactFiniteAddCommGroup : AddCommGroup A := Submodule.addCommGroup _

private def compactRightFunctionAction : Representation ℂ KI (AdelicMatrix → ℂ) :=
  (Whittaker.rightTranslation ℂ AdelicMatrix).comp
    ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)

private def smoothSectionFunctionInclusion :
    (finiteSmoothCompactAction F B S).IntertwiningMap (compactRightFunctionAction (F := F) (n := n)) where
  toLinearMap := (W).subtype.comp (V).subtype
  isIntertwining' _ := rfl

private theorem smoothSectionFunctionInclusion_injective :
    Function.Injective (smoothSectionFunctionInclusion F B S) := Subtype.val_injective.comp Subtype.val_injective

private theorem finite_mul_rightFunctions {f w : AdelicMatrix → ℂ}
    (hf : IsFiniteVector (compactRightFunctionAction (F := F) (n := n)) f)
    (hw : IsFiniteVector (compactRightFunctionAction (F := F) (n := n)) w) :
    IsFiniteVector (compactRightFunctionAction (F := F) (n := n)) (f * w) := by
  let c := compactRightFunctionAction (F := F) (n := n)
  have hfg : (orbitSpan c f * orbitSpan c w).FG :=
    (Module.Finite.iff_fg.mp hf).mul (Module.Finite.iff_fg.mp hw)
  let : FiniteDimensional ℂ (orbitSpan c f * orbitSpan c w) := (Submodule.fg_iff_finiteDimensional _).mp hfg
  apply Submodule.finiteDimensional_of_le (S₂ := orbitSpan c f * orbitSpan c w)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  change c k f * c k w ∈ _
  exact Submodule.mul_mem_mul (action_mem_orbitSpan c k f) (action_mem_orbitSpan c k w)

private theorem matrixWeight_mul_mem_compactFinite (w : AdelicMatrix → ℂ)
    (hleft : ∀ (q : Full F B) g, w (q.val * g) = w g)
    (hfin : ∀ d ∈ FiniteAdelicGL.standardIntegral F n, ∀ g, w (g * AdelicGL.ofFinite F n d) = w g)
    (hinf : IsFiniteVector (compactRightFunctionAction (F := F) (n := n)) w) (f : A) :
    ∃ y : A, y.val.val.val = f.val.val.val * w := by
  let v := f.val.val
  let g : AdelicMatrix → ℂ := v.val * w
  have hg : g ∈ W := by
    refine ⟨fun u a => ?_, fun k => ?_⟩
    · simp only [g, Pi.mul_apply, v.property.1, hleft u.val]
    · have he : normalizedSlice F B g k = w k.val • normalizedSlice F B v.val k := by
        funext m
        have hq := hleft (B.leviInParabolic (Adeles F) m) k.val
        rw [B.leviInParabolic_val] at hq
        simp only [normalizedSlice, g, Pi.mul_apply, hq, Pi.smul_apply, smul_eq_mul]
        ring
      rw [he]
      exact (coefficientValues F B S).smul_mem _ (v.property.2 k)
  let gv : W := ⟨g, hg⟩
  have hs : gv ∈ V := by
    obtain ⟨L, hL⟩ := f.val.property
    refine ⟨L ⊓ FiniteAdelicGL.standardIntegral F n, fun d => ?_⟩
    have hd := OpenSubgroup.mem_inf.mp d.property
    have hfix : RealizedSections.finiteAction F B S d.val v = v := hL ⟨d.val, hd.1⟩
    apply Subtype.ext
    funext a
    change g (a * AdelicGL.ofFinite F n d.val) = g a
    change v.val (a * AdelicGL.ofFinite F n d.val) * w (a * AdelicGL.ofFinite F n d.val) = v.val a * w a
    rw [hfin d.val hd.2, show v.val (a * AdelicGL.ofFinite F n d.val) = v.val a from
      congrFun (congrArg Subtype.val hfix) a]
  let y : V := ⟨gv, hs⟩
  have hf : IsFiniteVector (finiteSmoothCompactAction F B S) f.val := f.property
  have hy : IsFiniteVector (finiteSmoothCompactAction F B S) y :=
    (isFiniteVector_map_iff (smoothSectionFunctionInclusion F B S)
      (smoothSectionFunctionInclusion_injective F B S) y).mp
      (finite_mul_rightFunctions F (hf.map (smoothSectionFunctionInclusion F B S)) hinf)
  exact ⟨⟨y, hy⟩, rfl⟩

variable {d : ℕ}

/-- The actual height differential in the matrix picture. -/
def matrixHeightDifferential
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (g : AdelicMatrix) : ℂ :=
  (hK).heightPairingDirectional hsmooth hH X lam ((points).symm g)

private theorem matrixHeightDifferential_parabolic
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (q : Full F B) (g : AdelicMatrix) :
    matrixHeightDifferential F B hsmooth hH lam X (q.val * g) =
      matrixHeightDifferential F B hsmooth hH lam X g := by
  let R := CommAlgCat.of F (AdeleRing (𝓞 F) F)
  let qP := (blockParabolicPointsEquiv F B R).symm q
  have he : (points).symm q.val = map F P GLG pB qP := by
    apply (points).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    change q.val = (blockParabolicPointsEquiv F B R qP).val
    rw [MulEquiv.apply_symm_apply]
  rw [matrixHeightDifferential, matrixHeightDifferential, map_mul, he, (hK).heightDifferential_map_mul]

private theorem matrixHeightDifferential_finiteIntegral
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d)
    (b : FiniteAdelicGL F n) (hb : b ∈ FiniteAdelicGL.standardIntegral F n) (g : AdelicMatrix) :
    matrixHeightDifferential F B hsmooth hH lam X (g * AdelicGL.ofFinite F n b) =
      matrixHeightDifferential F B hsmooth hH lam X g := by
  let bP := (finiteHomeomorph F n).symm b
  have hbp : bP ∈ standardFiniteCompactPoints F n := by
    change finiteHomeomorph F n bP ∈ FiniteAdelicGL.standardIntegral F n
    rwa [ContinuousMulEquiv.apply_symm_apply]
  have he : (points).symm (AdelicGL.ofFinite F n b) = ofFinite F GLG bP := by
    apply (points).injective
    rw [ContinuousMulEquiv.apply_symm_apply, adelicHomeomorph_ofFinite, ContinuousMulEquiv.apply_symm_apply]
  rw [matrixHeightDifferential, matrixHeightDifferential, map_mul, he,
    (hK).heightDifferential_mul_ofFinite _ _ _ _ _ (ofFinite_mem_standardCompactPoints F ⟨bP, hbp⟩)]

private theorem matrixHeightDifferential_compactFinite
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) :
    IsFiniteVector (compactRightFunctionAction (F := F) (n := n))
      (matrixHeightDifferential F B hsmooth hH lam X) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  let := smoothLieGroup F GLG hsmooth
  let e := infiniteRealLieAlgebraEquiv F n hsmooth
  let : FiniteDimensional ℝ (ArchimedeanGL.RealLieAlgebra F n) := FiniteDimensional.of_injective
    (ArchimedeanGL.realLieAlgebraToMatrix F n).toLinearMap (ArchimedeanGL.realLieAlgebraToMatrix F n).injective
  let : FiniteDimensional ℝ (smoothModel F d) := FiniteDimensional.of_injective e.toLinearMap e.injective
  let b := Module.finBasis ℝ (smoothModel F d)
  let L : smoothModel F d →ₗ[ℝ] (AdelicMatrix → ℂ) :=
    { toFun := fun Y => matrixHeightDifferential F B hsmooth hH lam Y
      map_add' := fun Y Z => funext fun g => congrFun
        (((hK).heightDifferentialInDirection hsmooth hH lam).map_add Y Z) ((points).symm g)
      map_smul' := fun c Y => funext fun g => congrFun
        (((hK).heightDifferentialInDirection hsmooth hH lam).map_smul c Y) ((points).symm g) }
  let W₀ := Submodule.span ℂ (Set.range fun i => L (b i))
  let : FiniteDimensional ℂ W₀ := FiniteDimensional.span_of_finite _ (Set.finite_range _)
  have hmem (Y : smoothModel F d) : L Y ∈ W₀ := by
    rw [← b.sum_repr Y, map_sum]
    apply Submodule.sum_mem
    intro i _
    rw [map_smul]
    exact (W₀.restrictScalars ℝ).smul_mem _ (Submodule.subset_span ⟨i, rfl⟩)
  apply Submodule.finiteDimensional_of_le (S₂ := W₀)
  apply Submodule.span_le.mpr
  rintro _ ⟨k, rfl⟩
  let a := (infiniteHomeomorph F n).symm k.val
  have ha : a ∈ generalLinearStandardInfiniteCompact F n := by
    change infiniteHomeomorph F n a ∈ standardInfiniteCompact F n
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact k.property
  have he : (points).symm (AdelicGL.ofInfinite F n k.val) = ofInfinite F GLG a := by
    apply (points).injective
    rw [ContinuousMulEquiv.apply_symm_apply, adelicHomeomorph_ofInfinite, ContinuousMulEquiv.apply_symm_apply]
  have hf : compactRightFunctionAction F k (matrixHeightDifferential F B hsmooth hH lam X) =
      L (groupTangentConjugation 𝓘(ℝ, smoothModel F d) a X) := by
    funext g
    change (hK).heightPairingDirectional hsmooth hH X lam
      ((points).symm (g * AdelicGL.ofInfinite F n k.val)) = _
    rw [map_mul, he, (hK).heightDifferential_mul_ofInfinite _ _ _ _ _
      (ofInfinite_mem_standardCompactPoints F ⟨a, ha⟩)]
    rfl
  change compactRightFunctionAction F k (matrixHeightDifferential F B hsmooth hH lam X) ∈ W₀
  rw [hf]
  exact hmem _

/-- Multiplication by the differentiated height pairing preserves the actual
compact-finite scalar section carrier. -/
def heightSectionMultiplier
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) : Module.End ℂ A := by
  let w := matrixHeightDifferential F B hsmooth hH lam X
  have hy (f : A) := matrixWeight_mul_mem_compactFinite F B S w
    (matrixHeightDifferential_parabolic F B hsmooth hH lam X)
    (matrixHeightDifferential_finiteIntegral F B hsmooth hH lam X)
    (matrixHeightDifferential_compactFinite F B hsmooth hH lam X) f
  refine
    { toFun f := (hy f).choose
      map_add' f g := ?_
      map_smul' c f := ?_ }
  · apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (hy (f + g)).choose.val.val.val = (hy f).choose.val.val.val + (hy g).choose.val.val.val
    rw [(hy (f + g)).choose_spec, (hy f).choose_spec, (hy g).choose_spec]
    exact add_mul f.val.val.val g.val.val.val w
  · apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change (hy (c • f)).choose.val.val.val = c • (hy f).choose.val.val.val
    rw [(hy (c • f)).choose_spec, (hy f).choose_spec]
    exact smul_mul_assoc c f.val.val.val w

/-- The constructed multiplier evaluates to pointwise multiplication on scheme points. -/
theorem compactFiniteSectionOnScheme_heightSectionMultiplier
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (f : A) :
    compactFiniteSectionOnScheme F B S (heightSectionMultiplier F B S hsmooth hH lam X f) =
      compactFiniteSectionOnScheme F B S f * (hK).heightPairingDirectional hsmooth hH X lam := by
  funext g
  let w := matrixHeightDifferential F B hsmooth hH lam X
  have hy (f : A) := matrixWeight_mul_mem_compactFinite F B S w
    (matrixHeightDifferential_parabolic F B hsmooth hH lam X)
    (matrixHeightDifferential_finiteIntegral F B hsmooth hH lam X)
    (matrixHeightDifferential_compactFinite F B hsmooth hH lam X) f
  change (hy f).choose.val.val.val (points g) = _
  rw [(hy f).choose_spec]
  change f.val.val.val (points g) * (hK).heightPairingDirectional hsmooth hH X lam ((points).symm (points g)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- Multiplication by the height differential also preserves smoothness of each infinite slice. -/
theorem contMDiff_heightSectionMultiplier_pair
    (hsmooth : SmoothOfRelativeDimension d (GLG).X.hom)
    (hH : (hK).HasSmoothHeightPairings hsmooth) (lam : ComplexCharacterParameter F P)
    (X : smoothModel F d) (f : A) (b : FiniteAdelicGroupPoints F GLG) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F GLG hsmooth
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun a => compactFiniteSectionOnScheme F B S f (pair F GLG a b)) →
    ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞
      (fun a => compactFiniteSectionOnScheme F B S (heightSectionMultiplier F B S hsmooth hH lam X f)
        (pair F GLG a b)) := by
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F GLG hsmooth
  intro hf
  simp only [compactFiniteSectionOnScheme_heightSectionMultiplier, Pi.mul_apply]
  exact (contDiff_mul (𝕜 := ℝ) (𝔸 := ℂ)).contMDiff.comp
    (hf.prodMk_space ((hK).contMDiff_heightDifferential_pair hsmooth hH lam X b))

end Langlands.Global.AdelicBlockScalarSections

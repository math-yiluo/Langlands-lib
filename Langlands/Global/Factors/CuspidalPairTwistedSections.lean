import Langlands.Global.AdelicBlockAutomorphicSections
import Langlands.Global.AdelicBlockHeckeCharacter
import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Global.AdelicBlockEisensteinSmoothHeight
import Langlands.Global.AdelicBlockSmoothFiniteDeformation
import Langlands.Global.AdelicBlockParabolicCharacters
import Langlands.Global.HeckeNormPower
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.Global.AdelicEisensteinCentralCovariance

/-! # Block determinant twists of actual adelic sections -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory AlgebraicGeometry NumberField TensorProduct
open scoped CategoryTheory.MonObj TensorProduct NNReal Manifold ContDiff

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions
open Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockEisensteinGeometry AdelicBlockParabolic
open PrimitiveAdelicHeight Langlands.FiniteVectors

variable (F : Type u) [Field F] [NumberField F] {n : ℕ}
  (B : Langlands.GeneralLinear.BlockShape n)

local notation "𝕜" => CommRingCat.of F
local notation "G" => groupScheme (Fin n) 𝕜
local notation "P" => blockParabolicScheme (Fin n) 𝕜 (blockShapeWeight B)
local notation "p" => blockParabolicHom (Fin n) 𝕜 (blockShapeWeight B)
local notation "M" => blockLeviScheme (Fin n) 𝕜 (blockShapeWeight B)
local notation "U" => blockUnipotentScheme (Fin n) 𝕜 (blockShapeWeight B)
local notation "l" => blockLeviInclusion F B
local notation "iU" => blockUnipotentInclusion F B
local notation "K" => standardCompactPoints F n
local notation "hK" => isIwasawaCompact_blockParabolic F B
local notation "A" => CommAlgCat.of F (Adeles F)

local instance twistedSectionsGLAffine : IsAffine (G).X.left := isAffine_groupScheme (Fin n) _
local instance twistedSectionsParabolicAffine : IsAffine (P).X.left := blockParabolic_isAffine F B

/-- The character parameter with given complex coefficients at the block determinants. -/
def determinantParameter (s : Fin B.length → ℂ) : ComplexCharacterParameter F P :=
  ∑ i, s i ⊗ₜ[ℤ] parabolicBlockCharacter B 𝕜 i

private theorem normPower_determinant (s : ℂ) (b : ℕ) (g : AdelicGL F b) :
    ((HeckeCharacter.normPower F s).adelicDeterminant b g : ℂ) =
      Complex.exp (s * (Real.log ((AdelicBlockDeterminantCharacter.determinantNorm F b g : ℝ≥0) : ℝ) : ℂ)) := by
  change (HeckeCharacter.normPower F s (ideleClassMap F (AdelicGL.determinant F b g)) : ℂ) = _
  rw [HeckeCharacter.normPower_apply, IdeleAbsoluteValue.ideleClass_class]
  rfl

/-- In an Iwasawa factorization the block parameter is the product of determinant norm powers
on the diagonal blocks of the parabolic factor. -/
theorem heightPower_determinantParameter (s : Fin B.length → ℂ)
    (q : AdelicGroupPoints F P) {k : AdelicGroupPoints F G} (hk : k ∈ K) :
    (hK).heightPower (determinantParameter F B s) (map F P G p q * k) =
      (AdelicBlockHeckeCharacter.leviCharacter F B (fun i => HeckeCharacter.normPower F (s i))
        (B.leviProjection (Adeles F) (blockParabolicPointsEquiv F B A q)) : ℂ) := by
  rw [IsIwasawaCompact.heightPower, (hK).height_eq hk rfl]
  simp only [determinantParameter, map_sum, LinearMap.sum_apply,
    complexParameterPairing_tmul, Complex.exp_sum, characterLog_parabolicBlockCharacter,
    AdelicBlockHeckeCharacter.leviCharacter_apply, Units.coe_prod, normPower_determinant]
  rfl

variable (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

/-- The Levi realizations giving the compact picture of the twisted section. -/
abbrev determinantTwistedRealizations (s : Fin B.length → ℂ) :
    ∀ i : Fin B.length, OperatorRealization F (B.size i) :=
  fun i => (S i).heckeDeterminantTwist (HeckeCharacter.normPower F (s i))

private theorem coefficientValues_mul_normPowers (s : Fin B.length → ℂ)
    {f : FullLevi F B → ℂ} (hf : f ∈ coefficientValues F B S) :
    (fun m => f m * (AdelicBlockHeckeCharacter.leviCharacter F B
      (fun i => HeckeCharacter.normPower F (s i)) m : ℂ)) ∈
      coefficientValues F B (determinantTwistedRealizations F B S s) := by
  let χ := fun i => HeckeCharacter.normPower F (s i)
  let L : (FullLevi F B → ℂ) →ₗ[ℂ] (FullLevi F B → ℂ) :=
    { toFun := fun g m => g m * (AdelicBlockHeckeCharacter.leviCharacter F B χ m : ℂ)
      map_add' g h := funext fun m => add_mul (g m) (h m) _
      map_smul' c g := funext fun m => mul_assoc c (g m) _ }
  have hL : coefficientValues F B S ≤
      (coefficientValues F B (determinantTwistedRealizations F B S s)).comap L := by
    apply Submodule.span_le.mpr
    rintro _ ⟨v, rfl⟩
    apply Submodule.subset_span
    refine ⟨fun i => (S i).heckeDeterminantTwistEquiv (χ i) (v i), ?_⟩
    funext m
    change (∏ i, ContinuousRationalFunctions.evaluate F (B.size i)
      (((S i).heckeDeterminantTwist (χ i)).toContinuous
        ((S i).heckeDeterminantTwistEquiv (χ i) (v i))) (m i)) =
      (∏ i, ContinuousRationalFunctions.evaluate F (B.size i) ((S i).toContinuous (v i)) (m i)) *
        (AdelicBlockHeckeCharacter.leviCharacter F B χ m : ℂ)
    simp only [OperatorRealization.evaluate_heckeDeterminantTwistEquiv,
      AdelicBlockHeckeCharacter.leviCharacter_apply, Units.coe_prod, Finset.prod_mul_distrib]
    exact mul_comm _ _
  exact hL hf

local notation "e" => adelicHomeomorph F n

private def heightTwistMatrix (s : Fin B.length → ℂ) : (AdelicGL F n → ℂ) →ₗ[ℂ]
    (AdelicGL F n → ℂ) where
  toFun f := fun g => f g * (hK).heightPower (determinantParameter F B s) ((e).symm g)
  map_add' f g := funext fun x => add_mul (f x) (g x) _
  map_smul' c f := funext fun x => mul_assoc c (f x) _

private theorem heightTwistMatrix_mul_compact (s : Fin B.length → ℂ) (f : AdelicGL F n → ℂ)
    (g : AdelicGL F n) {k : AdelicGL F n} (hk : k ∈ standardCompact F n) :
    heightTwistMatrix F B s f (g * k) = heightTwistMatrix F B s (fun z => f (z * k)) g := by
  change f (g * k) * (hK).heightPower _ ((e).symm (g * k)) = f (g * k) * (hK).heightPower _ ((e).symm g)
  rw [map_mul, IsIwasawaCompact.heightPower, IsIwasawaCompact.heightPower, (hK).height_mul_right]
  change e ((e).symm k) ∈ standardCompact F n
  rwa [ContinuousMulEquiv.apply_symm_apply]

private theorem heightTwistMatrix_mem (s : Fin B.length → ℂ) (f : RealizedSections F B S) :
    heightTwistMatrix F B s f.val ∈ RealizedSections F B (determinantTwistedRealizations F B S s) := by
  refine ⟨fun u g => ?_, fun k => ?_⟩
  · let u₀ : B.unipotentSubgroup (Adeles F) := ⟨u.val.val, ⟨u.val, u.property, rfl⟩⟩
    let u' := (blockUnipotentPointsEquiv F B A).symm u₀
    have hu : e (map F U G (iU ≫ p) u') = u.val.val := by
      rw [blockUnipotentInclusion_comp]
      exact congrArg (fun w : B.unipotentSubgroup (Adeles F) => w.val)
        ((blockUnipotentPointsEquiv F B A).apply_symm_apply u₀)
    change f.val (u.val.val * g) * (hK).heightPower _ ((e).symm (u.val.val * g)) = _
    rw [f.property.1 u g, map_mul, ← hu, ContinuousMulEquiv.symm_apply_apply,
      (hK).heightPower_unipotent_mul (blockUnipotentInclusion_isGeometricUnipotentRadical F B).2.2.2.1 iU]
    rfl
  · let χ := fun i => HeckeCharacter.normPower F (s i)
    have heq : normalizedSlice F B (heightTwistMatrix F B s f.val) k =
        fun m => normalizedSlice F B f.val k m *
          (AdelicBlockHeckeCharacter.leviCharacter F B χ m : ℂ) := by
      funext m
      let q := (blockParabolicPointsEquiv F B A).symm (B.leviInParabolic (Adeles F) m)
      have hq : e (map F P G p q) = B.leviEmbedding (Adeles F) m := by
        change (blockParabolicPointsEquiv F B A q).val = _
        rw [MulEquiv.apply_symm_apply]
        rfl
      have hk : (e).symm k.val ∈ K := by
        change e ((e).symm k.val) ∈ standardCompact F n
        simpa only [ContinuousMulEquiv.apply_symm_apply] using k.property
      unfold normalizedSlice
      change _ * (f.val _ * (hK).heightPower _ ((e).symm (_ * _))) = (_ * f.val _) * _
      rw [map_mul, ← hq, ContinuousMulEquiv.symm_apply_apply,
        heightPower_determinantParameter F B s q hk,
        MulEquiv.apply_symm_apply, B.leviProjection_section, mul_assoc]
    rw [heq]
    exact coefficientValues_mul_normPowers F B S s (f.property.2 k)

local notation "KI" => standardInfiniteCompact F n
local notation "V[" R "]" => FiniteSmoothRealizedSections F B R
local notation "CF[" R "]" => CompactFiniteRealizedSections F B R
local notation "W[" R "]" => smoothCompactFiniteSections F B R

local instance twistedSectionsFiniteSmoothAddGroup (R : ∀ i : Fin B.length, OperatorRealization F (B.size i)) : AddCommGroup V[R] :=
  Submodule.addCommGroup _
local instance twistedSectionsCompactFiniteAddGroup (R : ∀ i : Fin B.length, OperatorRealization F (B.size i)) : AddCommGroup CF[R] :=
  Submodule.addCommGroup _
local instance twistedSectionsSmoothAddGroup (R : ∀ i : Fin B.length, OperatorRealization F (B.size i)) : AddCommGroup W[R] :=
  Submodule.addCommGroup _

private def compactFunctionAction : Representation ℂ KI (AdelicGL F n → ℂ) :=
  (Whittaker.rightTranslation ℂ (AdelicGL F n)).comp
    ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)

private def compactFunctionInclusion :
    (finiteSmoothCompactAction F B S).IntertwiningMap (compactFunctionAction F (n := n)) where
  toLinearMap := (RealizedSections F B S).subtype.comp (V[S]).subtype
  isIntertwining' _ := rfl

private theorem ofInfinite_mem_standardCompact (k : KI) :
    AdelicGL.ofInfinite F n k.val ∈ standardCompact F n := by
  apply (mem_standardCompact_iff F n _).mpr
  simpa only [AdelicGL.infinite_ofInfinite, AdelicGL.finite_ofInfinite] using
    ⟨k.property, (FiniteAdelicGL.standardIntegral F n).one_mem⟩

private theorem ofFinite_mem_standardCompact (k : FiniteAdelicGL F n)
    (hk : k ∈ FiniteAdelicGL.standardIntegral F n) :
    AdelicGL.ofFinite F n k ∈ standardCompact F n := by
  apply (mem_standardCompact_iff F n _).mpr
  simpa only [AdelicGL.infinite_ofFinite, AdelicGL.finite_ofFinite] using
    ⟨(standardInfiniteCompact F n).one_mem, hk⟩

private def heightTwistIntertwiner (s : Fin B.length → ℂ) :
    (compactFunctionAction F (n := n)).IntertwiningMap (compactFunctionAction F (n := n)) where
  toLinearMap := heightTwistMatrix F B s
  isIntertwining' k := by
    ext f g
    exact (heightTwistMatrix_mul_compact F B s f g (ofInfinite_mem_standardCompact F k)).symm

private def twistedCompactSection (s : Fin B.length → ℂ) (f : CF[S]) :
    CF[determinantTwistedRealizations F B S s] := by
  let R := determinantTwistedRealizations F B S s
  let v : RealizedSections F B R :=
    ⟨heightTwistMatrix F B s f.val.val.val, heightTwistMatrix_mem F B S s f.val.val⟩
  have hv : v ∈ V[R] := by
    obtain ⟨L, hL⟩ := f.val.property
    refine ⟨L ⊓ FiniteAdelicGL.standardIntegral F n, fun d => ?_⟩
    have hd := OpenSubgroup.mem_inf.mp d.property
    have hfix := hL ⟨d.val, hd.1⟩
    apply Subtype.ext
    funext a
    change heightTwistMatrix F B s f.val.val.val (a * AdelicGL.ofFinite F n d.val) =
      heightTwistMatrix F B s f.val.val.val a
    rw [heightTwistMatrix_mul_compact F B s _ _ (ofFinite_mem_standardCompact F d.val hd.2)]
    exact congrArg (fun z : RealizedSections F B S => heightTwistMatrix F B s z.val a) hfix
  let y : V[R] := ⟨v, hv⟩
  refine ⟨y, ?_⟩
  have hinc : Function.Injective (compactFunctionInclusion F B R) :=
    Subtype.val_injective.comp Subtype.val_injective
  exact (isFiniteVector_map_iff (compactFunctionInclusion F B R) hinc y).mp
    ((f.property.map (compactFunctionInclusion F B S)).map (heightTwistIntertwiner F B s))

/-- The Iwasawa twist is a smooth compact-finite section of the block determinant twists. -/
theorem exists_smoothSection_parameterTwist (s : Fin B.length → ℂ) (f : W[S])
    {d : ℕ} (hsmooth : SmoothOfRelativeDimension d (G).X.hom) :
    ∃ g : W[determinantTwistedRealizations F B S s],
      smoothSectionOnScheme F B (determinantTwistedRealizations F B S s) g =
        (hK).parameterTwist (smoothSectionOnScheme F B S f) (determinantParameter F B s) := by
  let R := determinantTwistedRealizations F B S s
  let g := twistedCompactSection F B S s (smoothSectionInclusion F B S f)
  have he : compactFiniteSectionOnScheme F B R g =
      (hK).parameterTwist (smoothSectionOnScheme F B S f) (determinantParameter F B s) := by
    funext x
    change f.val.val.val (e x) * (hK).heightPower _ ((e).symm (e x)) = _
    rw [ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hg : g.val ∈ W[R] := by
    apply (mem_smoothCompactFiniteSections_iff_schemeSlices F B R hsmooth g).mpr
    rw [he]
    exact (hK).contMDiff_parameterTwist_slice hsmooth (hasSmoothHeightPairings_blockParabolic F B hsmooth)
      _ _ (smoothSectionOnScheme_hasSmoothSlices F B S hsmooth f)
  exact ⟨⟨g.val, hg⟩, he⟩

end Langlands.Global.AdelicBlockScalarSections

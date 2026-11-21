import Langlands.Global.AdelicBlockEisensteinRoots
import Langlands.Global.AdelicBlockScalarSectionActions
import Langlands.Global.AdelicEisensteinFiniteSlices
import Langlands.Representation.Families.FiniteHolomorphicSections

/-! # The deformed finite action on the realized adelic block sections -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

namespace Langlands.Global.AdelicBlockScalarSections

open Langlands.Automorphic Langlands.Automorphic.GroupSchemeFunctions Langlands.GeneralLinear
open AdelicGroupPoints GeneralLinearGroupPoints AdelicBlockEisensteinGeometry
open AdelicBlockParabolic AdelicBlockDeterminantCharacter PrimitiveAdelicHeight

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
  (S : ∀ i : Fin B.length, OperatorRealization F (B.size i))

local notation "𝕜" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) 𝕜
local notation "wt" => GroupScheme.GeneralLinear.blockShapeWeight B
local notation "P" => GroupScheme.GeneralLinear.blockParabolicScheme (Fin n) 𝕜 wt
local notation "pB" => GroupScheme.GeneralLinear.blockParabolicHom (Fin n) 𝕜 wt
local notation "AdelicMatrix" => AdelicGL F n
local notation "W" => RealizedSections F B S
local notation "V" => FiniteSmoothRealizedSections F B S
local notation "A" => CompactFiniteRealizedSections F B S
local notation "points" => adelicHomeomorph F n
local notation "finitePoints" => finiteHomeomorph F n
local notation "hK" => isIwasawaCompact_blockParabolic F B

local instance finiteBlockGeneralLinearIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) 𝕜
local instance finiteBlockParabolicIsAffine : IsAffine (P).X.left := blockParabolic_isAffine F B
local instance finiteBlockSmoothAddCommGroup : AddCommGroup V := Submodule.addCommGroup _
local instance finiteBlockCompactFiniteAddCommGroup : AddCommGroup A := Submodule.addCommGroup _

/-- The realized scalar section evaluated on the scheme adelic (points). -/
def realizedSectionOnScheme : W →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) where
  toFun φ g := φ.val (points g)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem realizedSectionOnScheme_injective : Function.Injective (realizedSectionOnScheme F B S) := by
  intro f g h
  apply Subtype.ext
  funext x
  have he := congrFun h ((points).symm x)
  change f.val (points ((points).symm x)) = g.val (points ((points).symm x)) at he
  rwa [ContinuousMulEquiv.apply_symm_apply] at he

private def matrixFunctionEquiv : (AdelicGroupPoints F GLG → ℂ) ≃ₗ[ℂ] (AdelicMatrix → ℂ) where
  toFun f g := f ((points).symm g)
  invFun f g := f (points g)
  left_inv f := funext fun _ => congrArg f ((points).symm_apply_apply _)
  right_inv f := funext fun _ => congrArg f ((points).apply_symm_apply _)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private def finiteDeformedMatrixAction (lam : ComplexCharacterParameter F P) :
    Representation ℂ (FiniteAdelicGL F n) (AdelicMatrix → ℂ) :=
  transportRepresentation (((hK).parameterRightAction lam).comp
    ((ofFinite F GLG).toMonoidHom.comp (finitePoints).symm.toMonoidHom)) (matrixFunctionEquiv (F := F) (n := n))

private def finiteWeight (lam : ComplexCharacterParameter F P) (d : FiniteAdelicGL F n) (g : AdelicMatrix) : ℂ :=
  Complex.exp (complexParameterPairing F P lam
    ((hK).finiteHeightDisplacement ((finitePoints).symm d) ((points).symm g)))

private theorem finiteDeformedMatrixAction_apply (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : AdelicMatrix → ℂ) (g : AdelicMatrix) :
    finiteDeformedMatrixAction F B lam d f g = f (g * AdelicGL.ofFinite F n d) * finiteWeight F B lam d g := by
  change (hK).parameterRightAction lam (ofFinite F GLG ((finitePoints).symm d))
    (fun x => f (points x)) ((points).symm g) = _
  rw [(hK).parameterRightAction_finite_eq, map_mul, adelicHomeomorph_ofFinite,
    ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  rfl

private theorem finiteWeight_parabolic_mul (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (q : Full F B) (g : AdelicMatrix) :
    finiteWeight F B lam d (q.val * g) = finiteWeight F B lam d g := by
  let R := CommAlgCat.of F (AdeleRing (𝓞 F) F)
  let x := (blockParabolicPointsEquiv F B R).symm q
  have he : (points).symm q.val = map F P GLG pB x := by
    apply (points).injective
    rw [ContinuousMulEquiv.apply_symm_apply]
    change q.val = (blockParabolicPointsEquiv F B R x).val
    rw [MulEquiv.apply_symm_apply]
  rw [finiteWeight, finiteWeight, map_mul, he, (hK).finiteHeightDisplacement_map_mul]

private theorem finiteWeight_mul_infiniteCompact (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n) (g : AdelicMatrix) :
    finiteWeight F B lam d (g * AdelicGL.ofInfinite F n k.val) = finiteWeight F B lam d g := by
  let a := (infiniteHomeomorph F n).symm k.val
  have ha : a ∈ generalLinearStandardInfiniteCompact F n := by
    change infiniteHomeomorph F n a ∈ standardInfiniteCompact F n
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact k.property
  have he : (points).symm (AdelicGL.ofInfinite F n k.val) = ofInfinite F GLG a := by
    apply (points).injective
    rw [ContinuousMulEquiv.apply_symm_apply, adelicHomeomorph_ofInfinite,
      ContinuousMulEquiv.apply_symm_apply]
  rw [finiteWeight, finiteWeight, map_mul, he,
    (hK).finiteHeightDisplacement_mul_ofInfinite _ _ (ofInfinite_mem_standardCompactPoints F ⟨a, ha⟩)]

private theorem finiteDeformedMatrixAction_mem (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : W) : finiteDeformedMatrixAction F B lam d f.val ∈ W := by
  refine ⟨fun u g => ?_, fun k => ?_⟩
  · simp only [finiteDeformedMatrixAction_apply, finiteWeight_parabolic_mul F B lam d u.val,
      mul_assoc, f.property.1]
  · let fd := RealizedSections.finiteAction F B S d f
    have he : normalizedSlice F B (finiteDeformedMatrixAction F B lam d f.val) k =
        finiteWeight F B lam d k.val • normalizedSlice F B fd.val k := by
      funext m
      have hq := finiteWeight_parabolic_mul F B lam d (B.leviInParabolic (Adeles F) m) k.val
      rw [B.leviInParabolic_val] at hq
      simp only [normalizedSlice, finiteDeformedMatrixAction_apply, RealizedSections.finiteAction_apply,
        fd, hq, Pi.smul_apply, smul_eq_mul]
      ring
    rw [he]
    exact (coefficientValues F B S).smul_mem _ (fd.property.2 k)

/-- The deformed finite translation acts on the same realized scalar section carrier. -/
def deformedFiniteSubrepresentation (lam : ComplexCharacterParameter F P) :
    Subrepresentation (finiteDeformedMatrixAction F B lam) where
  toSubmodule := W
  apply_mem_toSubmodule d f hf := finiteDeformedMatrixAction_mem F B S lam d ⟨f, hf⟩

abbrev deformedFiniteAction (lam : ComplexCharacterParameter F P) : Representation ℂ (FiniteAdelicGL F n) W :=
  (deformedFiniteSubrepresentation F B S lam).toRepresentation

/-- Its evaluation agrees with the actual adelic height deformation. -/
theorem realizedSectionOnScheme_deformedFiniteAction (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : W) :
    realizedSectionOnScheme F B S (deformedFiniteAction F B S lam d f) =
      (hK).parameterRightAction lam (ofFinite F GLG ((finitePoints).symm d)) (realizedSectionOnScheme F B S f) := by
  funext g
  change (hK).parameterRightAction lam (ofFinite F GLG ((finitePoints).symm d)) _
    ((points).symm (points g)) = _
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- Integral finite translations act independently of the parameter on the source. -/
theorem deformedFiniteAction_of_mem_standardIntegral (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (hd : d ∈ FiniteAdelicGL.standardIntegral F n) :
    deformedFiniteAction F B S lam d = RealizedSections.finiteAction F B S d := by
  apply LinearMap.ext
  intro f
  apply realizedSectionOnScheme_injective F B S
  rw [realizedSectionOnScheme_deformedFiniteAction]
  let a := (finitePoints).symm d
  have ha : a ∈ standardFiniteCompactPoints F n := by
    change finitePoints a ∈ FiniteAdelicGL.standardIntegral F n
    rw [ContinuousMulEquiv.apply_symm_apply]
    exact hd
  funext g
  rw [(hK).parameterRightAction_compact _ _ (ofFinite_mem_standardCompactPoints F ⟨a, ha⟩)]
  change f.val (points (g * ofFinite F GLG a)) = f.val (points g * AdelicGL.ofFinite F n d)
  rw [map_mul, adelicHomeomorph_ofFinite, ContinuousMulEquiv.apply_symm_apply]

/-- At zero the deformed finite action specializes to the original action. -/
theorem deformedFiniteAction_zero (d : FiniteAdelicGL F n) :
    deformedFiniteAction F B S 0 d = RealizedSections.finiteAction F B S d := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change finiteDeformedMatrixAction F B 0 d f.val g = f.val (g * AdelicGL.ofFinite F n d)
  rw [finiteDeformedMatrixAction_apply]
  simp [finiteWeight]

private theorem isSmoothVector_deformedFiniteAction_iff (lam : ComplexCharacterParameter F P) (f : W) :
    IsSmoothVector (deformedFiniteAction F B S lam) f ↔
      IsSmoothVector (RealizedSections.finiteAction F B S) f := by
  constructor <;> rintro ⟨L, hL⟩
  · refine ⟨L ⊓ FiniteAdelicGL.standardIntegral F n, fun d => ?_⟩
    have hd := OpenSubgroup.mem_inf.mp d.property
    change RealizedSections.finiteAction F B S d.val f = f
    rw [← deformedFiniteAction_of_mem_standardIntegral F B S lam d.val hd.2]
    exact hL ⟨d.val, hd.1⟩
  · refine ⟨L ⊓ FiniteAdelicGL.standardIntegral F n, fun d => ?_⟩
    have hd := OpenSubgroup.mem_inf.mp d.property
    change deformedFiniteAction F B S lam d.val f = f
    rw [deformedFiniteAction_of_mem_standardIntegral F B S lam d.val hd.2]
    exact hL ⟨d.val, hd.1⟩

/-- The deformed finite action preserves the original finite-smooth subspace. -/
def deformedFiniteSmoothSubrepresentation (lam : ComplexCharacterParameter F P) :
    Subrepresentation (deformedFiniteAction F B S lam) where
  toSubmodule := V
  apply_mem_toSubmodule d _ hf := (isSmoothVector_deformedFiniteAction_iff F B S lam _).mp
    (isSmoothVector_apply d ((isSmoothVector_deformedFiniteAction_iff F B S lam _).mpr hf))

abbrev deformedFiniteSmoothAction (lam : ComplexCharacterParameter F P) : Representation ℂ (FiniteAdelicGL F n) V :=
  (deformedFiniteSmoothSubrepresentation F B S lam).toRepresentation

private theorem deformedFiniteAction_infiniteCompactAction (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (k : standardInfiniteCompact F n) (f : W) :
    deformedFiniteAction F B S lam d (RealizedSections.infiniteCompactAction F B S k f) =
      RealizedSections.infiniteCompactAction F B S k (deformedFiniteAction F B S lam d f) := by
  apply Subtype.ext
  funext g
  change finiteDeformedMatrixAction F B lam d (fun h => f.val (h * AdelicGL.ofInfinite F n k.val)) g =
    finiteDeformedMatrixAction F B lam d f.val (g * AdelicGL.ofInfinite F n k.val)
  rw [finiteDeformedMatrixAction_apply, finiteDeformedMatrixAction_apply,
    finiteWeight_mul_infiniteCompact, mul_assoc, mul_assoc, (AdelicGL.ofFinite_commute_ofInfinite F n d k.val).eq]

private def finiteSmoothDeformedTranslate (lam : ComplexCharacterParameter F P) (d : FiniteAdelicGL F n) :
    (finiteSmoothCompactAction F B S).IntertwiningMap (finiteSmoothCompactAction F B S) where
  toLinearMap := deformedFiniteSmoothAction F B S lam d
  isIntertwining' k := LinearMap.ext fun f => Subtype.ext
    (deformedFiniteAction_infiniteCompactAction F B S lam d k f.val)

/-- The deformed finite action preserves the original compact-finite subspace. -/
def deformedCompactFiniteSubrepresentation (lam : ComplexCharacterParameter F P) :
    Subrepresentation (deformedFiniteSmoothAction F B S lam) where
  toSubmodule := A
  apply_mem_toSubmodule d _ hf := FiniteVectors.IsFiniteVector.map (finiteSmoothDeformedTranslate F B S lam d) hf

abbrev deformedCompactFiniteAction (lam : ComplexCharacterParameter F P) :
    Representation ℂ (FiniteAdelicGL F n) A :=
  (deformedCompactFiniteSubrepresentation F B S lam).toRepresentation

/-- On the compact-finite carrier, integral finite translations retain their original action. -/
theorem deformedCompactFiniteAction_of_mem_standardIntegral (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (hd : d ∈ FiniteAdelicGL.standardIntegral F n) :
    deformedCompactFiniteAction F B S lam d = (compactFiniteFiniteSubrepresentation F B S).toRepresentation d := by
  apply LinearMap.ext
  intro f
  exact Subtype.ext (Subtype.ext (DFunLike.congr_fun
    (deformedFiniteAction_of_mem_standardIntegral F B S lam d hd) f.val.val))

/-- On the compact-finite carrier the specialization at zero is the original finite action. -/
theorem deformedCompactFiniteAction_zero (d : FiniteAdelicGL F n) :
    deformedCompactFiniteAction F B S 0 d = (compactFiniteFiniteSubrepresentation F B S).toRepresentation d := by
  apply LinearMap.ext
  intro f
  exact Subtype.ext (Subtype.ext (DFunLike.congr_fun (deformedFiniteAction_zero F B S d) f.val.val))

/-- Scheme-point evaluation on the compact-finite section carrier. -/
def compactFiniteSectionOnScheme : A →ₗ[ℂ] (AdelicGroupPoints F GLG → ℂ) :=
  (realizedSectionOnScheme F B S).comp ((V).subtype.comp (A).subtype)

theorem compactFiniteSectionOnScheme_injective : Function.Injective (compactFiniteSectionOnScheme F B S) :=
  (realizedSectionOnScheme_injective F B S).comp
    ((Submodule.injective_subtype (V)).comp (Submodule.injective_subtype (A)))

theorem compactFiniteSectionOnScheme_deformedFiniteAction (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : A) :
    compactFiniteSectionOnScheme F B S (deformedCompactFiniteAction F B S lam d f) =
      (hK).parameterRightAction lam (ofFinite F GLG ((finitePoints).symm d))
        (compactFiniteSectionOnScheme F B S f) :=
  realizedSectionOnScheme_deformedFiniteAction F B S lam d f.val.val

private theorem ofInfinite_projection_mem (g : AdelicGroupPoints F GLG) (hg : g ∈ standardCompactPoints F n) :
    ofInfinite F GLG (infinite F GLG g) ∈ standardCompactPoints F n :=
  ofInfinite_mem_standardCompactPoints F
    ⟨_, ((mem_standardCompactPoints_iff F g).mp hg).1⟩

/-- On every infinite slice, deformation of the compact-finite section
multiplies the translated finite argument's slice by a scalar. -/
theorem compactFiniteSectionOnScheme_deformedFiniteAction_pair (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : A)
    (a : InfiniteAdelicGroupPoints F GLG) (b : FiniteAdelicGroupPoints F GLG) :
    compactFiniteSectionOnScheme F B S (deformedCompactFiniteAction F B S lam d f) (pair F GLG a b) =
      compactFiniteSectionOnScheme F B S f (pair F GLG a (b * (finitePoints).symm d)) *
        (hK).finiteTranslationFactor lam ((finitePoints).symm d) b := by
  rw [compactFiniteSectionOnScheme_deformedFiniteAction]
  exact (hK).parameterRightAction_apply_pair (ofInfinite_projection_mem F) _ _ _ _ _

/-- The same constant-scalar formula in the original matrix coordinates. -/
theorem deformedCompactFiniteAction_matrix_pair (lam : ComplexCharacterParameter F P)
    (d : FiniteAdelicGL F n) (f : A) (a : InfiniteAdelicGL F n) (b : FiniteAdelicGL F n) :
    (deformedCompactFiniteAction F B S lam d f).val.val.val (AdelicGL.pair F n a b) =
      f.val.val.val (AdelicGL.pair F n a (b * d)) *
        (hK).finiteTranslationFactor lam ((finitePoints).symm d) ((finitePoints).symm b) := by
  have he := compactFiniteSectionOnScheme_deformedFiniteAction_pair F B S lam d f
    ((infiniteHomeomorph F n).symm a) ((finitePoints).symm b)
  change (deformedCompactFiniteAction F B S lam d f).val.val.val
    (points (pair F GLG _ _)) = f.val.val.val (points (pair F GLG _ _)) * _ at he
  simpa only [adelicHomeomorph_pair, map_mul, ContinuousMulEquiv.apply_symm_apply] using he

/-- Each finite generator has a finite holomorphic expansion on the original
compact-finite source carrier, in any finite-dimensional linear coordinates. -/
theorem deformedCompactFiniteAction_mem_finiteHolomorphicSections
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [FiniteDimensional ℂ E]
    (e : E →ₗ[ℂ] ComplexCharacterParameter F P) (d : FiniteAdelicGL F n) (f : A) :
    (fun t => deformedCompactFiniteAction F B S (e t) d f) ∈ finiteHolomorphicSections E A := by
  apply FiniteHolomorphicSections.mem_of_injective (compactFiniteSectionOnScheme F B S)
    (compactFiniteSectionOnScheme_injective F B S)
  simp only [compactFiniteSectionOnScheme_deformedFiniteAction]
  exact FiniteHolomorphicSections.mem_iff.mpr ((hK).finiteExpansion_parameterRightAction
    (standardFiniteCompactPoints F n).toSubgroup (standardFiniteCompactPoints F n).isOpen
    (standardFiniteCompactPoints_isCompact F n) (ofFinite_mem_standardCompactPoints F)
    (fun g hg => ((mem_standardCompactPoints_iff F g).mp hg).2) (ofInfinite_projection_mem F)
    e ((finitePoints).symm d) (compactFiniteSectionOnScheme F B S f))

end Langlands.Global.AdelicBlockScalarSections

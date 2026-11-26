import Langlands.Automorphic.GroupSchemeWeilCuspidalTransport
import Langlands.TraceFormula.WeilGeneralLinearCuspidalSummandRealizationStatement
import Langlands.GroupScheme.Rational.GeneralLinearCharacterAdapters
import Langlands.GroupScheme.Rational.CentralSplitTorusCharacterProof
import Langlands.GroupScheme.Rational.CharacterRestrictionReduction

/-! # Scalar split component and form classes for Weil-restricted `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport

open Langlands.Global AdelicGroupPoints AdelicWeilRestriction PositiveRealTorus
open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open Langlands.Automorphic.GroupSchemeFunctions.WeilCuspidalTransport
open Langlands.TraceFormula.AdelicGroupAutomorphism

set_option maxRecDepth 4096
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false

local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (K : Type u) [Field K] [NumberField K] (L : Type u) [Field L] [NumberField L]
  [Algebra K L] [FiniteDimensional K L] (r : ℕ)

local notation "GLK" => GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)
local notation "GLL" => GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of L)
local notation "W" => weilGroup K L GLK
local notation "Z" => Gm (Spec (CommRingCat.of L))
local notation "z" => GeneralLinear.scalarTorus (Fin (r + 1)) (CommRingCat.of L)
local notation "GLA" => GeneralLinearGroupPoints.adelicHomeomorph L (r + 1)

/-- The isomorphism from the Weil restriction of the base change of `GL_n` to
the Weil restriction of the general linear group written over the upper field. -/
def weilIso : W ≅ AffineWeil.groupScheme K L GLL :=
  AffineWeil.mapIso K L (GeneralLinear.baseChangeIso (Fin (r + 1)) (Spec.algebraMap K L))

/-- The point map in the Weil form-class predicate and descent hypothesis. -/
abbrev matrixPoint (x : AdelicGroupPoints K W) : AdelicGL L (r + 1) :=
  GLA (AdelicGroupPoints.map L (AffineWeil.unitBaseChange K L GLK) GLL
    (GeneralLinear.baseChangeIso (Fin (r + 1)) (Spec.algebraMap K L)).hom
    (AdelicGaloisUnit.weilAdelicEquiv K L GLK x))

theorem matrixPoint_eq (x : AdelicGroupPoints K W) :
    matrixPoint K L r x = GLA (ambientEquiv K L (weilIso K L r) x) := by
  rw [ambientEquiv_apply]
  exact congrArg (fun g : AdelicGroupPoints L GLL => GLA g) (adelicPointsEquiv_map K L
    (GeneralLinear.baseChangeIso (Fin (r + 1)) (Spec.algebraMap K L)).hom x).symm

omit [NumberField L] in
/-- The upper scalar torus supplies the split component in positive rank. -/
theorem scalar_isSplitComponent : IsSplitComponent z :=
  GeneralLinear.scalarTorus_isSplitComponent (n := Fin (r + 1)) L

omit [NumberField L] in
theorem scalar_isCentral : IsCentral z :=
  (scalar_isSplitComponent L r).1.2

omit [NumberField L] in
theorem scalarCharacter_injective : Function.Injective (characterRestrict z) :=
  characterRestrict_injective_of_centralSplitTorusCharacter centralSplitTorusCharacter
    (isConnectedReductive_generalLinear L (Fin (r + 1))) (scalar_isSplitComponent L r)

omit [NumberField L] in
theorem scalarCharacter_finiteIndex : (characterRestrict z).range.FiniteIndex :=
  (scalar_isSplitComponent L r).finiteIndex_range_characterRestrict
    (isConnectedReductive_generalLinear L (Fin (r + 1)))

section Quotient

variable (T : CommGroupScheme (Spec (CommRingCat.of K)))
  (i : T.toGrp ⟶ weilGroup K L
    (GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of K)))

local instance : (characterRestrict z).range.FiniteIndex := scalarCharacter_finiteIndex L r

local notation "PositiveMatch" =>
  Subgroup.map (MulEquiv.toMonoidHom
    (ContinuousMulEquiv.toMulEquiv (ambientEquiv K L (weilIso K L r))))
    (imageSubgroup K T W i) = imageSubgroup L Z GLL z

/-- For any lower torus as in the cuspidal statements, its positive subgroup
corresponds to the upper scalar positive subgroup. -/
theorem map_positiveImage (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex] (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i) :
    (imageSubgroup K T W i).map (ambientEquiv K L (weilIso K L r)).toMonoidHom =
      imageSubgroup L Z GLL z := by
  exact map_imageSubgroup_eq K L (G := GLL) (weilIso K L r)
    (T := T) (i := i) hi e (T' := Z) (j := z) (scalarCharacter_injective L r)
    (splitTorus.gmIso _) hc (scalar_isSplitComponent L r)

local notation "QK" => PositiveRationalQuotient K W T i
local notation "QL" => PositiveRationalQuotient L GLL Z z
local notation "mK" => positiveRationalQuotientHaarMeasure K W T i
local notation "mL" => positiveRationalQuotientHaarMeasure L GLL Z z
local notation "CGL" => Langlands.Automorphic.ContinuousRationalFunctions L (r + 1)
local notation "evalGL" => Langlands.Automorphic.ContinuousRationalFunctions.evaluate L (r + 1)
local notation "quotientIso{" h "}" => positiveQuotientEquiv K L (weilIso K L r) h

private theorem upper_pullback_eq_iff (f : CGL) (h : C(QL, ℂ)) :
    continuousGeneralLinearEquiv L (r + 1) (positiveQuotientContinuousPullback L GLL Z z h) = f ↔
      ∀ y : AdelicGroupPoints L GLL, h (LeftCosetSpace.mk _ y) = evalGL f (GLA y) := by
  constructor
  · intro hh y
    have hh' := congrArg (fun f : CGL => evalGL f (GLA y)) hh
    change h (LeftCosetSpace.mk _ ((GLA).symm (GLA y))) = _ at hh'
    rwa [(GLA).symm_apply_apply] at hh'
  · intro hh
    apply Subtype.ext
    apply Subtype.ext
    funext x
    change h (LeftCosetSpace.mk _ ((GLA).symm x)) = evalGL f x
    simpa only [(GLA).apply_symm_apply] using hh ((GLA).symm x)

private theorem quotient_pullback_eq_iff (hpos : PositiveMatch) (f : CGL) (h : C(QL, ℂ)) :
    continuousGeneralLinearEquiv L (r + 1) (positiveQuotientContinuousPullback L GLL Z z h) = f ↔
      ∀ x : AdelicGroupPoints K W,
        h (quotientIso{hpos} (LeftCosetSpace.mk _ x)) = evalGL f (matrixPoint K L r x) := by
  rw [upper_pullback_eq_iff L r]
  simp only [positiveQuotientEquiv_mk, matrixPoint_eq]
  exact (ambientEquiv K L (weilIso K L r)).surjective.forall

/-- A matrix-model form admits a continuous representative on the lower quotient
if and only if it admits one on the upper scalar quotient. -/
theorem descends_iff (hpos : PositiveMatch) (f : CGL) :
    (∃ h : C(QK, ℂ), ∀ x : AdelicGroupPoints K W,
      h (LeftCosetSpace.mk _ x) = evalGL f (matrixPoint K L r x)) ↔
    (∃ h : C(QL, ℂ),
      continuousGeneralLinearEquiv L (r + 1) (positiveQuotientContinuousPullback L GLL Z z h) = f) := by
  let q := quotientIso{hpos}
  simp only [quotient_pullback_eq_iff K L r T i hpos]
  constructor
  · rintro ⟨h, hh⟩
    exact ⟨h.comp ⟨q.symm, q.symm.continuous⟩, fun x => by
      change h (q.symm (q (LeftCosetSpace.mk _ x))) = _
      rw [q.symm_apply_apply, hh]⟩
  · rintro ⟨h, hh⟩
    exact ⟨h.comp ⟨q, q.continuous⟩, hh⟩

/-- The pullback of an upper `L²` class realizes the same matrix-model form on the lower
quotient exactly when the upper class realizes the form on the upper quotient. -/
theorem isWeilFormClass_iff (hi : Function.Injective (characterRestrict i))
    [(characterRestrict i).range.FiniteIndex] (I : Type u) [Fintype I]
    (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of K)) I) (hc : IsCentral i)
    (hpos : PositiveMatch) (f : CGL) (v : Lp ℂ 2 mL) :
    let U := quotientL2Equiv K L (weilIso K L r) hpos hi I e hc
      (scalarCharacter_injective L r) PUnit (splitTorus.gmIso _) (scalar_isCentral L r)
    IsWeilFormClass K L r T i (U v) f ↔ IsGeneralLinearFormClass L r Z z v f := by
  dsimp only
  let q := quotientIso{hpos}
  let U := quotientL2Equiv K L (weilIso K L r) hpos hi I e hc
    (scalarCharacter_injective L r) PUnit (splitTorus.gmIso _) (scalar_isCentral L r)
  change (∃ h : C(QK, ℂ), (∀ x : AdelicGroupPoints K W,
    h (LeftCosetSpace.mk _ x) = evalGL f (matrixPoint K L r x)) ∧
      ((U v : Lp ℂ 2 mK) : QK → ℂ) =ᵐ[mK] h) ↔ _
  unfold IsGeneralLinearFormClass
  simp only [quotient_pullback_eq_iff K L r T i hpos]
  have hrep : ((U v : Lp ℂ 2 mK) : QK → ℂ) =ᵐ[mK] (v : QL → ℂ) ∘ q :=
    coeFn_quotientL2Equiv K L (weilIso K L r) hpos
      hi I e hc (scalarCharacter_injective L r) PUnit (splitTorus.gmIso _) (scalar_isCentral L r) v
  have hae {p : QL → Prop} : (∀ᵐ x ∂mK, p (q x)) ↔ ∀ᵐ y ∂mL, p y :=
    ae_quotient_iff K L (weilIso K L r) hpos
      hi I e hc (scalarCharacter_injective L r) PUnit (splitTorus.gmIso _) (scalar_isCentral L r)
  constructor
  · rintro ⟨h, hh, hv⟩
    refine ⟨h.comp ⟨q.symm, q.symm.continuous⟩, fun x => ?_, ?_⟩
    · change h (q.symm (q (LeftCosetSpace.mk _ x))) = _
      rw [q.symm_apply_apply, hh]
    · apply (hae (p := fun y => v y = h (q.symm y))).mp
      filter_upwards [hrep.symm.trans hv] with x hx
      simpa only [q.symm_apply_apply, Function.comp_apply] using hx
  · rintro ⟨h, hh, hv⟩
    exact ⟨h.comp ⟨q, q.continuous⟩, hh, hrep.trans
      ((hae (p := fun y => v y = h y)).mpr hv)⟩

end Quotient

end Langlands.TraceFormula.WeilGeneralLinearCuspidalTransport

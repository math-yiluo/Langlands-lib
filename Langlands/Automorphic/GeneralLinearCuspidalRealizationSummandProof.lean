import Langlands.Automorphic.RealizationSummandClassMap
import Langlands.Automorphic.CuspidalHilbertOrbitCoefficientProof
import Langlands.Automorphic.CuspidalJointAdmissibility
import Langlands.Automorphic.OperatorUnitaryFormComparison
import Mathlib.Analysis.Calculus.Deriv.Star

/-! # From cuspidal operator realizations to irreducible cuspidal summands

The closure of the descended class map is adelically invariant by analytic continuation of
scalar orbit coefficients. An invariant closed subspace of this closure gives an orthogonal
projection; adding its form to the original inner product and applying uniqueness of the
unitary form proves irreducibility. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry MeasureTheory NumberField
open scoped CategoryTheory.MonObj ComplexInnerProductSpace

set_option autoImplicit false

namespace Langlands.Automorphic.RealizationSummand

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] (r : ℕ)
  (R : CuspidalOperatorRealization F r)

local notation "n" => (r + 1)
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
local notation "HB" => CuspidalHilbertOrbitCoefficient.BandHilbertSpace F r
local notation "J" => OperatorDeterminantSlice.translatedToL2 R.realization R.cuspidal

local instance : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance : AddCommGroup R.Space := Submodule.addCommGroup _

set_option maxHeartbeats 2000000 in
/-- The analytic annihilator argument applied directly to the smooth coefficient map, without
assuming a central character. -/
private theorem band_annihilator (w : HB) (hw : ∀ f : R.Space, ⟪w, J 1 f⟫ = 0)
    (f : R.Space) (g : InfiniteAdelicGL F n) :
    ⟪w, J (AdelicGL.ofInfinite F n g) f⟫ = 0 := by
  let C := CuspidalHilbertOrbitCoefficientProof.coefficientMap R.realization w R.cuspidal
  have hD := CuspidalHilbertOrbitCoefficientProof.coefficientMap_envelopingAction
    R.realization w R.cuspidal
  have hJ := CuspidalHilbertOrbitCoefficient.isJointFinite_of_covariant R w C (fun _ _ => rfl) hD f
  have han := ArchimedeanGL.jointFiniteAnalyticity F n (C f) hJ
  obtain ⟨k, hgk⟩ := ArchimedeanGL.compactComponentCoverage F n g
  have hzero (a : ArchimedeanGL.EnvelopingAlgebra F n) :
      (ArchimedeanGL.envelopingAction F n a (C f)).val k.val = 0 := by
    let b := R.realization.envelopingAction a f
    have h := OperatorDeterminantSlice.inner_translatedToL2_left R w 1
      (R.realization.compactRepresentation k b)
    simp only [OperatorDeterminantSlice.translate_one] at h
    exact (congrArg (fun s : ArchimedeanGL.SmoothFunctions F n => s.val k.val)
      (hD a f).symm).trans
      ((CuspidalHilbertOrbitCoefficient.coefficient_compact R w b k).trans (h.symm.trans (hw _)))
  have hjet := ArchimedeanGL.envelopingZeroJet F n (C f) k.val hzero
  have hz := ArchimedeanGL.analyticMatrixJetUniqueness F n (C f) k.val han hjet g hgk
  rw [OperatorDeterminantSlice.inner_translatedToL2_left]
  exact hz

local instance summandIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

local instance summandSmooth : Smooth (GLG).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

variable (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I] (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [hHaar : (Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  (hdesc : HasPositiveDescent F r T i R)

local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin n)
local notation "aGL" => GeneralLinearGroupPoints.adelicHomeomorph F n
local notation "S" => fullAEL2CuspidalSubmodule F GLG hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F GLG hPD hG T i hi I e hc
local notation "Φ" => classMap F r T i R hdesc hi I e hc hPD
local notation "P" => Submodule.topologicalClosure (LinearMap.range Φ)
local notation "cB" => bandConstant F n T i hi I e hc
local notation "hct" => bandConstant_ne_top_of_descent F r T i R hdesc hi I e hc
local notation "Lw" => bandPullback F r T i hi I e hc hPD hct

include hdesc hHaar in
private theorem bandScalar_ne_zero : (cB).toReal ≠ 0 :=
  ne_of_gt (ENNReal.toReal_pos (bandConstant_ne_zero F n T i hi I e hc (Nat.succ_ne_zero r)) hct)

omit [CompactSpace (AdeleQuotient F)] in
private theorem inner_action (a : AdelicGroupPoints F GLG) (x y : S) :
    ⟪πc a x, πc a y⟫ = ⟪x, y⟫ :=
  (fullAEL2CuspidalRightTranslate F GLG hPD hG T i hi I e hc a).toLinearIsometry.inner_map_map x y

omit [CompactSpace (AdeleQuotient F)] in
private theorem inner_action_right (a : AdelicGroupPoints F GLG) (x y : S) :
    ⟪x, πc a y⟫ = ⟪πc a⁻¹ x, y⟫ := by
  have hcancel : πc a (πc a⁻¹ x) = x := by
    change (πc a * πc a⁻¹) x = x
    rw [← map_mul (πc), mul_inv_cancel, map_one (πc), one_apply_eq_self]
  simpa only [hcancel] using inner_action F r hPD T i hi I e hc a (πc a⁻¹ x) y

set_option maxHeartbeats 1600000 in
/-- The archimedean translates of the original vectors lie in the closure of the class image. -/
private theorem infinite_image_mem_closure (g : InfiniteAdelicGL F n) (f : R.Space) :
    πc ((aGL).symm (AdelicGL.ofInfinite F n g)) (Φ f) ∈ P := by
  apply Langlands.mem_closure_range_of_inner_annihilators
  intro w hw
  have hw' (b : R.Space) : ⟪Lw w, J 1 b⟫ = 0 := by
    have h := inner_bandPullback_translated F r T i R hdesc hi I e hc hPD hct w 1 b
    simp only [map_one, one_apply_eq_self] at h
    exact h.trans ((congrArg ((cB).toReal • ·) (hw b)).trans (smul_zero _))
  have h := (inner_bandPullback_translated F r T i R hdesc hi I e hc hPD hct w
    (AdelicGL.ofInfinite F n g) f).symm.trans (band_annihilator F r R (Lw w) hw' f g)
  exact (smul_eq_zero.mp h).resolve_left (bandScalar_ne_zero F r R T i hi I e hc hdesc)

set_option maxHeartbeats 800000 in
/-- All adelic elements preserve the closure, since a finite translate is already a class
of a source vector and the archimedean translates of such classes stay in the closure. -/
private theorem classClosure_invariant (a : AdelicGroupPoints F GLG) (x : S) (hx : x ∈ P) :
    πc a x ∈ P := by
  have hclosed : IsClosed ((πc a) ⁻¹' (P : Set S)) :=
    (Submodule.isClosed_topologicalClosure (LinearMap.range Φ)).preimage (πc a).continuous
  apply (closure_minimal (t := (πc a) ⁻¹' (P : Set S)) ?_ hclosed) hx
  rintro _ ⟨f, rfl⟩
  let b := aGL a
  have ha : a = (aGL).symm (AdelicGL.ofInfinite F n (AdelicGL.infinite F n b)) *
      (aGL).symm (AdelicGL.ofFinite F n (AdelicGL.finite F n b)) := by
    apply (aGL).injective
    simpa only [map_mul, ContinuousMulEquiv.apply_symm_apply] using
      AdelicGL.eq_ofInfinite_mul_ofFinite F n b
  change πc a (Φ f) ∈ P
  rw [ha, map_mul (πc), mul_apply_eq_comp, ← classMap_finite F r T i R hdesc hi I e hc hPD]
  exact infinite_image_mem_closure F r R hPD T i hi I e hc hdesc _ _

open ArchimedeanGL

/-- The actual adelic point given by the archimedean one-parameter curve. -/
private def adelicCurve (X : RealLieAlgebra F n) (t : ℝ) : AdelicGroupPoints F GLG :=
  (aGL).symm (AdelicGL.ofInfinite F n (infiniteOneParameter F n X t))

local notation "curve" => adelicCurve F r

omit [CompactSpace (AdeleQuotient F)] hHaar in
private theorem adelicCurve_neg (X : RealLieAlgebra F n) (t : ℝ) :
    curve X (-t) = (curve X t)⁻¹ := by
  unfold adelicCurve infiniteOneParameter
  rw [← map_inv, ← map_inv, ← map_inv]
  congr 3
  apply Units.ext
  change NormedSpace.exp ((-t) • realLieAlgebraToMatrix F n X) =
    NormedSpace.exp (-(t • realLieAlgebraToMatrix F n X))
  rw [neg_smul]

set_option maxHeartbeats 800000 in
/-- The quotient orbit coefficient has the source real Lie operator as its weak derivative. -/
private theorem hasDerivAt_classCoefficient (w : S) (X : RealLieAlgebra F n) (f : R.Space) :
    HasDerivAt (fun t => ⟪w, πc (curve X t) (Φ f)⟫)
      ⟪w, Φ (R.realization.lieOperator X f)⟫ 0 := by
  let C := CuspidalHilbertOrbitCoefficientProof.coefficientMap R.realization (Lw w) R.cuspidal
  have hC (b : R.Space) (g : InfiniteAdelicGL F n) :
      (C b).val g = (cB).toReal • ⟪w, πc ((aGL).symm (AdelicGL.ofInfinite F n g)) (Φ b)⟫ :=
    (OperatorDeterminantSlice.inner_translatedToL2_left R (Lw w) (AdelicGL.ofInfinite F n g) b).symm.trans
      (inner_bandPullback_translated F r T i R hdesc hi I e hc hPD hct w _ b)
  have hd := hasDerivAt_smooth_oneParameter F n (C f) X 1 0
  simp only [one_mul, infiniteOneParameter_zero] at hd
  have hlie : smoothDifferential F n X (C f) = C (R.realization.lieOperator X f) :=
    (CuspidalHilbertOrbitCoefficientProof.coefficientMap_lieOperator
      R.realization (Lw w) R.cuspidal X f).symm
  rw [hlie] at hd
  have hd' : HasDerivAt (fun t => (cB).toReal • ⟪w, πc (curve X t) (Φ f)⟫)
      ((cB).toReal • ⟪w, Φ (R.realization.lieOperator X f)⟫) 0 := by
    simpa only [hC, adelicCurve, map_one, one_apply_eq_self] using hd
  simpa only [Pi.smul_def, smul_smul,
    inv_mul_cancel₀ (bandScalar_ne_zero F r R T i hi I e hc hdesc), one_smul]
    using hd'.const_smul ((cB).toReal)⁻¹

set_option maxHeartbeats 1600000 in
/-- Weak differentiation suffices for skew-invariance of a symmetric commuting form. -/
private theorem classForm_skew (B : S →L[ℂ] S)
    (hcomm : ∀ a x, B (πc a x) = πc a (B x))
    (hsymm : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫)
    (X : RealLieAlgebra F n) (f g : R.Space) :
    ⟪B (Φ (R.realization.lieOperator X f)), Φ g⟫ +
      ⟪B (Φ f), Φ (R.realization.lieOperator X g)⟫ = 0 := by
  have heq : (fun t : ℝ => star ⟪B (Φ g), πc (curve X (-t)) (Φ f)⟫) =
      fun t => ⟪B (Φ f), πc (curve X t) (Φ g)⟫ := by
    funext t
    calc
      _ = ⟪πc (curve X (-t)) (Φ f), B (Φ g)⟫ := by
        simpa only [starRingEnd_apply] using
          inner_conj_symm (𝕜 := ℂ) (πc (curve X (-t)) (Φ f)) (B (Φ g))
      _ = ⟪B (πc (curve X (-t)) (Φ f)), Φ g⟫ := (hsymm _ _).symm
      _ = ⟪πc (curve X (-t)) (B (Φ f)), Φ g⟫ :=
        congrArg (fun v : S => ⟪v, Φ g⟫) (hcomm _ _)
      _ = _ := by
        rw [adelicCurve_neg F r]
        exact (inner_action_right F r hPD T i hi I e hc (curve X t) _ _).symm
  have hdg := hasDerivAt_classCoefficient F r R hPD T i hi I e hc hdesc (B (Φ f)) X g
  have hdf := hasDerivAt_classCoefficient F r R hPD T i hi I e hc hdesc (B (Φ g)) X f
  have hn : HasDerivAt (fun t : ℝ => -t) (-1) 0 := (hasDerivAt_id (0 : ℝ)).neg
  have hd := (hdf.scomp_of_eq (0 : ℝ) hn neg_zero.symm).star
  have hd' : HasDerivAt (fun t => ⟪B (Φ f), πc (curve X t) (Φ g)⟫)
      (-⟪B (Φ (R.realization.lieOperator X f)), Φ g⟫) 0 := by
    have hs : star ⟪B (Φ g), Φ (R.realization.lieOperator X f)⟫ =
        ⟪B (Φ (R.realization.lieOperator X f)), Φ g⟫ := by
      simpa only [starRingEnd_apply] using
        (inner_conj_symm (𝕜 := ℂ) (Φ (R.realization.lieOperator X f)) (B (Φ g))).trans
          (hsymm (Φ (R.realization.lieOperator X f)) (Φ g)).symm
    simpa only [Function.comp_def, neg_smul, one_smul, star_neg, hs, heq] using hd
  rw [hdg.unique hd', add_neg_cancel]

set_option maxHeartbeats 1600000 in
/-- Pull a symmetric commuting operator dominating the identity back to a full unitary form. -/
private def unitaryFormOf (B : S →L[ℂ] S)
    (hcomm : ∀ a x, B (πc a x) = πc a (B x))
    (hsymm : ∀ x y, ⟪B x, y⟫ = ⟪x, B y⟫)
    (hpos : ∀ x, (⟪x, x⟫ : ℂ).re ≤ (⟪B x, x⟫ : ℂ).re) : R.realization.UnitaryForm := by
  have hInv (a : AdelicGroupPoints F GLG) (x y : S) :
      ⟪B (πc a x), πc a y⟫ = ⟪B x, y⟫ :=
    (congrArg (fun v : S => ⟪v, πc a y⟫) (hcomm a x)).trans
      (inner_action F r hPD T i hi I e hc a (B x) y)
  exact {
    finiteForm := {
      inner := fun f g => ⟪B (Φ f), Φ g⟫
      conj_inner_symm := fun f g =>
        (inner_conj_symm (𝕜 := ℂ) (Φ f) (B (Φ g))).trans (hsymm (Φ f) (Φ g)).symm
      re_inner_nonneg := fun f => (inner_self_nonneg (𝕜 := ℂ) (x := Φ f)).trans (hpos (Φ f))
      add_left := fun f g h => by simp only [map_add Φ, map_add B, inner_add_left]
      smul_left := fun f g z => by simp only [map_smul Φ, map_smul B, inner_smul_left]
      definite := fun f hf => by
        have h := (hpos (Φ f)).trans_eq (congrArg Complex.re hf)
        exact classMap_injective F r T i R hdesc hi I e hc hPD
          (((re_inner_self_nonpos (𝕜 := ℂ)).mp h).trans (map_zero Φ).symm)
      invariant := fun a f g =>
        (congrArg₂ (fun x y : S => ⟪B x, y⟫)
          (classMap_finite F r T i R hdesc hi I e hc hPD a f)
          (classMap_finite F r T i R hdesc hi I e hc hPD a g)).trans (hInv _ _ _) }
    compact_invariant := fun k f g =>
      (congrArg₂ (fun x y : S => ⟪B x, y⟫)
        (classMap_compact F r T i R hdesc hi I e hc hPD k f)
        (classMap_compact F r T i R hdesc hi I e hc hPD k g)).trans (hInv _ _ _)
    real_skew := classForm_skew F r R hPD T i hi I e hc hdesc B hcomm hsymm }

set_option maxHeartbeats 1600000 in
omit [CompactSpace (AdeleQuotient F)] in
/-- An invariant subspace's projection commutes with the unitary action: its orthogonal
complement is invariant, using the inverse action. -/
private theorem projection_commutes (U : Submodule ℂ S) [U.HasOrthogonalProjection]
    (hinv : ∀ a, ∀ x ∈ U, πc a x ∈ U) (a : AdelicGroupPoints F GLG) (x : S) :
    U.starProjection (πc a x) = πc a (U.starProjection x) := by
  refine Submodule.eq_starProjection_of_mem_orthogonal
    (hinv a _ (U.starProjection_apply_mem x)) ?_
  have h (y : S) (hy : y ∈ U) : ⟪y, πc a (x - U.starProjection x)⟫ = 0 :=
    (inner_action_right F r hPD T i hi I e hc a y _).trans
      ((Submodule.mem_orthogonal U _).mp (U.sub_starProjection_mem_orthogonal x) _
        (hinv a⁻¹ y hy))
  exact (Submodule.mem_orthogonal U _).mpr (fun y hy => by
    simpa only [map_sub (πc a)] using h y hy)

set_option maxHeartbeats 2500000 in
/-- Compare the original form with the form given by one plus the projection. This shifts a
possibly degenerate positive projector form into the range of the unitary-form comparison. -/
private theorem classClosure_minimal (U : Submodule ℂ S) (hle : U ≤ P)
    (hclosed : IsClosed (U : Set S)) (hinv : ∀ a, ∀ x ∈ U, πc a x ∈ U) :
    U = ⊥ ∨ U = P := by
  let _ : CompleteSpace U := hclosed.completeSpace_coe
  let E : S →L[ℂ] S := U.starProjection
  let b := unitaryFormOf F r R hPD T i hi I e hc hdesc 1
    (by intro a x; simp only [one_apply_eq_self])
    (by intro x y; simp only [one_apply_eq_self])
    (by intro x; simp only [one_apply_eq_self]; exact le_rfl)
  let c := unitaryFormOf F r R hPD T i hi I e hc hdesc (1 + E)
    (by
      intro a x
      simp only [add_apply, one_apply_eq_self, map_add (πc a),
        projection_commutes F r hPD T i hi I e hc U hinv a x, E])
    (by
      intro x y
      simp only [add_apply, one_apply_eq_self, inner_add_left, inner_add_right,
        U.inner_starProjection_left_eq_right x y, E])
    (by
      intro x
      have hn : 0 ≤ (⟪E x, x⟫ : ℂ).re :=
        (sq_nonneg _).trans_eq (U.re_inner_starProjection_eq_normSq x).symm
      simp only [add_apply, one_apply_eq_self, inner_add_left, Complex.add_re]
      exact le_add_of_nonneg_right hn)
  obtain ⟨a, _, h⟩ := b.exists_pos_scalar c R.irreducible R.isJointlyAdmissible
  have hform (f g : R.Space) : ⟪Φ f + E (Φ f), Φ g⟫ = (a : ℂ) * ⟪Φ f, Φ g⟫ := by
    have hf := h f g
    change ⟪((1 : S →L[ℂ] S) + E) (Φ f), Φ g⟫ =
      (a : ℂ) * ⟪(1 : S →L[ℂ] S) (Φ f), Φ g⟫ at hf
    simpa only [add_apply, one_apply_eq_self] using hf
  have hmem (f : R.Space) : Φ f ∈ P := Submodule.le_topologicalClosure _ ⟨f, rfl⟩
  have hpoint (f : R.Space) : Φ f + E (Φ f) = (a : ℂ) • Φ f := by
    let v := Φ f + E (Φ f) - (a : ℂ) • Φ f
    have hv : v ∈ P :=
      (P).sub_mem ((P).add_mem (hmem f) (hle (U.starProjection_apply_mem (Φ f))))
        ((P).smul_mem _ (hmem f))
    have hv' : v ∈ Pᗮ := by
      rw [Submodule.orthogonal_closure]
      refine (Submodule.mem_orthogonal' _ v).mpr ?_
      rintro _ ⟨g, rfl⟩
      have hs : ⟪(a : ℂ) • Φ f, Φ g⟫ = (a : ℂ) * ⟪Φ f, Φ g⟫ :=
        (inner_smul_left (𝕜 := ℂ) (Φ f) (Φ g) (a : ℂ)).trans
          (congrArg (· * ⟪Φ f, Φ g⟫) (Complex.conj_ofReal a))
      simp only [v, inner_sub_left, hs, hform f g, sub_self]
    exact sub_eq_zero.mp (inner_self_eq_zero (𝕜 := ℂ) |>.mp
      ((Submodule.mem_orthogonal' P v).mp hv' v hv))
  let z : ℂ := (a : ℂ) - 1
  have hE (f : R.Space) : E (Φ f) = z • Φ f := by
    calc
      E (Φ f) = Φ f + E (Φ f) - Φ f := (add_sub_cancel_left _ _).symm
      _ = (a : ℂ) • Φ f - (1 : ℂ) • Φ f :=
        congrArg₂ (· - ·) (hpoint f) (one_smul ℂ (Φ f)).symm
      _ = z • Φ f := (sub_smul (a : ℂ) (1 : ℂ) (Φ f)).symm
  by_cases hz : z = 0
  · left
    have hP0 : P ≤ Uᗮ := by
      refine Submodule.topologicalClosure_minimal _ ?_ U.isClosed_orthogonal
      rintro _ ⟨f, rfl⟩
      apply (U.starProjection_apply_eq_zero_iff).mp
      simpa only [hz, zero_smul] using hE f
    exact (Submodule.eq_bot_iff U).mpr (fun x hx =>
      (inner_self_eq_zero (𝕜 := ℂ)).mp ((Submodule.mem_orthogonal' U x).mp (hP0 (hle hx)) x hx))
  · right
    refine le_antisymm hle (Submodule.topologicalClosure_minimal _ ?_ hclosed)
    rintro _ ⟨f, rfl⟩
    have h := U.smul_mem z⁻¹ (show E (Φ f) ∈ U from U.starProjection_apply_mem (Φ f))
    simpa only [hE f, smul_smul, inv_mul_cancel₀ hz, one_smul] using h

private theorem classClosure_ne_bot : P ≠ ⊥ := by
  obtain ⟨f, hf⟩ := exists_ne (0 : R.Space)
  intro hP
  have h : Φ f ∈ P := Submodule.le_topologicalClosure _ ⟨f, rfl⟩
  rw [hP] at h
  exact hf (classMap_injective F r T i R hdesc hi I e hc hPD
    ((Submodule.mem_bot ℂ).mp h |>.trans (map_zero Φ).symm))

end Langlands.Automorphic.RealizationSummand

namespace Langlands.Automorphic.GroupSchemeFunctions

open RealizationSummand

set_option maxHeartbeats 1000000 in
/-- Positive-central descent sends an irreducible cuspidal operator realization to a dense
subspace of an irreducible closed cuspidal `L²` summand. -/
theorem generalLinearCuspidalRealizationSummand :
    GeneralLinearCuspidalRealizationSummandStatement.{u} := by
  intro F _ _ _ r hPD T i hi _ I _ e hc _
  dsimp only
  intro R hdesc
  let Φ := classMap F r T i R hdesc hi I e hc hPD
  exact ⟨(LinearMap.range Φ).topologicalClosure, Φ,
    ⟨classClosure_ne_bot F r R hPD T i hi I e hc hdesc,
      Submodule.isClosed_topologicalClosure (LinearMap.range Φ),
      classClosure_invariant F r R hPD T i hi I e hc hdesc,
      classClosure_minimal F r R hPD T i hi I e hc hdesc⟩,
    isGeneralLinearFormClass_classMap F r T i R hdesc hi I e hc hPD, rfl⟩

end Langlands.Automorphic.GroupSchemeFunctions

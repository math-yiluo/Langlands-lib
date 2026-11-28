import Langlands.Global.AdelicWeylConeTruncationRay

/-! # Fourier evaluation of the identity Weyl terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry Filter MeasureTheory Set TensorProduct
open scoped CategoryTheory.MonObj Classical ContDiff NNReal Topology

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints Langlands.Analysis ImaginaryAxis
  Langlands.Aubert.General.RationalPointFamily

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (P : StandardIndex F G fam.i fam.ν)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Roots" J:max => fam.relativeSimpleRoots J
local notation "Param" J:max => RealCharacterParameter F (fam.P J)
local notation "W" => relativeWeylGroup fam.i

private theorem realWeylParameter_pairing_of_class_one
    (a : normalizerPoints fam.i) (c : fam.M P ⟶ fam.M P) (π : fam.P P ⟶ fam.M P)
    (hπ : fam.l P ≫ π = 𝟙 (fam.M P))
    (hc : IsWeylConjugation (fam.p P) (fam.l P) (fam.p P) (fam.l P) a.val c)
    (ha : (QuotientGroup.mk a : W) = 1) (y : Param P) (v : V fam.T) :
    realParameterPairing F (fam.P P) (realWeylParameter (fam.l P) c π y) (fam.splitDual P v) =
      realParameterPairing F (fam.P P) y (fam.splitDual P v) := by
  let : IsClosedImmersion (fam.p P).hom.hom.left := fam.isClosedImmersion_p P
  let : IsAffine (fam.P P).X.left := isAffine_of_isAffineHom (fam.p P).hom.hom.left
  have hp : Mono (fam.p P).hom.hom := Over.mono_of_mono_left _
  let : Mono (fam.p P) := (Grp.forget _).mono_of_mono_map (f := fam.p P) hp
  have hreal (z : Param P) :
      parameterRealPart F (fam.P P) (realToComplexParameter (fam.P P) z) = z := by
    induction z using TensorProduct.inductionOn with
    | tmul t χ => rw [realToComplexParameter_tmul, parameterRealPart_tmul, Complex.ofReal_re]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hweyl :
      weylParameter (fam.l P) c π (realToComplexParameter (fam.P P) y) =
        realToComplexParameter (fam.P P) (realWeylParameter (fam.l P) c π y) := by
    induction y using TensorProduct.inductionOn with
    | tmul t χ => rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  have h := eisensteinAmbientWeylParameter F G (fam.P P) (fam.M P) (fam.P P) (fam.M P)
    fam.T fam.i (fam.p P) (fam.l P) (fam.p P) (fam.l P) (fam.torus P) (fam.torus P) π a c
    (fam.torus_comp P) (fam.torus_comp P) hπ hc (realToComplexParameter (fam.P P) y)
  rw [hweyl, hreal, hreal, ha, map_one] at h
  change fam.chamberEmbedding P (realWeylParameter (fam.l P) c π y) =
    fam.chamberEmbedding P y at h
  rw [fam.realParameterPairing_splitDual P, fam.realParameterPairing_splitDual P]
  exact congrArg (fun z => pair fam.T z v) h

private theorem coordinatePolynomialPointEvaluation_mul_left
    {Index : Type*} [Fintype Index] (p : MvPolynomial Index ℂ) (ξ : Index → ℝ)
    (a : (Index → ℝ) → ℂ) (ha : ContDiff ℝ ∞ a) (b : ℂ) :
    coordinatePolynomialPointEvaluation p ξ (fun x => b * a x) =
      b * coordinatePolynomialPointEvaluation p ξ a := by
  unfold coordinatePolynomialPointEvaluation
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  unfold fourierPolynomialPointEvaluation
  rw [show (fun x => b * a x) ∘ _ = b • (a ∘ _) from rfl,
    iteratedFDeriv_const_smul_apply
      ((ha.comp (ContinuousLinearEquiv.contDiff _)).of_le (by simp)).contDiffAt]
  simp only [smul_apply, smul_eq_mul]
  ring

/-- Reindex coroot coordinates along equality of the two standard parabolics. -/
def reindexCorootCoordinates {Q : Idx} (h : Q = P)
    (x : Roots P → ℝ) (α : Roots Q) : ℝ :=
  x ⟨α.val, congrArg fam.relativeSimpleRoots h ▸ α.property⟩

omit [NumberField F] in
@[simp]
theorem reindexCorootCoordinates_rfl (x : Roots P → ℝ) :
    fam.reindexCorootCoordinates P rfl x = x := rfl

private theorem identityChart_apply {Q : Idx} (hQ : Q = P)
    (relative : (Roots P → ℝ) ≃ₗ[ℝ] ↥(relativeParameterSpace (F := F) (fam.p P)))
    (hrelative : ∀ x α, realParameterPairing F (fam.P P) (relative x).val (fam.relativeCoroot P α) = x α)
    (a : normalizerPoints fam.i) (c : fam.M Q ⟶ fam.M P) (π : fam.P Q ⟶ fam.M Q)
    (hπ : fam.l Q ≫ π = 𝟙 (fam.M Q))
    (hc : IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) a.val c)
    (ha : (QuotientGroup.mk a : W) = 1)
    (e : (Roots P → ℝ) ≃L[ℝ] (Roots Q → ℝ))
    (he : ∀ x α, e x α = realParameterPairing F (fam.P Q)
      (realWeylParameter (fam.l P) c π (relative x).val) (fam.relativeCoroot Q α)) :
    ∀ x α, e x α = fam.reindexCorootCoordinates P hQ x α := by
  subst Q
  intro x α
  rw [he, relativeCoroot, fam.realWeylParameter_pairing_of_class_one P a c π hπ hc ha]
  exact hrelative x α

omit [NumberField F] in
private theorem identityChart_measure_and_phase {Q : Idx} (hQ : Q = P)
    (e : (Roots P → ℝ) ≃L[ℝ] (Roots Q → ℝ))
    (he : ∀ x α, e x α = fam.reindexCorootCoordinates P hQ x α)
    (spectral : Measure (Roots P → ℝ)) [spectral.IsAddHaarMeasure] (C : ℝ≥0)
    (hMap : Measure.map e spectral = C • coordinateSpectralMeasure (Roots Q)) :
    C = Measure.addHaarScalarFactor spectral (coordinateSpectralMeasure (Roots P)) ∧
    ∀ x, coordinateFourierPhase x ∘ e.symm =
      coordinateFourierPhase (fam.reindexCorootCoordinates P hQ x) := by
  subst Q
  have heq : e = ContinuousLinearEquiv.refl ℝ (Roots P → ℝ) :=
    ContinuousLinearEquiv.ext (funext (fun x => funext (he x)))
  subst e
  change Measure.map id spectral = _ at hMap
  rw [Measure.map_id] at hMap
  refine ⟨?_, fun _ => rfl⟩
  subst spectral
  simp [smul_eq_mul]

private theorem coordinateFourierPhase_eq_coroot_exp
    (Q : Idx) (x : Roots Q → ℝ) (freq : Param Q) :
    coordinateFourierPhase x
        (fun α => realParameterPairing F (fam.P Q) freq (fam.relativeCoroot Q α)) =
      Complex.exp (∑ α, (x α : ℂ) *
        fam.corootValue Q (-imaginaryParameter F (fam.P Q) freq) α) := by
  unfold coordinateFourierPhase
  apply congrArg Complex.exp
  rw [Complex.ofReal_neg, Complex.ofReal_sum, ← Finset.sum_neg_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  simp only [corootValue, map_neg, LinearMap.neg_apply,
    ChamberDecay.complexParameterPairing_imaginaryParameter, Complex.ofReal_mul]
  ring

variable {n : ℕ} {Label : Type*} [Fintype Label]
  (full : (Fin n → ℝ) ≃ₗ[ℝ] (RealCharacterParameter F (fam.P P)))
  (spectral : Measure (fam.relativeSimpleRoots P → ℝ))
  (Q : Label → StandardIndex F G fam.i fam.ν) (a : Label → normalizerPoints fam.i)
  (c : ∀ l, fam.M (Q l) ⟶ fam.M P) (π : ∀ l, fam.P (Q l) ⟶ fam.M (Q l))

local notation "Keep" l:max => (Q l = P ∧ (QuotientGroup.mk (a l) : W) = 1)

/-- The exponential polynomial for a retained label, reindexed to the inducing parabolic. -/
def identityWeylSpatialTerm {J : Idx} (h : J = P)
    (freq : Param J) (p : MvPolynomial (Roots J) ℂ) (β : ℂ) (x : Roots P → ℝ) : ℂ :=
  let y : Roots J → ℂ := fun α => fam.reindexCorootCoordinates P h x α
  β * (Complex.exp (∑ α, y α * fam.corootValue J (-imaginaryParameter F (fam.P J) freq) α) *
    p.eval y)

/-- The coroot-coordinate exponential polynomial contributed by identity Weyl labels. -/
def identityWeylSpatialSum
    (freq : ∀ l : Label, RealCharacterParameter F (fam.P (Q l)))
    (p : ∀ l : Label, MvPolynomial (fam.relativeSimpleRoots (Q l)) ℂ) (β : Label → ℂ)
    (x : fam.relativeSimpleRoots P → ℝ) : ℂ :=
  ∑ l : {l : Label // Keep l},
    fam.identityWeylSpatialTerm P l.property.1 (freq l.val) (p l.val) (β l.val) x

/-- A limit on compact spectral tests with a finite germ support and a specified
spatial exponential polynomial. -/
def HasIdentityFourierEvaluation
    (onAxis : (fam.relativeSimpleRoots P → ℝ) → (Fin n → ℂ)) (C : ℝ≥0)
    (freq : ∀ l, RealCharacterParameter F (fam.P (Q l)))
    (p : ∀ l, MvPolynomial (fam.relativeSimpleRoots (Q l)) ℂ) (β : Label → ℂ)
    (representative : ℕ → (Fin n → ℂ) → ℂ) : Prop :=
  ∃ (S : Finset (fam.relativeSimpleRoots P → ℝ))
    (D : ((fam.relativeSimpleRoots P → ℝ) → ℂ) → ℂ),
    (∀ f g, (∀ y ∈ S, f =ᶠ[𝓝 y] g) → D f = D g) ∧
    (∀ f : (fam.relativeSimpleRoots P → ℝ) → ℂ, ContDiff ℝ ∞ f → HasCompactSupport f →
      (∀ᶠ k : ℕ in atTop, Integrable (fun y => f y * representative k (onAxis y)) spectral) ∧
        Tendsto (fun (k : ℕ) => ∫ y, f y * representative k (onAxis y) ∂spectral) atTop
          (𝓝 (((C : ℝ) : ℂ) * D f))) ∧
    ∀ x : fam.relativeSimpleRoots P → ℝ,
      D (coordinateFourierPhase x) = fam.identityWeylSpatialSum P Q a freq p β x

/-- In the inducing parabolic's coroot coordinates, the surviving identity Weyl labels
use one common spectral Haar factor. If their weights are constant on the relative
axis, the limiting germ functional on a negative Fourier phase is their weighted
sum of exponential polynomials. -/
def WeylIdentityFourierEvaluationStatement : Prop :=
  ∀ [spectral.IsAddHaarMeasure],
    (∀ l, fam.l (Q l) ≫ π l = 𝟙 (fam.M (Q l))) →
    (∀ l, IsWeylConjugation (fam.p P) (fam.l P) (fam.p (Q l)) (fam.l (Q l)) (a l).val (c l)) →
    (∀ l, schemeWeylCharacterAction fam.i (QuotientGroup.mk (a l) : W)⁻¹ '' (Q l).val = P.val) →
    ∃ (relative : (fam.relativeSimpleRoots P → ℝ) ≃ₗ[ℝ]
          ↥(relativeParameterSpace (F := F) (fam.p P)))
      (C : ℝ≥0),
      (∀ x α, realParameterPairing F (fam.P P) (relative x).val (fam.relativeCoroot P α) = x α) ∧
      0 < C ∧
      ∀ (T₀ T : V fam.T) (freq : ∀ l, RealCharacterParameter F (fam.P (Q l)))
        (p : ∀ l, MvPolynomial (fam.relativeSimpleRoots (Q l)) ℂ)
        (weight : Label → (Fin n → ℂ) → ℂ) (β : Label → ℂ)
        (representative : ℕ → (Fin n → ℂ) → ℂ),
        (∀ α ∈ simpleRelativeRoots fam.i fam.ν, 0 < eval fam.T α T) →
        fam.IsWeylConeRayRepresentative P full Q c π T₀ T freq p weight representative →
        let onAxis : (fam.relativeSimpleRoots P → ℝ) → (Fin n → ℂ) :=
          fun y => imaginarySlice (full.symm (relative y).val)
        (∀ l, Keep l → ∀ y, weight l (onAxis y) = β l) →
        fam.HasIdentityFourierEvaluation P spectral Q a onAxis C freq p β representative

theorem weylIdentityFourierEvaluation :
    fam.WeylIdentityFourierEvaluationStatement P full spectral Q a c π := by
  classical
  intro _ hπ hconj hmatch
  obtain ⟨relative, hrelative⟩ := fam.relativeSpectralCorootChart P
  obtain ⟨e, C, he, hMap, _, hLimit⟩ :=
    fam.weylConeTruncationRay_withHaar P full relative spectral Q a c π hπ hconj hmatch
  let C₀ := Measure.addHaarScalarFactor spectral (coordinateSpectralMeasure (Roots P))
  refine ⟨relative, C₀, hrelative, Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _, ?_⟩
  intro T₀ T freq p weight β representative hT hReg onAxis hWeight
  let ξ (l : Label) (α : Roots (Q l)) : ℝ :=
    realParameterPairing F (fam.P (Q l)) (freq l) (fam.relativeCoroot (Q l) α)
  let w (l : Label) (f : (Roots P → ℝ) → ℂ) (y : Roots (Q l) → ℝ) :=
    f ((e l).symm y) * weight l (onAxis ((e l).symm y))
  let d (l : Label) (f : (Roots P → ℝ) → ℂ) :=
    coordinatePolynomialPointEvaluation (p l) (ξ l) (w l f)
  let point (l : {l // Keep l}) := (e l.val).symm (ξ l.val)
  let S := Finset.univ.image point
  let D (f : (Roots P → ℝ) → ℂ) : ℂ := ∑ l : {l // Keep l}, d l.val f
  have hId (l : {l // Keep l}) :
      C l.val = C₀ ∧ ∀ x, coordinateFourierPhase x ∘ (e l.val).symm =
        coordinateFourierPhase (fam.reindexCorootCoordinates P l.property.1 x) := by
    have h := fam.identityChart_apply P l.property.1 relative hrelative (a l.val) (c l.val) (π l.val)
      (hπ l.val) (hconj l.val) l.property.2 (e l.val) (he l.val)
    exact fam.identityChart_measure_and_phase P l.property.1 (e l.val) h spectral (C l.val) (hMap l.val)
  refine ⟨S, D, ?_, ?_, ?_⟩
  · intro f g hfg
    refine Finset.sum_congr rfl fun l _ => ?_
    apply (coordinatePolynomialFourierEvaluation (p l.val) (ξ l.val)).1
    have hpt : point l ∈ S := Finset.mem_image_of_mem point (Finset.mem_univ l)
    have hcont : Tendsto (e l.val).symm (𝓝 (ξ l.val)) (𝓝 (point l)) :=
      (e l.val).symm.continuous.continuousAt
    filter_upwards [hcont.eventually (hfg (point l) hpt)] with y hy
    simp only [w, hy]
  · intro f hf hfs
    obtain ⟨hInt, hLim⟩ := hLimit T₀ T freq p weight representative hT hReg f hf hfs
    refine ⟨hInt, ?_⟩
    have hSum :
        (∑ l ∈ Finset.univ.filter (fun l => Keep l), ((C l : ℝ) : ℂ) * d l f) =
          ((C₀ : ℝ) : ℂ) * D f := by
      dsimp only [D]
      rw [Finset.sum_subtype (p := fun l => Keep l) _ (by simp)
        (fun l : Label => ((C l : ℝ) : ℂ) * d l f), Finset.mul_sum]
      exact Finset.sum_congr rfl fun l _ => by rw [(hId l).1]
    change Tendsto _ atTop (𝓝 (∑ l ∈ Finset.univ.filter (fun l => Keep l),
      ((C l : ℝ) : ℂ) * d l f)) at hLim
    rwa [hSum] at hLim
  · intro x
    unfold identityWeylSpatialSum identityWeylSpatialTerm
    refine Finset.sum_congr rfl fun l _ => ?_
    let y := fam.reindexCorootCoordinates P l.property.1 x
    have hw : w l.val (coordinateFourierPhase x) =
        fun z => β l.val * coordinateFourierPhase y z := by
      funext z
      change (coordinateFourierPhase x ∘ (e l.val).symm) z *
        weight l.val (onAxis ((e l.val).symm z)) = _
      rw [(hId l).2 x, hWeight l.val l.property, mul_comm]
    change coordinatePolynomialPointEvaluation (p l.val) (ξ l.val) (w l.val (coordinateFourierPhase x)) = _
    rw [hw, coordinatePolynomialPointEvaluation_mul_left _ _ _ (contDiff_coordinateFourierPhase y),
      (coordinatePolynomialFourierEvaluation (p l.val) (ξ l.val)).2.2]
    change β l.val * (_ * coordinateFourierPhase y (fun α =>
      realParameterPairing F (fam.P (Q l.val)) (freq l.val) (fam.relativeCoroot (Q l.val) α))) = _
    rw [fam.coordinateFourierPhase_eq_coroot_exp, mul_comm ((p l.val).eval _)]

end Langlands.Global.StandardParabolicFamily

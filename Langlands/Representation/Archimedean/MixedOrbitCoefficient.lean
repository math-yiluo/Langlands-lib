import Langlands.Representation.Archimedean.SmoothUnitActionDerivative
import Langlands.Global.ArchimedeanJointFiniteAnalyticityProof
import Langlands.Global.ArchimedeanEnvelopingJetProof
import Langlands.Global.ArchimedeanAnalyticJetProof
import Langlands.Algebra.LieCasimir

/-! # Scalar orbit coefficients transported to the mixed archimedean matrix model -/

noncomputable section

open Filter Set
open scoped Classical Manifold ContDiff Topology Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean.MixedOrbit

open Langlands.Global Langlands.Global.ArchimedeanGL
open Langlands.Analysis (hasDerivAt_iff_tendsto_slope_tvs)

variable (K : Type*) [Field K] [NumberField K] (n : ℕ)
  {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A] [FiniteDimensional ℝ A]
  (ψ : ArchimedeanMatrix K n ≃ₐ[ℝ] A)
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] (R : Aˣ →* (E →L[ℂ] E))

local notation "𝓜" => 𝓘(ℝ, A)
local notation "D" => DerivativeSmoothVectors 𝓜 R
local notation "ε" => DerivativeSmoothVectors.derivativeCLM 𝓜 R []

/-- The algebra equivalence as a continuous real linear equivalence. -/
def algCLE : ArchimedeanMatrix K n ≃L[ℝ] A := ψ.toLinearEquiv.toContinuousLinearEquiv

omit [CompleteSpace A] [FiniteDimensional ℝ A] in
@[simp]
theorem algCLE_apply (X : ArchimedeanMatrix K n) : algCLE K n ψ X = ψ X := rfl

/-- The induced map of matrix units. -/
def unitsMap : ArchimedeanGL K n →* Aˣ := Units.map ψ.toRingEquiv.toRingHom.toMonoidHom

omit [NumberField K] [CompleteSpace A] [FiniteDimensional ℝ A] in
@[simp]
theorem unitsMap_val (g : ArchimedeanGL K n) :
    (unitsMap K n ψ g : A) = ψ (g : ArchimedeanMatrix K n) := rfl

omit [FiniteDimensional ℝ A] in
theorem contMDiff_unitsMap :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓜 ∞ (unitsMap K n ψ) := by
  apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓜 ∞
    (fun g : ArchimedeanGL K n => algCLE K n ψ (g : ArchimedeanMatrix K n))
  exact (algCLE K n ψ).contDiff.contMDiff.comp Units.contMDiff_val

/-- The scalar orbit coefficient of a genuine smooth vector, as an actual smooth function
on the completion-based general linear group. -/
def orbitCoefficient (ℓ : E →L[ℂ] ℂ) : D →ₗ[ℂ] SmoothFunctions K n where
  toFun v := ⟨fun x => ℓ (R (unitsMap K n ψ (archimedeanGLCoordinates K n x)) (ε v)), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞ (fun x : ArchimedeanGL K n =>
      ℓ (R (unitsMap K n ψ (archimedeanGLCoordinates K n
        ((archimedeanGLCoordinates K n).symm x))) (ε v)))
    simp only [ContinuousMulEquiv.apply_symm_apply]
    exact (ℓ.restrictScalars ℝ).contDiff.contMDiff.comp
      ((DerivativeSmoothVectors.toSmooth 𝓜 R v).property.comp (contMDiff_unitsMap K n ψ))⟩
  map_add' v w := by
    apply Subtype.ext
    funext x
    simp only [map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c v := by
    apply Subtype.ext
    funext x
    simp only [map_smul, Submodule.coe_smul, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]

omit [FiniteDimensional ℝ A] in
@[simp]
theorem orbitCoefficient_apply (ℓ : E →L[ℂ] ℂ) (v : D)
    (x : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (orbitCoefficient K n ψ R ℓ v).val x =
      ℓ (R (unitsMap K n ψ (archimedeanGLCoordinates K n x)) (ε v)) := rfl

/-- Each actual real directional derivative of a coefficient is the coefficient of the
genuine derivative in the transported direction. -/
theorem smoothDifferential_orbitCoefficient (hR : IsContinuousRepresentation R)
    (ℓ : E →L[ℂ] ℂ) (X : RealLieAlgebra K n) (v : D) :
    smoothDifferential K n X (orbitCoefficient K n ψ R ℓ v) =
      orbitCoefficient K n ψ R ℓ
        (DerivativeSmoothVectors.operator 𝓜 R (ψ (realLieAlgebraToMatrix K n X)) v) := by
  apply Subtype.ext
  funext x
  rw [smoothDifferential_apply]
  let u : ArchimedeanGL K n := archimedeanGLCoordinates K n x
  let Y : ArchimedeanMatrix K n := realLieAlgebraToMatrix K n X
  let F := coordinateExtension K n (orbitCoefficient K n ψ R ℓ v)
  let γ : ℝ → ArchimedeanMatrix K n := fun t => (u : ArchimedeanMatrix K n) +
    t • ((u : ArchimedeanMatrix K n) * Y)
  let c : ℝ → A := fun t => algCLE K n ψ (γ t)
  let g : Aˣ := unitsMap K n ψ u
  have hγ : HasDerivAt γ ((u : ArchimedeanMatrix K n) * Y) 0 := by
    simpa only [γ, id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const ((u : ArchimedeanMatrix K n) * Y)).const_add
        (u : ArchimedeanMatrix K n)
  have hγ0 : γ 0 = (u : ArchimedeanMatrix K n) := by simp [γ]
  have hc : HasDerivAt c (g.val * ψ Y) 0 := by
    have h := (algCLE K n ψ).hasFDerivAt.comp_hasDerivAt (0 : ℝ) hγ
    simpa only [c, Function.comp_def, ContinuousLinearEquiv.coe_coe, algCLE_apply, map_mul,
      g, unitsMap_val] using h
  have hc0 : c 0 = g.val := by
    simp only [c, hγ0, algCLE_apply, g, unitsMap_val]
  have horb := DerivativeSmoothVectors.hasDerivAt_unitsChartOrbit R hR g v hc hc0
  rw [← mul_assoc, Units.inv_mul, one_mul] at horb
  let L : D →L[ℝ] ℂ := (ℓ.restrictScalars ℝ).comp ((ε).restrictScalars ℝ)
  have hscalar : HasDerivAt (fun t => L (DerivativeSmoothVectors.unitsChartAction R (c t, v)))
      (L (DerivativeSmoothVectors.representation 𝓜 R g
        (DerivativeSmoothVectors.operator 𝓜 R (ψ Y) v))) 0 := by
    apply hasDerivAt_iff_tendsto_slope_tvs.mpr
    have h := (L.continuous.tendsto _).comp (hasDerivAt_iff_tendsto_slope_tvs.mp horb)
    refine h.congr fun t => ?_
    simp only [Function.comp_apply, slope_def_module, map_smul, map_sub]
  have hF : HasDerivAt (F ∘ γ) (fderiv ℝ F (u : ArchimedeanMatrix K n)
      ((u : ArchimedeanMatrix K n) * Y)) 0 := by
    have hdiff := (coordinateExtension_contDiffAt K n (orbitCoefficient K n ψ R ℓ v) u).differentiableAt
      (by simp)
    exact hdiff.hasFDerivAt.comp_hasDerivAt_of_eq (0 : ℝ) hγ hγ0.symm
  have heq : F ∘ γ =ᶠ[𝓝 0] fun t => L (DerivativeSmoothVectors.unitsChartAction R (c t, v)) := by
    have hm : ∀ᶠ t in 𝓝 (0 : ℝ), γ t ∈ range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n) :=
      hγ.continuousAt (Units.isOpenEmbedding_val.isOpen_range.mem_nhds ⟨u, hγ0.symm⟩)
    filter_upwards [hm] with t ht
    obtain ⟨h, hh⟩ := ht
    have hct : c t = (unitsMap K n ψ h : A) := by
      simp only [c, ← hh, algCLE_apply, unitsMap_val]
    simp only [Function.comp_apply, F, ← hh, coordinateExtension_apply, hct,
      DerivativeSmoothVectors.unitsChartAction_val]
    rw [orbitCoefficient_apply, ContinuousMulEquiv.apply_symm_apply]
    rfl
  have huniq := hF.unique (hscalar.congr_of_eventuallyEq heq)
  rw [huniq]
  rfl

/-- The genuine derivatives in the transported normalized Cartan directions, squared and summed. -/
def transportedCartanSquareSum : Module.End ℂ D :=
  ∑ i, DerivativeSmoothVectors.operator 𝓜 R
      (ψ (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i))) *
    DerivativeSmoothVectors.operator 𝓜 R
      (ψ (realLieAlgebraToMatrix K n (cartanAdaptedBasis K n i)))

theorem envelopingAction_cartanSquareSum_orbitCoefficient (hR : IsContinuousRepresentation R)
    (ℓ : E →L[ℂ] ℂ) (v : D) :
    envelopingAction K n (cartanSquareSum K n) (orbitCoefficient K n ψ R ℓ v) =
      orbitCoefficient K n ψ R ℓ (transportedCartanSquareSum K n ψ R v) := by
  simp only [cartanSquareSum, transportedCartanSquareSum, map_sum, map_mul,
    realEnvelopingGenerator_apply]
  rw [LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  simp only [Module.End.mul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have hgen (Z : RealLieAlgebra K n) :
      envelopingAction K n (envelopingGenerator K n ((1 : ℂ) ⊗ₜ[ℝ] Z)) =
        smoothDifferential K n Z :=
    envelopingAction_real_generator K n Z
  rw [hgen, smoothDifferential_orbitCoefficient K n ψ R hR,
    smoothDifferential_orbitCoefficient K n ψ R hR]

private theorem map_aeval_of_comm {M N : Type*} [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] (T : M →ₗ[ℂ] N) (a : Module.End ℂ M) (b : Module.End ℂ N)
    (h : ∀ m, T (a m) = b (T m)) (p : Polynomial ℂ) (m : M) :
    T (Polynomial.aeval a p m) = Polynomial.aeval b p (T m) := by
  induction p using Polynomial.induction_on generalizing m with
  | C c => simp [Polynomial.aeval_C, Module.algebraMap_end_apply]
  | add p q hp hq => simp only [map_add, LinearMap.add_apply, hp, hq]
  | monomial k c hk =>
      have e : Polynomial.C c * Polynomial.X ^ (k + 1) =
          (Polynomial.C c * Polynomial.X ^ k) * Polynomial.X := by ring
      rw [e, map_mul (Polynomial.aeval a) (Polynomial.C c * Polynomial.X ^ k) Polynomial.X,
        map_mul (Polynomial.aeval b) (Polynomial.C c * Polynomial.X ^ k) Polynomial.X,
        Polynomial.aeval_X, Polynomial.aeval_X, Module.End.mul_apply, Module.End.mul_apply,
        hk, h]

/-- Every polynomial in the Cartan square sum acts on coefficients through the transported
square sum of genuine derivatives. -/
theorem envelopingAction_aeval_orbitCoefficient (hR : IsContinuousRepresentation R)
    (ℓ : E →L[ℂ] ℂ) (p : Polynomial ℂ) (v : D) :
    envelopingAction K n (Polynomial.aeval (cartanSquareSum K n) p)
        (orbitCoefficient K n ψ R ℓ v) =
      orbitCoefficient K n ψ R ℓ (Polynomial.aeval (transportedCartanSquareSum K n ψ R) p v) := by
  rw [← Polynomial.aeval_algHom_apply]
  exact (map_aeval_of_comm (orbitCoefficient K n ψ R ℓ) _ _
    (fun m => (envelopingAction_cartanSquareSum_orbitCoefficient K n ψ R hR ℓ m).symm) p v).symm

/-- A coefficient of a vector annihilated by a monic polynomial in the transported Cartan
square sum is real analytic on all invertible matrices. -/
theorem analyticOnNhd_orbitCoefficient (hR : IsContinuousRepresentation R) (ℓ : E →L[ℂ] ℂ)
    {p : Polynomial ℂ} (hp : p.Monic) {v : D}
    (hv : Polynomial.aeval (transportedCartanSquareSum K n ψ R) p v = 0) :
    AnalyticOnNhd ℝ (coordinateExtension K n (orbitCoefficient K n ψ R ℓ v))
      (range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)) := by
  obtain ⟨d, Dop, hcoeff, haction, hsymbol⟩ := cartanPolynomialCoordinateRealization K n p hp
  let f := orbitCoefficient K n ψ R ℓ v
  let S : Set (ArchimedeanMatrix K n) := range (Units.val : ArchimedeanGL K n → ArchimedeanMatrix K n)
  have hS : IsOpen S := Units.isOpenEmbedding_val.isOpen_range
  have hsm : ContDiffOn ℝ ∞ (coordinateExtension K n f) S := coordinateExtension_contDiffOn K n f
  have hell : Dop.IsEllipticOn S := by
    rintro x ⟨g, rfl⟩ ξ hξ
    rw [hsymbol g ξ]
    apply pow_ne_zero
    exact_mod_cast (ne_of_gt (ambientCartanCovectorForm_unit_pos K n g ξ hξ))
  have heqn : ∀ x ∈ S, Dop.action (coordinateExtension K n f) x = 0 := by
    rintro x ⟨g, rfl⟩
    rw [haction _ hsm g, cartanAmbientPolynomial_coordinateExtension,
      envelopingAction_aeval_orbitCoefficient K n ψ R hR ℓ p v, hv, map_zero]
    rfl
  exact Langlands.Analysis.scalarEllipticAnalyticity (ArchimedeanMatrix K n) d (2 * p.natDegree)
    Dop S (coordinateExtension K n f) hS hcoeff hell hsm heqn

/-- Endomorphisms of smooth functions preserving a submodule form a subalgebra. -/
private def stabilizerSubalgebra (S : Submodule ℂ (SmoothFunctions K n)) :
    Subalgebra ℂ (Module.End ℂ (SmoothFunctions K n)) where
  carrier := {T | ∀ f ∈ S, T f ∈ S}
  mul_mem' {T U} hT hU f hf := hT _ (hU f hf)
  add_mem' {T U} hT hU f hf := S.add_mem (hT f hf) (hU f hf)
  algebraMap_mem' c f hf := by
    simpa only [Module.algebraMap_end_apply] using S.smul_mem c hf

/-- Fix a continuous complex-linear functional `ℓ`. Let `W` be stable under all genuine
derivatives in the transported directions, and suppose that for each `w' ∈ W` the coefficient
`orbitCoefficient ℓ w'` (formed with this same `ℓ`) vanishes at `x₀`. Then for a vector `w ∈ W`
annihilated by a monic polynomial in the transported Cartan square sum, `orbitCoefficient ℓ w`
vanishes on the whole connected component of `x₀`. -/
theorem orbitCoefficient_eq_zero_of_stable (hR : IsContinuousRepresentation R) (ℓ : E →L[ℂ] ℂ)
    (W : Submodule ℂ D)
    (hW : ∀ (X : RealLieAlgebra K n), ∀ w ∈ W,
      DerivativeSmoothVectors.operator 𝓜 R (ψ (realLieAlgebraToMatrix K n X)) w ∈ W)
    {w : D} (hw : w ∈ W) {p : Polynomial ℂ} (hp : p.Monic)
    (hpw : Polynomial.aeval (transportedCartanSquareSum K n ψ R) p w = 0)
    (x₀ : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (h₀ : ∀ w' ∈ W, (orbitCoefficient K n ψ R ℓ w').val x₀ = 0) :
    ∀ x ∈ connectedComponent x₀, (orbitCoefficient K n ψ R ℓ w).val x = 0 := by
  let S := W.map (orbitCoefficient K n ψ R ℓ)
  let P := stabilizerSubalgebra K n S
  have hreal (Z : RealLieAlgebra K n) : smoothDifferential K n Z ∈ P := by
    rintro _ ⟨w', hw', rfl⟩
    rw [smoothDifferential_orbitCoefficient K n ψ R hR]
    exact Submodule.mem_map_of_mem (hW Z w' hw')
  have hgen (Z : ComplexLieAlgebra K n) : envelopingAction K n (envelopingGenerator K n Z) ∈ P := by
    rw [envelopingAction_generator]
    induction Z using TensorProduct.inductionOn with
    | tmul z Y =>
        rw [complexSmoothLieAction_tmul]
        exact P.smul_mem (hreal Y) z
    | add U V hU hV => simpa only [map_add] using P.add_mem hU hV
  have hall (a : EnvelopingAlgebra K n) : envelopingAction K n a ∈ P := by
    have ha : a ∈ Algebra.adjoin ℂ (range (envelopingGenerator K n)) := by
      change a ∈ Algebra.adjoin ℂ (range (UniversalEnvelopingAlgebra.ι ℂ :
        ComplexLieAlgebra K n → EnvelopingAlgebra K n))
      rw [Langlands.Algebra.LieCasimir.enveloping_adjoin_range]
      trivial
    have hle : Algebra.adjoin ℂ (range (envelopingGenerator K n)) ≤
        P.comap (envelopingAction K n) :=
      Algebra.adjoin_le (by rintro _ ⟨Z, rfl⟩; exact hgen Z)
    exact hle ha
  have hjet0 : ∀ a : EnvelopingAlgebra K n,
      (envelopingAction K n a (orbitCoefficient K n ψ R ℓ w)).val x₀ = 0 := by
    intro a
    obtain ⟨w', hw', he⟩ := hall a _ (Submodule.mem_map_of_mem hw)
    rw [← he]
    exact h₀ w' hw'
  have hjet := envelopingZeroJet K n _ x₀ hjet0
  have han := analyticOnNhd_orbitCoefficient K n ψ R hR ℓ hp hpw
  exact analyticMatrixJetUniqueness K n _ x₀ (fun g => han (g : ArchimedeanMatrix K n) ⟨g, rfl⟩)
    hjet

end Langlands.Archimedean.MixedOrbit

import Langlands.Global.SmoothWhittakerExpansion.Decay
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionRealization

/-! # The Whittaker expansion of a smooth cuspidal function, standard character

Let `f₀` be a finite-smooth function on `GL_{r+1}(F) \ GL_{r+1}(𝔸)` all of whose enveloping
derivatives are cuspidal and grow at most like `exp (c ∑ |x i|)` on archimedean torus
translates of compact sets. The group-scheme functions of the enveloping derivatives of `f₀`
form a `WhittakerDecayClass`, with the archimedean derivatives given by the enveloping action.
The Library's analytic core then gives summable majorants of the Whittaker terms at every level
(half (S)) and the Whittaker expansion with the standard character (half (E)).

This is the argument of `Unfolding.cuspidalWhittakerExpansion` (module
`WhittakerExpansionCore.ExpansionRealization`) for the cyclic space of enveloping derivatives of
one function in place of the space of an operator realization. See `Expansion.md`. -/

noncomputable section
universe u
open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.SmoothWhittakerExpansion

open Langlands.Global Langlands.Global.RankinSelbergGlobal
  Langlands.Global.RankinSelbergGlobal.Unfolding Langlands.Automorphic

local instance expansionSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _

local instance expansionAddCommGroupRationalInvariant (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance expansionAddCommGroupContinuousRational (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance expansionAddCommGroupFiniteSmoothRational (F : Type u) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F]

section Slice

variable {n : ℕ}

/-- The left-invariant derivative of an archimedean slice of a finite-smooth function is the
slice of its enveloping derivative. -/
theorem smoothDifferential_finiteSmoothSlice (w : FiniteSmoothRationalFunctions F n)
    (Z : ArchimedeanMatrix F n) (y : FiniteAdelicGL F n) (x : InfiniteAdelicGL F n) :
    (ArchimedeanGL.smoothDifferential F n ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n y w)).val x =
      ContinuousRationalFunctions.evaluate F n
        (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w).val
        (AdelicGL.ofInfinite F n x * AdelicGL.ofFinite F n y) := by
  have e2 := finiteSmoothSlice_envelopingAction F n (matrixGenerator F n Z) w y
  have e3 := ArchimedeanGL.envelopingAction_real_generator F n
    ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
  have e4 : finiteSmoothSlice F n y (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w) =
      ArchimedeanGL.smoothDifferential F n ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n y w) := by
    rw [e2]
    exact congrArg (fun A : Module.End ℂ (ArchimedeanGL.SmoothFunctions F n) =>
      A (finiteSmoothSlice F n y w)) e3
  rw [← e4, finiteSmoothSlice_apply, OperatorRealization.pair_eq_ofInfinite_mul_ofFinite]

/-- **Derivative of a finite-smooth function along a square-zero archimedean direction.** -/
theorem hasDerivAt_finiteSmooth_squareZero (w : FiniteSmoothRationalFunctions F n)
    (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) (g : AdelicGL F n) :
    HasDerivAt (fun t : ℝ => ContinuousRationalFunctions.evaluate F n w.val
        (g * AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement (t • Z)
          (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))))
      (ContinuousRationalFunctions.evaluate F n
        (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w).val g) 0 := by
  have hfun : (fun t : ℝ => ContinuousRationalFunctions.evaluate F n w.val
      (g * AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement (t • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))) =
      fun t : ℝ => (finiteSmoothSlice F n (AdelicGL.finite F n g) w).val
        (AdelicGL.infinite F n g * ArchimedeanGL.squareZeroElement (t • Z)
          (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) := by
    funext t
    rw [mul_ofInfinite_eq, finiteSmoothSlice_apply,
      OperatorRealization.pair_eq_ofInfinite_mul_ofFinite]
  have hg : g = AdelicGL.ofInfinite F n (AdelicGL.infinite F n g) *
      AdelicGL.ofFinite F n (AdelicGL.finite F n g) := by
    refine AdelicGL.ext_infinite_finite F n ?_ ?_ <;> simp
  have h := hasDerivAt_smooth_squareZero F n
    (finiteSmoothSlice F n (AdelicGL.finite F n g) w) (AdelicGL.infinite F n g) Z hZ
  have h2 : (ArchimedeanGL.smoothDifferential F n
      ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n (AdelicGL.finite F n g) w)).val (AdelicGL.infinite F n g) =
      ContinuousRationalFunctions.evaluate F n
        (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w).val g :=
    (smoothDifferential_finiteSmoothSlice F w Z _ _).trans
      (congrArg (ContinuousRationalFunctions.evaluate F n _) hg.symm)
  exact (h.congr_deriv h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hfun t)

end Slice

section SchemeFunction

variable (n : ℕ)

/-- The group-scheme function of a matrix-side finite-smooth function. -/
def schemeFunction : FiniteSmoothRationalFunctions F n →ₗ[ℂ] (Points F n → ℂ) where
  toFun w := GroupSchemeFunctions.evaluate F (Scheme F n)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm w.val)
  map_add' v w := by
    funext x
    simp only [Submodule.coe_add, map_add, Pi.add_apply]
    rfl
  map_smul' c w := by
    funext x
    simp only [Submodule.coe_smul, map_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

variable {n}

theorem schemeFunction_apply (w : FiniteSmoothRationalFunctions F n) (x : Points F n) :
    schemeFunction F n w x = ContinuousRationalFunctions.evaluate F n w.val
      (GeneralLinearGroupPoints.adelicHomeomorph F n x) := by
  have hx := GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F n
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm w.val) x
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx.symm

theorem schemeFunction_injective : Function.Injective (schemeFunction F n) := by
  intro v w h
  apply Subtype.ext
  apply (GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm.injective
  apply Subtype.ext
  apply Subtype.ext
  exact h

theorem continuous_schemeFunction (w : FiniteSmoothRationalFunctions F n) :
    Continuous (schemeFunction F n w) :=
  show Continuous (GroupSchemeFunctions.evaluate F (Scheme F n)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm w.val)) from
  Unfolding.continuous_evaluate F (Scheme F n) _

theorem schemeFunction_rational_mul (w : FiniteSmoothRationalFunctions F n) {k : Points F n}
    (hk : k ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F n)) (x : Points F n) :
    schemeFunction F n w (k * x) = schemeFunction F n w x :=
  show GroupSchemeFunctions.evaluate F (Scheme F n)
      ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm w.val) (k * x) =
    GroupSchemeFunctions.evaluate F (Scheme F n)
      ((GroupSchemeFunctions.continuousGeneralLinearEquiv F n).symm w.val) x from
  Unfolding.evaluate_rational_mul F (Scheme F n) _ ⟨k, hk⟩ x

/-- The derivative of a group-scheme function along a square-zero archimedean direction. -/
theorem schemeFunction_deriv (w : FiniteSmoothRationalFunctions F n)
    (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) (x : Points F n) :
    HasDerivAt (fun t : ℝ => schemeFunction F n w
        (x * archPoint F n (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (schemeFunction F n (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w) x) 0 := by
  have h := hasDerivAt_finiteSmooth_squareZero F w Z hZ
    (GeneralLinearGroupPoints.adelicHomeomorph F n x)
  have h2 := schemeFunction_apply F
    (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z) w) x
  refine (h.congr_deriv h2.symm).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e1 := schemeFunction_apply F w
    (x * archPoint F n (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))
  have e3 : GeneralLinearGroupPoints.adelicHomeomorph F n
      (x * archPoint F n (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) =
      GeneralLinearGroupPoints.adelicHomeomorph F n x * AdelicGL.ofInfinite F n
        (ArchimedeanGL.squareZeroElement (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) := by
    rw [map_mul, adelicHomeomorph_archPoint]
  exact e1.trans (congrArg (ContinuousRationalFunctions.evaluate F n w.val) e3)

end SchemeFunction

section Derivatives

variable {n : ℕ} (f₀ : FiniteSmoothRationalFunctions F n)

/-- The enveloping derivatives `u · f₀` of `f₀`, a submodule of finite-smooth functions. -/
def derivatives : Submodule ℂ (FiniteSmoothRationalFunctions F n) :=
  LinearMap.range ((LinearMap.applyₗ f₀).comp (finiteSmoothEnvelopingAction F n).toLinearMap)

theorem mem_derivatives {w : FiniteSmoothRationalFunctions F n} :
    w ∈ derivatives F f₀ ↔ ∃ u, finiteSmoothEnvelopingAction F n u f₀ = w :=
  LinearMap.mem_range

theorem self_mem_derivatives : f₀ ∈ derivatives F f₀ :=
  (mem_derivatives F f₀).mpr ⟨1, by rw [map_one, Module.End.one_apply]⟩

theorem envelopingAction_mem_derivatives (a : ArchimedeanGL.EnvelopingAlgebra F n)
    {w : FiniteSmoothRationalFunctions F n} (hw : w ∈ derivatives F f₀) :
    finiteSmoothEnvelopingAction F n a w ∈ derivatives F f₀ := by
  obtain ⟨u, rfl⟩ := (mem_derivatives F f₀).mp hw
  exact (mem_derivatives F f₀).mpr ⟨a * u, by rw [map_mul, Module.End.mul_apply]⟩

/-- The enveloping action restricted to the derivatives of `f₀`. -/
def derivativeEnd (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    derivatives F f₀ →ₗ[ℂ] derivatives F f₀ :=
  LinearMap.codRestrict (derivatives F f₀)
    ((finiteSmoothEnvelopingAction F n a).comp (derivatives F f₀).subtype)
    (fun w => envelopingAction_mem_derivatives F f₀ a w.property)

theorem derivativeEnd_add (a b : ArchimedeanGL.EnvelopingAlgebra F n) :
    derivativeEnd F f₀ (a + b) = derivativeEnd F f₀ a + derivativeEnd F f₀ b := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  simp [derivativeEnd, map_add]

theorem derivativeEnd_smul (c : ℂ) (a : ArchimedeanGL.EnvelopingAlgebra F n) :
    derivativeEnd F f₀ (c • a) = c • derivativeEnd F f₀ a := by
  refine LinearMap.ext fun w => Subtype.ext ?_
  simp [derivativeEnd, map_smul]

/-- The group-scheme functions of the enveloping derivatives of `f₀`. -/
def decaySpace : Submodule ℂ (Points F n → ℂ) := (derivatives F f₀).map (schemeFunction F n)

/-- The derivatives of `f₀` are identified with their group-scheme functions. -/
def decayEquiv : derivatives F f₀ ≃ₗ[ℂ] decaySpace F f₀ :=
  Submodule.equivMapOfInjective (schemeFunction F n) (schemeFunction_injective F) _

theorem coe_decayEquiv (w : derivatives F f₀) :
    ((decayEquiv F f₀ w : decaySpace F f₀) : Points F n → ℂ) = schemeFunction F n w := rfl

theorem coe_eq_schemeFunction (v : decaySpace F f₀) :
    (v : Points F n → ℂ) = schemeFunction F n ((decayEquiv F f₀).symm v) := by
  rw [← coe_decayEquiv, LinearEquiv.apply_symm_apply]

theorem exists_eq_envelopingAction (v : decaySpace F f₀) :
    ∃ u, (v : Points F n → ℂ) = schemeFunction F n (finiteSmoothEnvelopingAction F n u f₀) := by
  obtain ⟨u, hu⟩ := (mem_derivatives F f₀).mp ((decayEquiv F f₀).symm v).property
  exact ⟨u, by rw [hu, coe_eq_schemeFunction]⟩

/-- The archimedean derivatives on the decay space, through the enveloping action. -/
def decayDerivative :
    ArchimedeanMatrix F n →ₗ[ℝ] decaySpace F f₀ →ₗ[ℂ] decaySpace F f₀ where
  toFun Z := (decayEquiv F f₀).toLinearMap ∘ₗ derivativeEnd F f₀ (matrixGenerator F n Z) ∘ₗ
    (decayEquiv F f₀).symm.toLinearMap
  map_add' Z₁ Z₂ := by
    rw [matrixGenerator_add, derivativeEnd_add, LinearMap.add_comp, LinearMap.comp_add]
  map_smul' c Z := by
    rw [matrixGenerator_smul, derivativeEnd_smul]
    refine LinearMap.ext fun v => Subtype.ext ?_
    funext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, LinearEquiv.coe_coe, map_smul,
      RingHom.id_apply, Submodule.coe_smul_of_tower, Pi.smul_apply, Complex.real_smul,
      smul_eq_mul]

theorem coe_decayDerivative (Z : ArchimedeanMatrix F n) (v : decaySpace F f₀) :
    ((decayDerivative F f₀ Z v : decaySpace F f₀) : Points F n → ℂ) =
      schemeFunction F n (finiteSmoothEnvelopingAction F n (matrixGenerator F n Z)
        ((decayEquiv F f₀).symm v)) := rfl

end Derivatives

section DecayClass

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (f₀ : FiniteSmoothRationalFunctions F (r + 1))
  (hcusp : ∀ u, IsCuspidal F (r + 1) (finiteSmoothEnvelopingAction F (r + 1) u f₀).val)
  {c : ℝ} (hc : 0 ≤ c)
  (hgrowth : ∀ (u : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) (Q : Set (AdelicGL F (r + 1))),
    IsCompact Q → ∃ C : ℝ, ∀ x, ∀ q ∈ Q,
      ‖ContinuousRationalFunctions.evaluate F (r + 1)
          (finiteSmoothEnvelopingAction F (r + 1) u f₀).val
          (AdelicGL.ofInfinite F (r + 1) (torInf F (r + 1) x) * q)‖ ≤
        C * Real.exp (c * ∑ i, |x i|))

include hcusp hc hgrowth in
/-- **The enveloping derivatives of `f₀` form a Whittaker decay class.** -/
theorem whittakerDecayClass_decaySpace :
    WhittakerDecayClass F r (decaySpace F f₀) (decayDerivative F f₀) := by
  obtain ⟨L, hLo, hL⟩ := exists_common_level f₀
  refine ⟨fun v => ?_, fun v y hy x => ?_, fun v => ⟨L, hLo, fun x l hl => ?_⟩,
    fun v lo hi hlo => ?_, fun v Z hZ x => ?_⟩
  · rw [coe_eq_schemeFunction]
    exact continuous_schemeFunction F _
  · rw [coe_eq_schemeFunction]
    exact schemeFunction_rational_mul F _ hy x
  · obtain ⟨u, hu⟩ := exists_eq_envelopingAction F f₀ v
    rw [hu, schemeFunction_apply, schemeFunction_apply, map_mul, adelicHomeomorph_finitePoint]
    exact hL u _ l hl
  · obtain ⟨u, hu⟩ := exists_eq_envelopingAction F f₀ v
    obtain ⟨B, hB⟩ := SmoothWhittakerExpansion.exists_band_bound f₀ hcusp hc hgrowth u hlo
      (hi := hi)
    refine ⟨B, fun x hlx hhx => ?_⟩
    rw [hu, schemeFunction_apply]
    exact hB _ hlx hhx
  · rw [coe_decayDerivative]
    have e := coe_eq_schemeFunction F f₀ v
    refine (schemeFunction_deriv F _ Z hZ x).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => congrFun e _)

variable (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ)

include hcusp hc hgrowth hψ in
/-- **Locally uniform summable majorants** of the Whittaker terms of `f₀`, at every level. -/
theorem hasWhittakerMajorants_schemeFunction :
    HasWhittakerMajorants F r ψ (schemeFunction F (r + 1) f₀) :=
  whittakerMajorantsStatement_proof F r (decaySpace F f₀) (decayDerivative F f₀)
    (whittakerDecayClass_decaySpace F f₀ hcusp hc hgrowth) ψ hψ
    (decayEquiv F f₀ ⟨f₀, self_mem_derivatives F f₀⟩)

include hcusp hc hgrowth hψ in
/-- **The Whittaker expansion of `f₀` with the standard character.** -/
theorem hasSum_whittaker_schemeFunction (x : Points F (r + 1)) :
    HasSum (fun q : UnipotentRationalCosets F r =>
      whittaker F r ψ (schemeFunction F (r + 1) f₀) (cornerAdelicPoint F r q.out * x))
      (schemeFunction F (r + 1) f₀ x) := by
  have hmaj := hasWhittakerMajorants_schemeFunction F f₀ hcusp hc hgrowth ψ hψ
  have hsum : ∀ (k : ℕ) (hk : k ≤ r) (x : Points F (r + 1)),
      Summable fun q : UnipotentRationalCosets F k =>
        ‖whittaker F r ψ (schemeFunction F (r + 1) f₀)
          (padRational F (Nat.le_succ_of_le hk) q.out * x)‖ := by
    intro k hk x
    obtain ⟨b, hb, hle⟩ := hmaj k hk {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hle q x rfl) hb
  have htop : CuspidalWhittaker.LevelPropsB r (fun g =>
      schemeFunction F (r + 1) f₀ ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) := by
    have h0 := hcusp 1
    rw [map_one, Module.End.one_apply] at h0
    have h := (CuspidalWhittaker.levelProps_top f₀.val h0).levelPropsB
    have e : (fun g => schemeFunction F (r + 1) f₀
        ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) =
        ContinuousRationalFunctions.evaluate F (r + 1) f₀.val := by
      funext g
      rw [schemeFunction_apply, ContinuousMulEquiv.apply_symm_apply]
    rw [e]
    exact h
  exact hasSum_whittaker_of_levelPropsB F ψ (schemeFunction F (r + 1) f₀) hψ
    (continuous_schemeFunction F f₀) (fun k hk x => schemeFunction_rational_mul F f₀ hk x) htop
    hsum x

end DecayClass

end Langlands.Global.SmoothWhittakerExpansion

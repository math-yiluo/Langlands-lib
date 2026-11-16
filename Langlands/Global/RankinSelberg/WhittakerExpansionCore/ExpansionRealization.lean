import Langlands.Global.RankinSelberg.WhittakerExpansionCore.ExpansionInduction
import Langlands.Global.RankinSelberg.WhittakerExpansionCore.WhittakerStep
import Langlands.Automorphic.CuspidalL2.SiegelCover

/-! # The Whittaker expansion of the vectors of a cuspidal realization

The cusp functions `x ↦ φ_v(x)` of the vectors `v` of an actual cuspidal operator realization
form a `WhittakerDecayClass`, with the archimedean derivatives given by the enveloping algebra
action. Half (S) then gives summable majorants for the Whittaker terms at every level. Half (E),
with cuspidality at the top level, gives the expansion. -/

noncomputable section
universe u
open scoped Matrix.Norms.Operator
open CategoryTheory AlgebraicGeometry NumberField MeasureTheory
open scoped CategoryTheory.MonObj
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.Unfolding

open Langlands.Global Langlands.GroupScheme Langlands.GroupScheme.GeneralLinear
  AdelicSubgroupPoints Langlands.Automorphic Langlands.Automorphic.ContinuousRationalFunctions

local instance realizationSchemeAffine (F : Type u) [Field F] (n : ℕ) :
    IsAffine (Scheme F n).X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
local instance realizationSchemeSmooth (F : Type u) [Field F] (n : ℕ) :
    Smooth (Scheme F n).X.hom := GroupScheme.GeneralLinear.smoothStatement _ _

local instance realizationAddCommGroupRationalInvariant (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance realizationAddCommGroupContinuousRational (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance realizationAddCommGroupFiniteSmoothRational (F : Type u) [Field F]
    [NumberField F] (n : ℕ) : AddCommGroup (FiniteSmoothRationalFunctions F n) :=
  Submodule.addCommGroup _
local instance realizationAddCommGroupAutomorphicForms (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance realizationAddCommGroupStableAutomorphic (F : Type u) [Field F] [NumberField F]
    (n : ℕ) : AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _

variable (F : Type u) [Field F] [NumberField F]

section Archimedean

open scoped Classical

variable (n : ℕ)

/-- The enveloping-algebra generator of a real archimedean matrix direction `Z`. -/
def matrixGenerator (Z : ArchimedeanMatrix F n) : ArchimedeanGL.EnvelopingAlgebra F n :=
  ArchimedeanGL.envelopingGenerator F n
    (ArchimedeanGL.complexify F n ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z))

omit [NumberField F] in
theorem matrixGenerator_add (Z₁ Z₂ : ArchimedeanMatrix F n) :
    matrixGenerator F n (Z₁ + Z₂) = matrixGenerator F n Z₁ + matrixGenerator F n Z₂ := by
  unfold matrixGenerator
  simp only [map_add]

omit [NumberField F] in
theorem matrixGenerator_smul (c : ℝ) (Z : ArchimedeanMatrix F n) :
    matrixGenerator F n (c • Z) = (c : ℂ) • matrixGenerator F n Z := by
  unfold matrixGenerator
  rw [← map_smul (ArchimedeanGL.envelopingGenerator F n)]
  congr 1
  rw [LinearEquiv.map_smul, ArchimedeanGL.complexify_apply, ArchimedeanGL.complexify_apply,
    TensorProduct.tmul_smul]
  exact (algebraMap_smul ℂ c _).symm

/-- Right translation of an adelic matrix by an archimedean matrix, in product form. -/
theorem mul_ofInfinite_eq (g : AdelicGL F n) (h : InfiniteAdelicGL F n) :
    g * AdelicGL.ofInfinite F n h =
      AdelicGL.ofInfinite F n (AdelicGL.infinite F n g * h) *
        AdelicGL.ofFinite F n (AdelicGL.finite F n g) := by
  refine AdelicGL.ext_infinite_finite F n ?_ ?_ <;> simp

/-- The derivative of a smooth archimedean function along `t ↦ x (1 + t Z)` at `t = 0`, for a
square-zero `Z`, is its left-invariant derivative in the direction `Z`. -/
theorem hasDerivAt_smooth_squareZero (f : ArchimedeanGL.SmoothFunctions F n)
    (x : InfiniteAdelicGL F n) (Z : ArchimedeanMatrix F n) (hZ : Z * Z = 0) :
    HasDerivAt (fun t : ℝ => f.val (x * ArchimedeanGL.squareZeroElement (t • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      ((ArchimedeanGL.smoothDifferential F n
        ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z) f).val x) 0 := by
  set xc : ArchimedeanGL F n := archimedeanGLCoordinates F n x with hxc
  let p : ℝ → ArchimedeanMatrix F n := fun s => (xc : ArchimedeanMatrix F n) * (1 + s • Z)
  have hp_unit (s : ℝ) : p s =
      ((xc * ArchimedeanGL.squareZeroUnit (s • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ s) :
        ArchimedeanGL F n) : ArchimedeanMatrix F n) := rfl
  have hh (s : ℝ) : ArchimedeanGL.coordinateExtension F n f (p s) =
      f.val (x * ArchimedeanGL.squareZeroElement (s • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ s)) := by
    rw [hp_unit, ArchimedeanGL.coordinateExtension_apply, map_mul,
      ContinuousMulEquiv.symm_apply_apply]
    rfl
  have hpderiv : HasDerivAt p ((xc : ArchimedeanMatrix F n) * Z) 0 := by
    have h1 : HasDerivAt (fun s : ℝ => (1 : ArchimedeanMatrix F n) + s • Z) Z 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const Z).const_add (1 : ArchimedeanMatrix F n)
    have h2 := h1.const_mul (xc : ArchimedeanMatrix F n)
    simpa [p] using h2
  have hdiff : DifferentiableAt ℝ (ArchimedeanGL.coordinateExtension F n f) (p 0) := by
    rw [hp_unit]
    exact (ArchimedeanGL.coordinateExtension_contDiffAt F n f _).differentiableAt (by simp)
  have hc : HasDerivAt (fun t : ℝ => f.val (x * ArchimedeanGL.squareZeroElement (t • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (fderiv ℝ (ArchimedeanGL.coordinateExtension F n f) (p 0)
        ((xc : ArchimedeanMatrix F n) * Z)) 0 :=
    (hdiff.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hpderiv).congr_of_eventuallyEq
      (Filter.Eventually.of_forall fun t => (hh t).symm)
  have hp0 : p 0 = (xc : ArchimedeanMatrix F n) := by simp [p]
  refine hc.congr_deriv ?_
  rw [ArchimedeanGL.smoothDifferential_apply, hp0, LinearEquiv.apply_symm_apply]

variable {n} (S : OperatorRealization F n)

local instance realizationAddCommGroupSpace : AddCommGroup S.Space := Submodule.addCommGroup _

/-- The left-invariant derivative of an archimedean slice of a realized vector is the slice of
its enveloping derivative. -/
theorem smoothDifferential_slice (w : S.Space) (Z : ArchimedeanMatrix F n)
    (y : FiniteAdelicGL F n) (x : InfiniteAdelicGL F n) :
    (ArchimedeanGL.smoothDifferential F n ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n y (S.ambient w))).val x =
      evaluate F n (S.toContinuous (S.envelopingAction (matrixGenerator F n Z) w))
        (AdelicGL.ofInfinite F n x * AdelicGL.ofFinite F n y) := by
  have e1 := congrArg (finiteSmoothSlice F n y)
    (S.ambient_envelopingAction (matrixGenerator F n Z) w)
  have e2 := finiteSmoothSlice_envelopingAction F n (matrixGenerator F n Z) (S.ambient w) y
  have e3 := ArchimedeanGL.envelopingAction_real_generator F n
    ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
  have e4 : finiteSmoothSlice F n y (S.ambient (S.envelopingAction (matrixGenerator F n Z) w)) =
      ArchimedeanGL.smoothDifferential F n ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n y (S.ambient w)) := by
    rw [e1, e2]
    exact congrArg (fun A : Module.End ℂ (ArchimedeanGL.SmoothFunctions F n) =>
      A (finiteSmoothSlice F n y (S.ambient w))) e3
  exact (congrArg (fun f : ArchimedeanGL.SmoothFunctions F n => f.val x) e4).symm.trans
    (S.finiteSmoothSlice_ambient_apply _ y x)

/-- **Derivative of a realized vector along a square-zero archimedean direction.** -/
theorem hasDerivAt_evaluate_squareZero (w : S.Space) (Z : ArchimedeanMatrix F n)
    (hZ : Z * Z = 0) (g : AdelicGL F n) :
    HasDerivAt (fun t : ℝ => evaluate F n (S.toContinuous w)
        (g * AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement (t • Z)
          (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))))
      (evaluate F n (S.toContinuous (S.envelopingAction (matrixGenerator F n Z) w)) g) 0 := by
  have hfun : (fun t : ℝ => evaluate F n (S.toContinuous w)
      (g * AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement (t • Z)
        (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))) =
      fun t : ℝ => (finiteSmoothSlice F n (AdelicGL.finite F n g) (S.ambient w)).val
        (AdelicGL.infinite F n g * ArchimedeanGL.squareZeroElement (t • Z)
          (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) := by
    funext t
    rw [mul_ofInfinite_eq, S.finiteSmoothSlice_ambient_apply]
  have hg : g = AdelicGL.ofInfinite F n (AdelicGL.infinite F n g) *
      AdelicGL.ofFinite F n (AdelicGL.finite F n g) := by
    refine AdelicGL.ext_infinite_finite F n ?_ ?_ <;> simp
  have h := hasDerivAt_smooth_squareZero F n
    (finiteSmoothSlice F n (AdelicGL.finite F n g) (S.ambient w)) (AdelicGL.infinite F n g) Z hZ
  have h2 : (ArchimedeanGL.smoothDifferential F n
      ((ArchimedeanGL.realLieAlgebraToMatrix F n).symm Z)
        (finiteSmoothSlice F n (AdelicGL.finite F n g) (S.ambient w))).val
          (AdelicGL.infinite F n g) =
      evaluate F n (S.toContinuous (S.envelopingAction (matrixGenerator F n Z) w)) g :=
    (smoothDifferential_slice F S w Z _ _).trans (congrArg (evaluate F n _) hg.symm)
  exact (h.congr_deriv h2).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun hfun t)

/-- A realized vector is invariant under right translation by an open finite level. -/
theorem exists_level_evaluate (w : S.Space) :
    ∃ L : Subgroup (FiniteAdelicGL F n), IsOpen (L : Set (FiniteAdelicGL F n)) ∧
      ∀ (g : AdelicGL F n), ∀ l ∈ L,
        evaluate F n (S.toContinuous w) (g * AdelicGL.ofFinite F n l) =
          evaluate F n (S.toContinuous w) g := by
  obtain ⟨L, hLo, hL⟩ := S.exists_level w
  refine ⟨L, hLo, fun g l hl => ?_⟩
  have h := hL 1 g l hl
  rwa [map_one, Module.End.one_apply] at h

/-- A vector of a cuspidal realization is bounded on every determinant band. -/
theorem exists_band_bound [CompactSpace (AdeleQuotient F)] (hS : S.IsCuspidal) (w : S.Space)
    {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ B : ℝ, ∀ g : AdelicGL F n, lo ≤ absDet F n g → absDet F n g ≤ hi →
      ‖evaluate F n (S.toContinuous w) g‖ ≤ B := by
  obtain ⟨Q₁, K, hQ₁, hK, hdec⟩ := exists_siegelDecomposition F n
  obtain ⟨L, hL⟩ : ∃ L : ℝ, ∀ q ∈ Q₁, |Real.log (absDet F n q)| ≤ L :=
    (hQ₁.image (continuous_abs.comp ((continuous_absDet F n).log
      fun g => (absDet_pos F n g).ne'))).bddAbove.elim
      fun L hL => ⟨L, fun q hq => hL ⟨q, hq, rfl⟩⟩
  obtain ⟨C, hC⟩ := S.exists_chamber_decay hS w Q₁ hQ₁
    (K := K) (R := max |Real.log lo| |Real.log hi| + L) (c := 0) hK le_rfl
  refine ⟨C, fun g hlg hhg => ?_⟩
  obtain ⟨γr, y, q, hq, hγ, hy⟩ := hdec g
  have hRy : |∑ i, y i| ≤ max |Real.log lo| |Real.log hi| + L := by
    have h1 := abs_sum_le_of_absDet F n y q
    rw [← hγ, absDet_rational_mul] at h1
    have hl := Real.log_le_log hlo hlg
    have hh := Real.log_le_log (absDet_pos F n g) hhg
    have h2 : |Real.log (absDet F n g)| ≤ max |Real.log lo| |Real.log hi| :=
      abs_le.mpr ⟨by linarith [neg_abs_le (Real.log lo), le_max_left |Real.log lo| |Real.log hi|],
        by linarith [le_abs_self (Real.log hi), le_max_right |Real.log lo| |Real.log hi|]⟩
    linarith [hL q hq]
  have h := hC y hy hRy q hq
  rw [← hγ, evaluate_rational, zero_mul, neg_zero, Real.exp_zero, mul_one] at h
  exact h

end Archimedean

variable [CompactSpace (AdeleQuotient F)] {r : ℕ} (T : CuspidalOperatorRealization F r)

section Realization

theorem cuspFunction_apply_eq (v : T.Space) (x : Points F (r + 1)) :
    cuspFunction F T v x = evaluate F (r + 1) (T.realization.toContinuous v)
      (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x) := by
  have hx := GroupSchemeFunctions.evaluate_continuousGeneralLinearEquiv_at_point F (r + 1)
    ((GroupSchemeFunctions.continuousGeneralLinearEquiv F (r + 1)).symm
      (T.realization.toContinuous v)) x
  rw [LinearEquiv.apply_symm_apply] at hx
  exact hx.symm

omit [NumberField F] in
theorem adelicHomeomorph_finitePoint [NumberField F] (n : ℕ) (l : FiniteAdelicGL F n) :
    GeneralLinearGroupPoints.adelicHomeomorph F n (finitePoint F n l) = AdelicGL.ofFinite F n l :=
  (GeneralLinearGroupPoints.adelicEquiv F n).apply_symm_apply _

omit [NumberField F] in
theorem adelicHomeomorph_archPoint [NumberField F] (n : ℕ) (Z : ArchimedeanMatrix F n)
    (hZ : Z * Z = 0) :
    GeneralLinearGroupPoints.adelicHomeomorph F n (archPoint F n Z hZ) =
      AdelicGL.ofInfinite F n (ArchimedeanGL.squareZeroElement Z hZ) :=
  (GeneralLinearGroupPoints.adelicEquiv F n).apply_symm_apply _

/-- The cusp functions of the vectors of `T`, as a linear map. -/
def cuspLinear : T.Space →ₗ[ℂ] (Points F (r + 1) → ℂ) where
  toFun := cuspFunction F T
  map_add' v w := by
    funext x
    simp only [cuspFunction_apply_eq, map_add, Pi.add_apply]
    rfl
  map_smul' c v := by
    funext x
    simp only [cuspFunction_apply_eq, map_smul, Pi.smul_apply, RingHom.id_apply]
    rfl

theorem cuspLinear_injective : Function.Injective (cuspLinear F T) := by
  intro v w h
  apply T.realization.toContinuous_injective
  have h' : evaluate F (r + 1) (T.realization.toContinuous v) =
      evaluate F (r + 1) (T.realization.toContinuous w) := by
    funext g
    have := congrFun h ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)
    change cuspFunction F T v _ = cuspFunction F T w _ at this
    rwa [cuspFunction_apply_eq, cuspFunction_apply_eq, ContinuousMulEquiv.apply_symm_apply] at this
  exact Subtype.ext (Subtype.ext h')

/-- The space of cusp functions of `T`. -/
def cuspSpace : Submodule ℂ (Points F (r + 1) → ℂ) := LinearMap.range (cuspLinear F T)

/-- The vectors of `T` are identified with their cusp functions. -/
def cuspEquiv : T.Space ≃ₗ[ℂ] cuspSpace F T :=
  LinearEquiv.ofInjective (cuspLinear F T) (cuspLinear_injective F T)

theorem coe_cuspEquiv (v : T.Space) :
    ((cuspEquiv F T v : cuspSpace F T) : Points F (r + 1) → ℂ) = cuspFunction F T v := rfl

theorem coe_eq_cuspFunction (f : cuspSpace F T) :
    (f : Points F (r + 1) → ℂ) = cuspFunction F T ((cuspEquiv F T).symm f) := by
  rw [← coe_cuspEquiv, LinearEquiv.apply_symm_apply]

/-- The archimedean derivatives on the cusp functions, through the enveloping action. -/
def cuspDerivative :
    ArchimedeanMatrix F (r + 1) →ₗ[ℝ] cuspSpace F T →ₗ[ℂ] cuspSpace F T where
  toFun Z := (cuspEquiv F T).toLinearMap ∘ₗ
    T.realization.envelopingAction (matrixGenerator F (r + 1) Z) ∘ₗ
      (cuspEquiv F T).symm.toLinearMap
  map_add' Z₁ Z₂ := by
    refine LinearMap.ext fun f => ?_
    simp only [LinearMap.comp_apply, LinearMap.add_apply, matrixGenerator_add, map_add,
      LinearEquiv.coe_coe]
  map_smul' c Z := by
    refine LinearMap.ext fun f => ?_
    apply Subtype.ext
    funext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply, matrixGenerator_smul, map_smul,
      LinearEquiv.coe_coe, RingHom.id_apply, Submodule.coe_smul_of_tower, Pi.smul_apply,
      Complex.real_smul, smul_eq_mul]

theorem coe_cuspDerivative (Z : ArchimedeanMatrix F (r + 1)) (f : cuspSpace F T) :
    ((cuspDerivative F T Z f : cuspSpace F T) : Points F (r + 1) → ℂ) =
      cuspFunction F T (T.realization.envelopingAction (matrixGenerator F (r + 1) Z)
        ((cuspEquiv F T).symm f)) := rfl

/-- Cusp functions are bounded on every determinant band `lo ≤ |det| ≤ hi`. -/
theorem exists_bound_cuspFunction (v : T.Space) {lo hi : ℝ} (hlo : 0 < lo) :
    ∃ B : ℝ, ∀ x : Points F (r + 1), lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi →
      ‖cuspFunction F T v x‖ ≤ B := by
  obtain ⟨B, hB⟩ := exists_band_bound F T.realization T.cuspidal v hlo (hi := hi)
  refine ⟨B, fun x hlx hhx => ?_⟩
  rw [cuspFunction_apply_eq]
  exact hB _ hlx hhx

theorem cuspSpace_continuous (f : cuspSpace F T) : Continuous (f : Points F (r + 1) → ℂ) := by
  rw [coe_eq_cuspFunction]
  exact continuous_cuspFunction F T _

theorem cuspSpace_rational (f : cuspSpace F T) (y : Points F (r + 1))
    (hy : y ∈ AdelicGroupPoints.rationalSubgroup F (Scheme F (r + 1))) (x : Points F (r + 1)) :
    (f : Points F (r + 1) → ℂ) (y * x) = (f : Points F (r + 1) → ℂ) x := by
  rw [coe_eq_cuspFunction]
  exact cuspFunction_rational_mul F T _ hy x

/-- Cusp functions are invariant under an open finite level. -/
theorem cuspFunction_level (v : T.Space) : ∃ L : Subgroup (FiniteAdelicGL F (r + 1)),
    IsOpen (L : Set (FiniteAdelicGL F (r + 1))) ∧
      ∀ x, ∀ l ∈ L, cuspFunction F T v (x * finitePoint F (r + 1) l) = cuspFunction F T v x := by
  obtain ⟨L, hLo, hL⟩ := exists_level_evaluate F T.realization v
  refine ⟨L, hLo, fun x l hl => ?_⟩
  have e1 := cuspFunction_apply_eq F T v (x * finitePoint F (r + 1) l)
  have e2 := cuspFunction_apply_eq F T v x
  have e3 : GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) (x * finitePoint F (r + 1) l) =
      GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x * AdelicGL.ofFinite F (r + 1) l := by
    rw [map_mul, adelicHomeomorph_finitePoint]
  rw [e1, e2, e3]
  exact hL _ l hl

theorem cuspSpace_level (f : cuspSpace F T) : ∃ L : Subgroup (FiniteAdelicGL F (r + 1)),
    IsOpen (L : Set (FiniteAdelicGL F (r + 1))) ∧
      ∀ x, ∀ l ∈ L, (f : Points F (r + 1) → ℂ) (x * finitePoint F (r + 1) l) =
        (f : Points F (r + 1) → ℂ) x := by
  rw [coe_eq_cuspFunction]
  exact cuspFunction_level F T _

theorem cuspSpace_bounded (f : cuspSpace F T) (lo hi : ℝ) (hlo : 0 < lo) :
    ∃ B : ℝ, ∀ x : Points F (r + 1), lo ≤ detNorm F (r + 1) x → detNorm F (r + 1) x ≤ hi →
      ‖(f : Points F (r + 1) → ℂ) x‖ ≤ B := by
  rw [coe_eq_cuspFunction]
  exact exists_bound_cuspFunction F T _ hlo

/-- The derivative of a cusp function along a square-zero archimedean direction. -/
theorem cuspFunction_deriv (v : T.Space) (Z : ArchimedeanMatrix F (r + 1)) (hZ : Z * Z = 0)
    (x : Points F (r + 1)) :
    HasDerivAt (fun t : ℝ => cuspFunction F T v
        (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (cuspFunction F T (T.realization.envelopingAction (matrixGenerator F (r + 1) Z) v) x) 0 := by
  have h := hasDerivAt_evaluate_squareZero F T.realization v Z hZ
    (GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x)
  have h2 := cuspFunction_apply_eq F T
    (T.realization.envelopingAction (matrixGenerator F (r + 1) Z) v) x
  refine (h.congr_deriv h2.symm).congr_of_eventuallyEq (Filter.Eventually.of_forall fun t => ?_)
  have e1 := cuspFunction_apply_eq F T v
    (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t))
  have e3 : GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)
      (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) =
      GeneralLinearGroupPoints.adelicHomeomorph F (r + 1) x * AdelicGL.ofInfinite F (r + 1)
        (ArchimedeanGL.squareZeroElement (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)) := by
    rw [map_mul, adelicHomeomorph_archPoint]
  exact e1.trans (congrArg (evaluate F (r + 1) (T.realization.toContinuous v)) e3)

theorem cuspSpace_deriv (f : cuspSpace F T) (Z : ArchimedeanMatrix F (r + 1)) (hZ : Z * Z = 0)
    (x : Points F (r + 1)) :
    HasDerivAt (fun t : ℝ => (f : Points F (r + 1) → ℂ)
        (x * archPoint F (r + 1) (t • Z) (ArchimedeanGL.smul_mul_smul_eq_zero hZ t)))
      (((cuspDerivative F T Z f : cuspSpace F T) : Points F (r + 1) → ℂ) x) 0 := by
  have h := cuspFunction_deriv F T ((cuspEquiv F T).symm f) Z hZ x
  have e := coe_eq_cuspFunction F T f
  have e' := congrFun (coe_cuspDerivative F T Z f) x
  refine (h.congr_deriv e'.symm).congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun t => congrFun e _)

/-- **The cusp functions of `T` form a Whittaker decay class.** -/
theorem whittakerDecayClass_cuspSpace :
    WhittakerDecayClass F r (cuspSpace F T) (cuspDerivative F T) :=
  ⟨cuspSpace_continuous F T, cuspSpace_rational F T, cuspSpace_level F T,
    cuspSpace_bounded F T, cuspSpace_deriv F T⟩

end Realization

section Expansion

/-- **The Whittaker expansion of the vectors of an actual cuspidal realization.** -/
theorem cuspidalWhittakerExpansion : CuspidalWhittakerExpansion F T := by
  intro ψ hψ v g
  have hmaj : HasWhittakerMajorants F r ψ (cuspFunction F T v) :=
    whittakerMajorantsStatement_proof F r (cuspSpace F T) (cuspDerivative F T)
      (whittakerDecayClass_cuspSpace F T) ψ hψ (cuspEquiv F T v)
  have hsum : ∀ (k : ℕ) (hk : k ≤ r) (x : Points F (r + 1)),
      Summable fun q : UnipotentRationalCosets F k =>
        ‖whittaker F r ψ (cuspFunction F T v) (padRational F (Nat.le_succ_of_le hk) q.out * x)‖ := by
    intro k hk x
    obtain ⟨b, hb, hle⟩ := hmaj k hk {x} isCompact_singleton
    exact Summable.of_nonneg_of_le (fun _ => norm_nonneg _) (fun q => hle q x rfl) hb
  have htop : CuspidalWhittaker.LevelPropsB r (fun g =>
      cuspFunction F T v ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) := by
    have h := (CuspidalWhittaker.levelProps_top (T.realization.toContinuous v)
      (fun a b h ha hb g => T.realization.constantTerm_eq_zero T.cuspidal h ha hb v g)).levelPropsB
    have e : (fun g => cuspFunction F T v
        ((GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)).symm g)) =
        evaluate F (r + 1) (T.realization.toContinuous v) := by
      funext g
      rw [cuspFunction_apply_eq, ContinuousMulEquiv.apply_symm_apply]
    rw [e]
    exact h
  refine ⟨?_, ?_⟩
  · have e : (fun q : UnipotentRationalCosets F r =>
        ‖cuspWhittaker F T ψ v (cornerAdelicPoint F r q.out * g)‖) =
        fun q => ‖whittaker F r ψ (cuspFunction F T v)
          (padRational F (Nat.le_succ_of_le le_rfl) q.out * g)‖ := by
      funext q
      rw [← padRational_eq_cornerAdelicPoint]
      rfl
    rw [e]
    exact hsum r le_rfl g
  · exact hasSum_whittaker_of_levelPropsB F ψ (cuspFunction F T v) hψ
      (continuous_cuspFunction F T v) (fun k hk x => cuspFunction_rational_mul F T v hk x) htop
      hsum g

end Expansion

end Langlands.Global.RankinSelbergGlobal.Unfolding

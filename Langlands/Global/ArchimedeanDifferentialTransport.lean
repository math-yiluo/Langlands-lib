import Langlands.Global.ArchimedeanLieTransport
import Langlands.Global.ArchimedeanCenterFinite

/-! # Arithmetic pullback and actual archimedean differential actions -/

noncomputable section
universe uK uL uM

open scoped Classical TensorProduct Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanDifferentialTransport

open NumberField AdelicFunctoriality ArchimedeanGL ArchimedeanGLTransport
open ArchimedeanLieTransport

variable {K : Type uK} {L : Type uL} {M : Type uM}
variable [Field K] [NumberField K] [Field L] [NumberField L] [Field M] [NumberField M]

private theorem matrixRealLinearEquiv_mul (n : ℕ) (e : K ≃+* L)
    (a b : ArchimedeanMatrix K n) :
    matrixRealLinearEquiv n e (a * b) =
      matrixRealLinearEquiv n e a * matrixRealLinearEquiv n e b := by
  exact map_mul (mixedEquiv e).mapMatrix a b

private theorem matrixRealLinearEquiv_coordinates (n : ℕ) (e : K ≃+* L)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    matrixRealLinearEquiv n e (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) =
      (archimedeanGLCoordinates L n
        (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) :
          ArchimedeanMatrix L n) := by
  apply Matrix.ext
  intro i j
  change mixedEquiv e (InfiniteAdeleRing.ringEquiv_mixedSpace K (g i j)) =
    InfiniteAdeleRing.ringEquiv_mixedSpace L (infiniteAdeleEquiv e (g i j))
  change InfiniteAdeleRing.ringEquiv_mixedSpace L
      (infiniteAdeleEquiv e ((InfiniteAdeleRing.ringEquiv_mixedSpace K).symm
        (InfiniteAdeleRing.ringEquiv_mixedSpace K (g i j)))) = _
  rw [RingEquiv.symm_apply_apply]

private theorem coordinateExtension_comap (n : ℕ) (e : K ≃+* L)
    (f : SmoothFunctions L n) (h : ArchimedeanGL K n) :
    coordinateExtension L n f (matrixRealLinearEquiv n e (h : ArchimedeanMatrix K n)) =
      (smoothComap n e f).val ((archimedeanGLCoordinates K n).symm h) := by
  change coordinateExtension L n f
      ((Matrix.GeneralLinearGroup.map (mixedEquiv e).toRingHom h :
        ArchimedeanGL L n) : ArchimedeanMatrix L n) = _
  rw [coordinateExtension_apply, ← coordinates_arithmetic_map n e h,
    ContinuousMulEquiv.symm_apply_apply]
  rfl

/-- Arithmetic pullback intertwines the actual real matrix directional derivatives. -/
theorem smoothComap_smoothDifferential (n : ℕ) (e : K ≃+* L)
    (X : RealLieAlgebra K n) (f : SmoothFunctions L n) :
    smoothComap n e (smoothDifferential L n (realLieEquiv n e X) f) =
      smoothDifferential K n X (smoothComap n e f) := by
  apply Subtype.ext
  funext g
  change (smoothDifferential L n (realLieEquiv n e X) f).val
      (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) =
    (smoothDifferential K n X (smoothComap n e f)).val g
  rw [smoothDifferential_eq_of_extension K n X (smoothComap n e f)
    (fun a => coordinateExtension L n f (matrixRealLinearEquiv n e a))
    (coordinateExtension_comap n e f)]
  have hdiff : DifferentiableAt ℝ (coordinateExtension L n f)
      (matrixRealLinearEquiv n e
        (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n)) := by
    rw [matrixRealLinearEquiv_coordinates]
    exact (coordinateExtension_contDiffAt L n f _).differentiableAt (by simp)
  rw [fderiv_fun_comp _ hdiff (matrixRealLinearEquiv n e).toContinuousLinearMap.differentiableAt]
  change _ = fderiv ℝ (coordinateExtension L n f)
    (matrixRealLinearEquiv n e (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))
    ((fderiv ℝ (matrixRealLinearEquiv n e).toContinuousLinearMap
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n))
      ((archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) *
        realLieAlgebraToMatrix K n X))
  rw [ContinuousLinearMap.fderiv]
  simp only [ContinuousLinearEquiv.coe_coe, matrixRealLinearEquiv_mul,
    matrixRealLinearEquiv_coordinates, ← realLieEquiv_matrix, smoothDifferential_apply]

/-- Fixed complex coefficients extend real differential covariance by tensor induction. -/
theorem smoothComap_complexSmoothLieAction (n : ℕ) (e : K ≃+* L)
    (X : ComplexLieAlgebra K n) (f : SmoothFunctions L n) :
    smoothComap n e (complexSmoothLieAction L n (complexLieEquiv n e X) f) =
      complexSmoothLieAction K n X (smoothComap n e f) := by
  induction X using TensorProduct.inductionOn with
  | tmul z X =>
    simp only [complexLieEquiv_tmul, complexSmoothLieAction_tmul,
      LinearMap.smul_apply, map_smul]
    rw [smoothComap_smoothDifferential]
  | add X Y hX hY =>
    simp only [map_add, LinearMap.add_apply, hX, hY]

/-- Pullback intertwines every element of the actual universal enveloping algebra. -/
theorem smoothComap_envelopingAction (n : ℕ) (e : K ≃+* L)
    (a : EnvelopingAlgebra K n) (f : SmoothFunctions L n) :
    smoothComap n e (envelopingAction L n (envelopingEquiv n e a) f) =
      envelopingAction K n a (smoothComap n e f) := by
  revert f
  refine Quotient.inductionOn a ?_
  intro t
  let q := UniversalEnvelopingAlgebra.mkAlgHom ℂ (ComplexLieAlgebra K n)
  change ∀ f : SmoothFunctions L n,
    smoothComap n e (envelopingAction L n (envelopingEquiv n e (q t)) f) =
      envelopingAction K n (q t) (smoothComap n e f)
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    intro f
    simp [Algebra.algebraMap_eq_smul_one]
  | ι X =>
    intro f
    change smoothComap n e
        (envelopingAction L n (envelopingEquiv n e (envelopingGenerator K n X)) f) =
      envelopingAction K n (envelopingGenerator K n X) (smoothComap n e f)
    simpa only [envelopingAction_generator, envelopingEquiv_generator] using
      smoothComap_complexSmoothLieAction n e X f
  | mul a b ha hb =>
    intro f
    simp only [map_mul, Module.End.mul_apply]
    rw [ha, hb]
  | add a b ha hb =>
    intro f
    simp only [map_add, LinearMap.add_apply, ha, hb]

/-- Restrict the covariance equation to the actual enveloping center. -/
theorem smoothComap_centerAction (n : ℕ) (e : K ≃+* L)
    (z : EnvelopingCenter K n) (f : SmoothFunctions L n) :
    smoothComap n e (centerAction L n (centerEquiv n e z) f) =
      centerAction K n z (smoothComap n e f) := by
  simpa only [centerAction_apply, centerInclusion_centerEquiv] using
    smoothComap_envelopingAction n e (centerInclusion K n z) f

/-- The entire actual center orbit is the linear image of the target center orbit. -/
theorem centerOrbitSpan_smoothComap (n : ℕ) (e : K ≃+* L)
    (f : SmoothFunctions L n) :
    centerOrbitSpan K n (smoothComap n e f) =
      (centerOrbitSpan L n f).map (smoothComap n e) := by
  rw [centerOrbitSpan_eq_range, centerOrbitSpan_eq_range]
  apply le_antisymm
  · rintro _ ⟨z, rfl⟩
    exact ⟨centerAction L n (centerEquiv n e z) f,
      ⟨centerEquiv n e z, rfl⟩, smoothComap_centerAction n e z f⟩
  · rintro _ ⟨h, ⟨z, rfl⟩, rfl⟩
    obtain ⟨w, rfl⟩ := (centerEquiv n e).surjective z
    exact ⟨w, (smoothComap_centerAction n e w f).symm⟩

/-- Arithmetic pullback restricts to an equivalence of the actual center-orbit spans. -/
def centerOrbitEquiv (n : ℕ) (e : K ≃+* L) (f : SmoothFunctions L n) :
    centerOrbitSpan L n f ≃ₗ[ℂ] centerOrbitSpan K n (smoothComap n e f) :=
  (smoothEquiv n e).ofSubmodules _ _ (centerOrbitSpan_smoothComap n e f).symm

@[simp] theorem centerOrbitEquiv_apply (n : ℕ) (e : K ≃+* L)
    (f : SmoothFunctions L n) (h : centerOrbitSpan L n f) :
    (centerOrbitEquiv n e f h).val = smoothComap n e h.val := rfl

/-- Center finiteness is preserved and reflected, without a finiteness assumption on all functions. -/
theorem isCenterFinite_smoothComap_iff (n : ℕ) (e : K ≃+* L)
    (f : SmoothFunctions L n) :
    IsCenterFinite K n (smoothComap n e f) ↔ IsCenterFinite L n f :=
  (LinearMap.finite_iff_of_bijective
    (centerOrbitEquiv n e f).toLinearMap (centerOrbitEquiv n e f).bijective).symm

/-- The actual center-finite subspace is carried onto the corresponding source subspace. -/
theorem centerFiniteFunctions_map (n : ℕ) (e : K ≃+* L) :
    (centerFiniteFunctions L n).map (smoothComap n e) = centerFiniteFunctions K n := by
  ext f
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact (isCenterFinite_smoothComap_iff n e h).mpr hh
  · intro hf
    exact ⟨smoothComap n e.symm f,
      (isCenterFinite_smoothComap_iff n e.symm f).mpr hf,
      smoothComap_apply_symm n e f⟩

/-- Genuine arithmetic pullback on the existing subspaces of center-finite smooth functions. -/
def centerFiniteEquiv (n : ℕ) (e : K ≃+* L) :
    centerFiniteFunctions L n ≃ₗ[ℂ] centerFiniteFunctions K n :=
  (smoothEquiv n e).ofSubmodules _ _ (centerFiniteFunctions_map n e)

@[simp] theorem centerFiniteEquiv_apply (n : ℕ) (e : K ≃+* L)
    (f : centerFiniteFunctions L n) :
    (centerFiniteEquiv n e f).val = smoothComap n e f.val := rfl

@[simp] theorem centerFiniteEquiv_symm_apply (n : ℕ) (e : K ≃+* L)
    (f : centerFiniteFunctions K n) :
    ((centerFiniteEquiv n e).symm f).val = smoothComap n e.symm f.val := rfl

@[simp] theorem evaluate_centerFiniteEquiv (n : ℕ) (e : K ≃+* L)
    (f : centerFiniteFunctions L n)
    (g : Matrix.GeneralLinearGroup (Fin n) (InfiniteAdeleRing K)) :
    (centerFiniteEquiv n e f).val.val g =
      f.val.val (Matrix.GeneralLinearGroup.map (infiniteAdeleEquiv e).toRingHom g) := rfl

@[simp] theorem centerFiniteEquiv_refl (n : ℕ) :
    centerFiniteEquiv n (RingEquiv.refl K) = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  exact smoothComap_refl n f.val

theorem centerFiniteEquiv_trans (n : ℕ) (e : K ≃+* L) (a : L ≃+* M) :
    centerFiniteEquiv n (e.trans a) =
      (centerFiniteEquiv n a).trans (centerFiniteEquiv n e) := by
  apply LinearEquiv.ext
  intro f
  apply Subtype.ext
  exact smoothComap_trans n e a f.val

@[simp] theorem centerFiniteEquiv_symm (n : ℕ) (e : K ≃+* L) :
    centerFiniteEquiv n e.symm = (centerFiniteEquiv n e).symm := by
  apply LinearEquiv.ext
  intro f
  rfl

end Langlands.Global.ArchimedeanDifferentialTransport

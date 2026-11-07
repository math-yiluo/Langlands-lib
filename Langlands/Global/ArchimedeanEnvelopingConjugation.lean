import Langlands.Global.ArchimedeanEnvelopingAction

/-!
# Complex conjugation of the archimedean enveloping algebra and smooth functions

Complex conjugation of the scalar factor of `ℂ ⊗[ℝ] 𝔤` extends to a conjugate-linear
ring involution of the universal enveloping algebra. Pointwise conjugation of smooth
functions on the archimedean group intertwines the genuine enveloping action with this
involution.
-/

noncomputable section
universe u
open scoped Classical TensorProduct ComplexConjugate Manifold ContDiff Matrix.Norms.Operator
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Conjugation of the complex scalar factor of the complexified real Lie algebra. -/
def complexConj : ComplexLieAlgebra K n →ₗ[ℝ] ComplexLieAlgebra K n :=
  TensorProduct.map Complex.conjAe.toLinearMap LinearMap.id

@[simp]
theorem complexConj_tmul (z : ℂ) (X : RealLieAlgebra K n) :
    complexConj K n (z ⊗ₜ[ℝ] X) = conj z ⊗ₜ[ℝ] X := rfl

@[simp]
theorem complexConj_complexify (X : RealLieAlgebra K n) :
    complexConj K n (complexify K n X) = complexify K n X := by
  simp [complexify_apply]

@[simp]
theorem complexConj_complexConj (x : ComplexLieAlgebra K n) :
    complexConj K n (complexConj K n x) = x := by
  induction x using TensorProduct.inductionOn with
  | tmul z X => simp
  | add x y hx hy => simp only [map_add, hx, hy]

theorem complexConj_smul (c : ℂ) (x : ComplexLieAlgebra K n) :
    complexConj K n (c • x) = conj c • complexConj K n x := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    rw [TensorProduct.smul_tmul', complexConj_tmul, complexConj_tmul,
      TensorProduct.smul_tmul', smul_eq_mul, smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

theorem complexConj_lie (x y : ComplexLieAlgebra K n) :
    complexConj K n ⁅x, y⁆ = ⁅complexConj K n x, complexConj K n y⁆ := by
  induction x using TensorProduct.inductionOn with
  | tmul z X =>
    induction y using TensorProduct.inductionOn with
    | tmul w Y => simp only [complexLieAlgebra_lie_tmul, complexConj_tmul, map_mul]
    | add y y' hy hy' => rw [LieRing.lie_add, map_add, map_add, LieRing.lie_add, hy, hy']
  | add x x' hx hx' => rw [add_lie, map_add, map_add, add_lie, hx, hx']

/-- The enveloping algebra with complex scalars acting through their conjugates. -/
def ConjEnvelopingAlgebra : Type u := EnvelopingAlgebra K n

instance : Ring (ConjEnvelopingAlgebra K n) :=
  inferInstanceAs (Ring (EnvelopingAlgebra K n))

instance : Algebra ℂ (ConjEnvelopingAlgebra K n) :=
  RingHom.toAlgebra' ((algebraMap ℂ (EnvelopingAlgebra K n)).comp (starRingEnd ℂ) :
      ℂ →+* ConjEnvelopingAlgebra K n)
    (fun c x => Algebra.commutes (R := ℂ) (A := EnvelopingAlgebra K n) (conj c) x)

attribute [local instance 100] LieRing.ofAssociativeRing

/-- Conjugated Lie generators, linear for the conjugated scalar action. -/
def conjGenerator : ComplexLieAlgebra K n →ₗ⁅ℂ⁆ ConjEnvelopingAlgebra K n where
  toFun x := (envelopingGenerator K n (complexConj K n x) : EnvelopingAlgebra K n)
  map_add' x y := by
    change envelopingGenerator K n (complexConj K n (x + y)) =
      envelopingGenerator K n (complexConj K n x) + envelopingGenerator K n (complexConj K n y)
    rw [map_add, map_add]
  map_smul' c x := by
    change envelopingGenerator K n (complexConj K n (c • x)) =
      algebraMap ℂ (EnvelopingAlgebra K n) (conj c) *
        envelopingGenerator K n (complexConj K n x)
    rw [complexConj_smul, ← Algebra.smul_def]
    exact map_smul (envelopingGenerator K n) (conj c) (complexConj K n x)
  map_lie' := by
    intro x y
    change envelopingGenerator K n (complexConj K n ⁅x, y⁆) =
      envelopingGenerator K n (complexConj K n x) * envelopingGenerator K n (complexConj K n y) -
        envelopingGenerator K n (complexConj K n y) * envelopingGenerator K n (complexConj K n x)
    rw [complexConj_lie, envelopingGenerator_lie]

/-- The lift of the conjugated generators, an algebra map into the conjugate algebra. -/
def envelopingConjAlgHom : EnvelopingAlgebra K n →ₐ[ℂ] ConjEnvelopingAlgebra K n :=
  UniversalEnvelopingAlgebra.lift ℂ (conjGenerator K n)

/-- Complex conjugation of the universal enveloping algebra, as a ring endomorphism. -/
def envelopingConj : EnvelopingAlgebra K n →+* EnvelopingAlgebra K n :=
  ((envelopingConjAlgHom K n).toRingHom : EnvelopingAlgebra K n →+* ConjEnvelopingAlgebra K n)

theorem envelopingConj_apply (u : EnvelopingAlgebra K n) :
    envelopingConj K n u = (envelopingConjAlgHom K n u : EnvelopingAlgebra K n) := rfl

@[simp]
theorem envelopingConj_generator (x : ComplexLieAlgebra K n) :
    envelopingConj K n (envelopingGenerator K n x) =
      envelopingGenerator K n (complexConj K n x) := by
  rw [envelopingConj_apply]
  exact UniversalEnvelopingAlgebra.lift_ι_apply ℂ (conjGenerator K n) x

@[simp]
theorem envelopingConj_algebraMap (c : ℂ) :
    envelopingConj K n (algebraMap ℂ (EnvelopingAlgebra K n) c) =
      algebraMap ℂ (EnvelopingAlgebra K n) (conj c) := by
  rw [envelopingConj_apply]
  exact (envelopingConjAlgHom K n).commutes c

theorem envelopingConj_smul (c : ℂ) (u : EnvelopingAlgebra K n) :
    envelopingConj K n (c • u) = conj c • envelopingConj K n u := by
  rw [Algebra.smul_def, map_mul, envelopingConj_algebraMap, ← Algebra.smul_def]

@[simp]
theorem envelopingConj_envelopingConj (u : EnvelopingAlgebra K n) :
    envelopingConj K n (envelopingConj K n u) = u := by
  let Ψ : EnvelopingAlgebra K n →ₐ[ℂ] EnvelopingAlgebra K n :=
    { (envelopingConj K n).comp (envelopingConj K n) with
      commutes' := fun c => by
        change envelopingConj K n (envelopingConj K n (algebraMap ℂ _ c)) = algebraMap ℂ _ c
        rw [envelopingConj_algebraMap, envelopingConj_algebraMap, Complex.conj_conj] }
  have h : Ψ = AlgHom.id ℂ (EnvelopingAlgebra K n) := by
    apply UniversalEnvelopingAlgebra.hom_ext ℂ
    apply LieHom.ext
    intro x
    change envelopingConj K n (envelopingConj K n (envelopingGenerator K n x)) =
      envelopingGenerator K n x
    rw [envelopingConj_generator, envelopingConj_generator, complexConj_complexConj]
  exact congrArg (fun φ : EnvelopingAlgebra K n →ₐ[ℂ] EnvelopingAlgebra K n => φ u) h

theorem envelopingConj_bijective : Function.Bijective (envelopingConj K n) :=
  Function.Involutive.bijective (envelopingConj_envelopingConj K n)

/-- Conjugation preserves the algebra center. -/
theorem envelopingConj_mem_center {z : EnvelopingAlgebra K n}
    (hz : z ∈ Subalgebra.center ℂ (EnvelopingAlgebra K n)) :
    envelopingConj K n z ∈ Subalgebra.center ℂ (EnvelopingAlgebra K n) := by
  rw [Subalgebra.mem_center_iff] at hz ⊢
  intro a
  obtain ⟨b, rfl⟩ := (envelopingConj_bijective K n).2 a
  rw [← map_mul, ← map_mul, hz b]

/-- Conjugation of the center of the enveloping algebra. -/
def centerConj (z : EnvelopingCenter K n) : EnvelopingCenter K n :=
  ⟨envelopingConj K n z.val, envelopingConj_mem_center K n z.property⟩

@[simp]
theorem centerInclusion_centerConj (z : EnvelopingCenter K n) :
    centerInclusion K n (centerConj K n z) = envelopingConj K n (centerInclusion K n z) := rfl

@[simp]
theorem centerConj_centerConj (z : EnvelopingCenter K n) :
    centerConj K n (centerConj K n z) = z :=
  Subtype.ext (envelopingConj_envelopingConj K n z.val)

variable [NumberField K]

/-- Pointwise complex conjugation of smooth functions on the archimedean group. -/
def smoothConj : SmoothFunctions K n →ₛₗ[starRingEnd ℂ] SmoothFunctions K n where
  toFun f := ⟨fun g => conj (f.val g), by
    change ContMDiff 𝓘(ℝ, ArchimedeanMatrix K n) 𝓘(ℝ, ℂ) ∞
      (fun x : ArchimedeanGL K n => conj (f.val ((archimedeanGLCoordinates K n).symm x)))
    exact (Complex.conjCLE.contDiff.contMDiff).comp f.property⟩
  map_add' f h := Subtype.ext (funext fun _ => map_add (starRingEnd ℂ) _ _)
  map_smul' c f := Subtype.ext (funext fun _ => map_mul (starRingEnd ℂ) _ _)

@[simp]
theorem smoothConj_val (f : SmoothFunctions K n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K)) :
    (smoothConj K n f).val g = conj (f.val g) := rfl

@[simp]
theorem smoothConj_smoothConj (f : SmoothFunctions K n) :
    smoothConj K n (smoothConj K n f) = f :=
  Subtype.ext (funext fun _ => Complex.conj_conj _)

theorem smoothConj_smoothRightAction
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing K))
    (f : SmoothFunctions K n) :
    smoothConj K n (smoothRightAction K n g f) = smoothRightAction K n g (smoothConj K n f) :=
  rfl

/-- Real directional derivatives commute with complex conjugation. -/
theorem smoothConj_smoothDifferential (X : RealLieAlgebra K n) (f : SmoothFunctions K n) :
    smoothConj K n (smoothDifferential K n X f) = smoothDifferential K n X (smoothConj K n f) := by
  apply Subtype.ext
  funext g
  rw [smoothConj_val, smoothDifferential_apply, smoothDifferential_apply]
  have hd : DifferentiableAt ℝ (coordinateExtension K n f)
      (archimedeanGLCoordinates K n g : ArchimedeanMatrix K n) :=
    (coordinateExtension_contDiffAt K n f (archimedeanGLCoordinates K n g)).differentiableAt
      (by simp)
  have hext : coordinateExtension K n (smoothConj K n f) =
      (Complex.conjCLE : ℂ →L[ℝ] ℂ) ∘ coordinateExtension K n f := rfl
  rw [hext, ((Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp _ hd.hasFDerivAt).fderiv]
  rfl

/-- Conjugation of an operator on smooth functions by pointwise conjugation. -/
def conjEnd (A : Module.End ℂ (SmoothFunctions K n)) : Module.End ℂ (SmoothFunctions K n) :=
  ((smoothConj K n).comp A).comp (smoothConj K n)

@[simp]
theorem conjEnd_apply (A : Module.End ℂ (SmoothFunctions K n)) (f : SmoothFunctions K n) :
    conjEnd K n A f = smoothConj K n (A (smoothConj K n f)) := rfl

theorem conjEnd_smul (c : ℂ) (A : Module.End ℂ (SmoothFunctions K n)) :
    conjEnd K n (c • A) = conj c • conjEnd K n A := by
  apply LinearMap.ext
  intro f
  simp only [conjEnd_apply, LinearMap.smul_apply, LinearMap.map_smulₛₗ]

theorem conjEnd_mul (A B : Module.End ℂ (SmoothFunctions K n)) :
    conjEnd K n (A * B) = conjEnd K n A * conjEnd K n B := by
  apply LinearMap.ext
  intro f
  simp only [conjEnd_apply, Module.End.mul_apply, smoothConj_smoothConj]

theorem conjEnd_conjEnd (A : Module.End ℂ (SmoothFunctions K n)) :
    conjEnd K n (conjEnd K n A) = A := by
  apply LinearMap.ext
  intro f
  simp only [conjEnd_apply, smoothConj_smoothConj]

theorem conjEnd_smoothDifferential (X : RealLieAlgebra K n) :
    conjEnd K n (smoothDifferential K n X) = smoothDifferential K n X := by
  apply LinearMap.ext
  intro f
  rw [conjEnd_apply, smoothConj_smoothDifferential, smoothConj_smoothConj]

/-- The genuine enveloping action intertwines conjugation of the enveloping algebra with
pointwise conjugation of smooth functions. -/
theorem envelopingAction_envelopingConj (u : EnvelopingAlgebra K n) :
    envelopingAction K n (envelopingConj K n u) = conjEnd K n (envelopingAction K n u) := by
  let Ψ : EnvelopingAlgebra K n →ₐ[ℂ] Module.End ℂ (SmoothFunctions K n) :=
    { toFun := fun v => conjEnd K n (envelopingAction K n (envelopingConj K n v))
      map_one' := by
        apply LinearMap.ext
        intro f
        simp only [map_one, conjEnd_apply, Module.End.one_apply, smoothConj_smoothConj]
      map_mul' := fun v w => by
        simp only [map_mul, conjEnd_mul]
      map_zero' := by
        apply LinearMap.ext
        intro f
        simp only [map_zero, conjEnd_apply, LinearMap.zero_apply]
      map_add' := fun v w => by
        apply LinearMap.ext
        intro f
        simp only [map_add, conjEnd_apply, LinearMap.add_apply]
      commutes' := fun c => by
        apply LinearMap.ext
        intro f
        simp only [envelopingConj_algebraMap, AlgHom.commutes, conjEnd_apply,
          Module.algebraMap_end_apply, LinearMap.map_smulₛₗ, smoothConj_smoothConj,
          RingHomCompTriple.comp_apply, RingHom.id_apply] }
  have hΨ : Ψ = envelopingAction K n := by
    refine (UniversalEnvelopingAlgebra.lift_unique ℂ (complexSmoothLieAction K n) Ψ).mp ?_
    funext x
    change conjEnd K n (envelopingAction K n (envelopingConj K n (envelopingGenerator K n x))) =
      complexSmoothLieAction K n x
    rw [envelopingConj_generator, envelopingAction_generator]
    induction x using TensorProduct.inductionOn with
    | tmul z X =>
      rw [complexConj_tmul, complexSmoothLieAction_tmul, complexSmoothLieAction_tmul,
        conjEnd_smul, conjEnd_smoothDifferential, Complex.conj_conj]
    | add x y hx hy =>
      rw [map_add, map_add, map_add]
      apply LinearMap.ext
      intro f
      have hx' := LinearMap.congr_fun hx f
      have hy' := LinearMap.congr_fun hy f
      simp only [conjEnd_apply, LinearMap.add_apply, map_add] at hx' hy' ⊢
      rw [hx', hy']
  have h := congrArg (fun φ : EnvelopingAlgebra K n →ₐ[ℂ] Module.End ℂ (SmoothFunctions K n) =>
    φ (envelopingConj K n u)) hΨ
  change conjEnd K n (envelopingAction K n (envelopingConj K n (envelopingConj K n u))) =
    envelopingAction K n (envelopingConj K n u) at h
  rw [envelopingConj_envelopingConj] at h
  exact h.symm

theorem smoothConj_envelopingAction (u : EnvelopingAlgebra K n) (f : SmoothFunctions K n) :
    smoothConj K n (envelopingAction K n u f) =
      envelopingAction K n (envelopingConj K n u) (smoothConj K n f) := by
  rw [envelopingAction_envelopingConj, conjEnd_apply, smoothConj_smoothConj]

theorem smoothConj_centerAction (z : EnvelopingCenter K n) (f : SmoothFunctions K n) :
    smoothConj K n (centerAction K n z f) =
      centerAction K n (centerConj K n z) (smoothConj K n f) := by
  rw [centerAction_apply, centerAction_apply, centerInclusion_centerConj]
  exact smoothConj_envelopingAction K n _ f

end Langlands.Global.ArchimedeanGL

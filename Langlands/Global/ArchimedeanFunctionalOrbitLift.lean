import Langlands.Global.ArchimedeanOrbitDerivativeInterchange
import Langlands.Global.GeneralLinearInfiniteAdelicDifferential
import Langlands.Representation.Archimedean.SmoothFunctionalOrbit

/-! # Smooth scalar lifts of derivative-continuous Hilbert evaluations -/

noncomputable section
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false

open scoped Classical Manifold ContDiff Matrix.Norms.Operator

namespace Langlands.Global.ArchimedeanGL

open Langlands.Archimedean Langlands.Geometry.Manifold

universe u v uV

section EnvelopingCovariance

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A linear scalar lift that intertwines the real generators is covariant
for the full complex enveloping action. -/
theorem envelopingCovariance_of_realGenerators
    (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V) (C : V →ₗ[ℂ] SmoothFunctions F n)
    (hgen : ∀ (X : RealLieAlgebra F n) (w : V),
      C (D (envelopingGenerator F n (complexify F n X)) w) =
        envelopingAction F n (envelopingGenerator F n (complexify F n X)) (C w))
    (a : EnvelopingAlgebra F n) (w : V) :
    C (D a w) = envelopingAction F n a (C w) := by
  let P (b : EnvelopingAlgebra F n) : Prop :=
    ∀ z : V, C (D b z) = envelopingAction F n b (C z)
  suffices h : P a from h w
  apply enveloping_real_left_induction F n
  · intro z
    rw [map_one, Module.End.one_apply, envelopingAction_one]
  · intro b c hb hc z
    rw [map_add, LinearMap.add_apply, map_add, hb z, hc z, map_add, LinearMap.add_apply]
  · intro c b hb z
    rw [map_smul, LinearMap.smul_apply, map_smul, hb z, map_smul, LinearMap.smul_apply]
  · intro X b hb z
    rw [map_mul, Module.End.mul_apply, hgen, hb z, envelopingAction_mul]

end EnvelopingCovariance

variable (F : Type u) [Field F] [NumberField F] (n : ℕ)
  {E : Type v} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
  (π : ArchimedeanGL F n →* (E →L[ℂ] E))

local notation "I" => 𝓘(ℝ, ArchimedeanMatrix F n)

local notation "V∞" => Langlands.Archimedean.smoothVectors I π

/-- Scalar evaluation of the genuine orbit gives a smooth function on the
original infinite adelic group. -/
def functionalOrbitLift
    (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
    (hdense : DenseRange (Subtype.val : V∞ → E))
    (L : V∞ →ₗ[ℂ] ℂ) (hL : IsContinuousOnSmoothVectors I π L) :
    V∞ →ₗ[ℂ] SmoothFunctions F n :=
  (LinearMap.pi fun a : InfiniteAdelicGL F n =>
    L.comp (smoothRepresentation I π (archimedeanGLCoordinates F n a))).codRestrict
      (smoothFunctions F n) fun w => by
        change ContMDiff I 𝓘(ℝ, ℂ) ∞ (fun g : ArchimedeanGL F n =>
          L (smoothRepresentation I π
            (archimedeanGLCoordinates F n ((archimedeanGLCoordinates F n).symm g)) w))
        simpa only [ContinuousMulEquiv.apply_symm_apply] using
          (SmoothFunctionalOrbit.contMDiff_mfderiv_smoothFunctional_orbit
            π hπ hdense L hL w).1

variable (hπ : ∀ g u v, Inner.inner ℂ (π g u) (π g v) = Inner.inner ℂ u v)
variable (hdense : DenseRange (Subtype.val : Langlands.Archimedean.smoothVectors
  𝓘(ℝ, ArchimedeanMatrix F n) π → E))
variable (L : Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F n) π →ₗ[ℂ] ℂ)
variable (hL : IsContinuousOnSmoothVectors 𝓘(ℝ, ArchimedeanMatrix F n) π L)

@[simp]
theorem functionalOrbitLift_apply (w : V∞) (a : InfiniteAdelicGL F n) :
    (functionalOrbitLift F n π hπ hdense L hL w).val a =
      L (smoothRepresentation I π (archimedeanGLCoordinates F n a) w) := rfl

/-- The published invariant differential on scalar functions is the genuine
orbit derivative transported through the evaluation. -/
theorem smoothDifferential_functionalOrbitLift (X : RealLieAlgebra F n)
    (w : V∞) :
    smoothDifferential F n X (functionalOrbitLift F n π hπ hdense L hL w) =
      functionalOrbitLift F n π hπ hdense L hL
        (smoothLieDerivative I π (realLieAlgebraToMatrix F n X) w) := by
  apply Subtype.ext
  funext a
  let g := archimedeanGLCoordinates F n a
  let Z := realLieAlgebraToMatrix F n X
  let f : ArchimedeanGL F n → ℂ := fun h => L (smoothRepresentation I π h w)
  obtain ⟨hf, hd⟩ := SmoothFunctionalOrbit.contMDiff_mfderiv_smoothFunctional_orbit
    π hπ hdense L hL w
  have he : (fun h => (functionalOrbitLift F n π hπ hdense L hL w).val
      ((archimedeanGLCoordinates F n).symm h)) = f := by
    funext h
    simp only [functionalOrbitLift_apply, ContinuousMulEquiv.apply_symm_apply, f]
  calc
    _ = mvfderiv I f g ((g : ArchimedeanMatrix F n) * Z) := by
      rw [smoothDifferential_eq_mfderiv, he]
      rfl
    _ = groupDirectionalValue I Z f g := (units_groupDirectionalValue Z hf g).symm
    _ = _ := hd g Z

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (D : EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ V)
variable (j : V →ₗ[ℂ] Langlands.Archimedean.smoothVectors 𝓘(ℝ, ArchimedeanMatrix F n) π)

/-- Agreement on the real generators gives covariance of the original scalar
orbit lift under every supplied enveloping operator. -/
theorem functionalOrbitLift_envelopingAction
    (hgen : ∀ (X : RealLieAlgebra F n) (w : V),
      j (D (envelopingGenerator F n (complexify F n X)) w) =
        smoothLieDerivative I π (realLieAlgebraToMatrix F n X) (j w))
    (a : EnvelopingAlgebra F n) (w : V) :
    functionalOrbitLift F n π hπ hdense L hL (j (D a w)) =
      envelopingAction F n a (functionalOrbitLift F n π hπ hdense L hL (j w)) := by
  let C : V →ₗ[ℂ] SmoothFunctions F n := (functionalOrbitLift F n π hπ hdense L hL).comp j
  have hC (X : RealLieAlgebra F n) (z : V) :
      C (D (envelopingGenerator F n (complexify F n X)) z) =
        envelopingAction F n (envelopingGenerator F n (complexify F n X)) (C z) := by
    change functionalOrbitLift F n π hπ hdense L hL
      (j (D (envelopingGenerator F n (complexify F n X)) z)) = _
    rw [hgen X z, envelopingAction_real_generator]
    exact (smoothDifferential_functionalOrbitLift F n π hπ hdense L hL X (j z)).symm
  exact envelopingCovariance_of_realGenerators F n D C hC a w

end Langlands.Global.ArchimedeanGL

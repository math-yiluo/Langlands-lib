import Langlands.Global.ArchimedeanEnvelopingAction

/-! # Multiplication by a smooth character and the archimedean enveloping action

Let `c` be a character of the archimedean matrix group whose values form a smooth function.
Multiplication by `c` preserves smooth functions. By the Leibniz rule and the character
property, `D_X (c f) = c (D_X f + λ(X) f)`, where `λ(X)` is the derivative of `c` at the
identity in the direction `X`. The commutator law of the directional differentials shows
that `λ` vanishes on brackets, so `U ↦ U + λ(U)` extends to an algebra automorphism `θ` of
the universal enveloping algebra, and `D(u) ∘ c = c ∘ D(θ u)` for every `u`. The
automorphism `θ` preserves the center.
-/

noncomputable section

universe u

open scoped Classical Manifold ContDiff Matrix.Norms.Operator TensorProduct
open Topology

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.ArchimedeanGL

variable {F : Type u} [Field F] [NumberField F] {n : ℕ}

attribute [local instance 100] LieRing.ofAssociativeRing

/-- The pointwise product of two smooth functions is smooth. -/
theorem mul_mem_smoothFunctions (f h : SmoothFunctions F n) :
    (fun g => f.val g * h.val g) ∈ smoothFunctions F n := by
  change ContMDiff 𝓘(ℝ, ArchimedeanMatrix F n) 𝓘(ℝ, ℂ) ∞
    (fun x : ArchimedeanGL F n => f.val ((archimedeanGLCoordinates F n).symm x) *
      h.val ((archimedeanGLCoordinates F n).symm x))
  intro x
  exact contDiff_mul.contDiffAt.comp_contMDiffAt ((f.property x).prodMk_space (h.property x))

section Shift

variable (μ : ComplexLieAlgebra F n →ₗ[ℂ] ℂ)

/-- The Lie map `U ↦ U + μ(U)` into the enveloping algebra, for a linear form `μ`
vanishing on brackets. -/
def envelopingShiftLie (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ EnvelopingAlgebra F n :=
  { (envelopingGenerator F n).toLinearMap +
      (Algebra.linearMap ℂ (EnvelopingAlgebra F n)).comp μ with
    map_lie' := by
      intro U V
      change envelopingGenerator F n ⁅U, V⁆ + algebraMap ℂ (EnvelopingAlgebra F n) (μ ⁅U, V⁆) =
        (envelopingGenerator F n U + algebraMap ℂ (EnvelopingAlgebra F n) (μ U)) *
            (envelopingGenerator F n V + algebraMap ℂ (EnvelopingAlgebra F n) (μ V)) -
          (envelopingGenerator F n V + algebraMap ℂ (EnvelopingAlgebra F n) (μ V)) *
            (envelopingGenerator F n U + algebraMap ℂ (EnvelopingAlgebra F n) (μ U))
      rw [hμ, map_zero, add_zero, envelopingGenerator_lie]
      have h1 := Algebra.commutes (μ U) (envelopingGenerator F n V)
      have h2 := Algebra.commutes (μ V) (envelopingGenerator F n U)
      have h3 : algebraMap ℂ (EnvelopingAlgebra F n) (μ U) *
          algebraMap ℂ (EnvelopingAlgebra F n) (μ V) =
          algebraMap ℂ (EnvelopingAlgebra F n) (μ V) *
            algebraMap ℂ (EnvelopingAlgebra F n) (μ U) :=
        ((Commute.all (μ U) (μ V)).map (algebraMap ℂ (EnvelopingAlgebra F n))).eq
      rw [add_mul, add_mul, mul_add, mul_add, mul_add, mul_add, h1, h2, h3]
      abel }

/-- The algebra endomorphism of the enveloping algebra extending `U ↦ U + μ(U)`. -/
def envelopingShift (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0) :
    EnvelopingAlgebra F n →ₐ[ℂ] EnvelopingAlgebra F n :=
  UniversalEnvelopingAlgebra.lift ℂ (envelopingShiftLie μ hμ)

omit [NumberField F] in
@[simp]
theorem envelopingShift_generator (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0)
    (U : ComplexLieAlgebra F n) :
    envelopingShift μ hμ (envelopingGenerator F n U) =
      envelopingGenerator F n U + algebraMap ℂ (EnvelopingAlgebra F n) (μ U) :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (envelopingShiftLie μ hμ) U

omit [NumberField F] in
theorem neg_lie_eq_zero (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0)
    (U V : ComplexLieAlgebra F n) :
    (-μ) ⁅U, V⁆ = 0 := by
  rw [LinearMap.neg_apply, hμ, neg_zero]

omit [NumberField F] in
/-- The shift by `-μ` is a left inverse of the shift by `μ`. -/
theorem envelopingShift_neg_comp (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0) :
    (envelopingShift (-μ) (neg_lie_eq_zero μ hμ)).comp (envelopingShift μ hμ) =
      AlgHom.id ℂ (EnvelopingAlgebra F n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro U
  change envelopingShift (-μ) (neg_lie_eq_zero μ hμ)
      (envelopingShift μ hμ (envelopingGenerator F n U)) = envelopingGenerator F n U
  rw [envelopingShift_generator, map_add, envelopingShift_generator, AlgHom.commutes,
    LinearMap.neg_apply, map_neg, add_assoc, neg_add_cancel, add_zero]

omit [NumberField F] in
/-- The shift by `μ` is a left inverse of the shift by `-μ`. -/
theorem envelopingShift_comp_neg (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0) :
    (envelopingShift μ hμ).comp (envelopingShift (-μ) (neg_lie_eq_zero μ hμ)) =
      AlgHom.id ℂ (EnvelopingAlgebra F n) := by
  apply UniversalEnvelopingAlgebra.hom_ext
  apply LieHom.ext
  intro U
  change envelopingShift μ hμ
      (envelopingShift (-μ) (neg_lie_eq_zero μ hμ) (envelopingGenerator F n U)) =
    envelopingGenerator F n U
  rw [envelopingShift_generator, map_add, envelopingShift_generator, AlgHom.commutes,
    LinearMap.neg_apply, map_neg, add_assoc, add_neg_cancel, add_zero]

omit [NumberField F] in
/-- The shift maps central elements to central elements. -/
theorem envelopingShift_mem_center (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0)
    (z : EnvelopingCenter F n) :
    envelopingShift μ hμ z.val ∈ Subalgebra.center ℂ (EnvelopingAlgebra F n) := by
  rw [Subalgebra.mem_center_iff]
  intro a
  have ha : envelopingShift μ hμ (envelopingShift (-μ) (neg_lie_eq_zero μ hμ) a) = a :=
    AlgHom.congr_fun (envelopingShift_comp_neg μ hμ) a
  rw [← ha, ← map_mul, ← map_mul, Subalgebra.mem_center_iff.mp z.property]

/-- The shift restricted to the center. -/
def centerShift (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0)
    (z : EnvelopingCenter F n) :
    EnvelopingCenter F n :=
  ⟨envelopingShift μ hμ z.val, envelopingShift_mem_center μ hμ z⟩

@[simp]
theorem centerInclusion_centerShift (hμ : ∀ U V : ComplexLieAlgebra F n, μ ⁅U, V⁆ = 0)
    (z : EnvelopingCenter F n) :
    centerInclusion F n (centerShift μ hμ z) = envelopingShift μ hμ (centerInclusion F n z) :=
  rfl

end Shift

section Character

variable (c : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F) →* ℂˣ)
  (hc : (fun g => (c g : ℂ)) ∈ smoothFunctions F n)

/-- The values of the character, as a smooth function. -/
def characterFunction : SmoothFunctions F n := ⟨fun g => (c g : ℂ), hc⟩

@[simp]
theorem characterFunction_apply
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (characterFunction c hc).val g = c g := rfl

/-- Multiplication by a smooth character, as a complex-linear operator. -/
def characterMultiplier : Module.End ℂ (SmoothFunctions F n) where
  toFun f := ⟨fun g => (c g : ℂ) * f.val g,
    mul_mem_smoothFunctions (characterFunction c hc) f⟩
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact mul_add _ _ _
  map_smul' z f := by
    apply Subtype.ext
    funext x
    exact mul_left_comm _ _ _

@[simp]
theorem characterMultiplier_apply (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (characterMultiplier c hc f).val g = c g * f.val g := rfl

/-- The Leibniz rule for multiplication by the character. -/
theorem smoothDifferential_characterMultiplier_apply (X : RealLieAlgebra F n)
    (f : SmoothFunctions F n)
    (g : Matrix.GeneralLinearGroup (Fin n) (NumberField.InfiniteAdeleRing F)) :
    (smoothDifferential F n X (characterMultiplier c hc f)).val g =
      (c g : ℂ) * (smoothDifferential F n X f).val g +
        (smoothDifferential F n X (characterFunction c hc)).val g * f.val g := by
  have hcd := (coordinateExtension_contDiffAt F n (characterFunction c hc)
    (archimedeanGLCoordinates F n g)).differentiableAt (by simp)
  have hfd := (coordinateExtension_contDiffAt F n f
    (archimedeanGLCoordinates F n g)).differentiableAt (by simp)
  have he : coordinateExtension F n (characterMultiplier c hc f) =
      fun a => coordinateExtension F n (characterFunction c hc) a *
        coordinateExtension F n f a := rfl
  rw [smoothDifferential_apply, smoothDifferential_apply, smoothDifferential_apply, he,
    fderiv_fun_mul hcd hfd]
  simp only [_root_.add_apply, _root_.smul_apply, smul_eq_mul,
    coordinateExtension_apply, ContinuousMulEquiv.symm_apply_apply, characterFunction_apply]
  ring

/-- The derivative of the character at the identity, as a real-linear form. -/
def characterDifferential : RealLieAlgebra F n →ₗ[ℝ] ℂ where
  toFun X := (smoothDifferential F n X (characterFunction c hc)).val 1
  map_add' X Y := by
    change (realSmoothDifferential F n (X + Y) (characterFunction c hc)).val 1 = _
    rw [map_add]
    rfl
  map_smul' r X := by
    change (realSmoothDifferential F n (r • X) (characterFunction c hc)).val 1 = _
    rw [map_smul]
    rfl

/-- The directional derivative of the character is the character times its derivative at
the identity. -/
theorem smoothDifferential_characterFunction (X : RealLieAlgebra F n) :
    smoothDifferential F n X (characterFunction c hc) =
      characterDifferential c hc X • characterFunction c hc := by
  apply Subtype.ext
  funext g
  let G : ArchimedeanMatrix F n := (archimedeanGLCoordinates F n g : ArchimedeanMatrix F n)
  let L : ArchimedeanMatrix F n →L[ℝ] ArchimedeanMatrix F n :=
    ContinuousLinearMap.mul ℝ (ArchimedeanMatrix F n) G
  let E := coordinateExtension F n (characterFunction c hc)
  have hE1 : DifferentiableAt ℝ E 1 := by
    have h := (coordinateExtension_contDiffAt F n (characterFunction c hc) 1).differentiableAt
      (by simp)
    simpa only [Units.val_one] using h
  have hEG : DifferentiableAt ℝ E (L 1) := by
    have h := (coordinateExtension_contDiffAt F n (characterFunction c hc)
      (archimedeanGLCoordinates F n g)).differentiableAt (by simp)
    simpa only [L, ContinuousLinearMap.mul_apply', mul_one] using h
  have hcomp : HasFDerivAt (E ∘ L) ((fderiv ℝ E (L 1)).comp L) 1 :=
    hEG.hasFDerivAt.comp 1 L.hasFDerivAt
  have heq : E ∘ L =ᶠ[𝓝 1] fun a => (c g : ℂ) * E a := by
    filter_upwards [Units.isOpenEmbedding_val.isOpen_range.mem_nhds
      (show (1 : ArchimedeanMatrix F n) ∈
        Set.range (Units.val : ArchimedeanGL F n → ArchimedeanMatrix F n) from
        ⟨1, rfl⟩)] with a ha
    obtain ⟨h, rfl⟩ := ha
    have hm : L (h : ArchimedeanMatrix F n) =
        ((archimedeanGLCoordinates F n g * h : ArchimedeanGL F n) : ArchimedeanMatrix F n) :=
      rfl
    rw [Function.comp_apply, hm]
    change coordinateExtension F n (characterFunction c hc)
        ((archimedeanGLCoordinates F n g * h : ArchimedeanGL F n) : ArchimedeanMatrix F n) =
      (c g : ℂ) * coordinateExtension F n (characterFunction c hc) (h : ArchimedeanMatrix F n)
    rw [coordinateExtension_apply, coordinateExtension_apply, characterFunction_apply,
      characterFunction_apply, map_mul, map_mul, ContinuousMulEquiv.symm_apply_apply,
      Units.val_mul]
  have hfd : fderiv ℝ (E ∘ L) 1 = (c g : ℂ) • fderiv ℝ E 1 := by
    rw [heq.fderiv_eq, fderiv_const_mul hE1]
  have hX := congrArg (fun T : ArchimedeanMatrix F n →L[ℝ] ℂ =>
    T (realLieAlgebraToMatrix F n X)) (hcomp.fderiv.symm.trans hfd)
  simp only [ContinuousLinearMap.comp_apply, _root_.smul_apply, smul_eq_mul] at hX
  change fderiv ℝ E G (G * realLieAlgebraToMatrix F n X) =
    characterDifferential c hc X * (c g : ℂ)
  have hL1 : L 1 = G := by simp [L]
  have hLX : L (realLieAlgebraToMatrix F n X) = G * realLieAlgebraToMatrix F n X := rfl
  rw [hL1, hLX] at hX
  rw [hX, mul_comm]
  congr 1
  change _ = fderiv ℝ E
    ((archimedeanGLCoordinates F n 1 : ArchimedeanGL F n) : ArchimedeanMatrix F n)
    (((archimedeanGLCoordinates F n 1 : ArchimedeanGL F n) : ArchimedeanMatrix F n) *
      realLieAlgebraToMatrix F n X)
  rw [map_one, Units.val_one, one_mul]

/-- The derivative of a character vanishes on brackets. -/
theorem characterDifferential_lie (X Y : RealLieAlgebra F n) :
    characterDifferential c hc ⁅X, Y⁆ = 0 := by
  have h := LinearMap.congr_fun (smoothDifferential_commutator F n X Y)
    (characterFunction c hc)
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, smoothDifferential_characterFunction,
    map_smul, smul_smul, mul_comm (characterDifferential c hc X), sub_self] at h
  have h1 := congrArg (fun f : SmoothFunctions F n => f.val 1) h
  simp only [SetLike.val_smul, Pi.smul_apply, characterFunction_apply, map_one, Units.val_one,
    smul_eq_mul, mul_one, ZeroMemClass.coe_zero, Pi.zero_apply] at h1
  exact h1

/-- The complex-linear extension of the derivative of the character. -/
def complexCharacterDifferential : ComplexLieAlgebra F n →ₗ[ℂ] ℂ :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (characterDifferential c hc))

@[simp]
theorem complexCharacterDifferential_tmul (z : ℂ) (X : RealLieAlgebra F n) :
    complexCharacterDifferential c hc (z ⊗ₜ[ℝ] X) = z * characterDifferential c hc X :=
  rfl

theorem complexCharacterDifferential_lie (U V : ComplexLieAlgebra F n) :
    complexCharacterDifferential c hc ⁅U, V⁆ = 0 := by
  induction U using TensorProduct.inductionOn with
  | tmul z X =>
    induction V using TensorProduct.inductionOn with
    | tmul w Y =>
      rw [complexLieAlgebra_lie_tmul, complexCharacterDifferential_tmul,
        characterDifferential_lie, mul_zero]
    | add V W hV hW =>
      rw [LieRing.lie_add, map_add, hV, hW, add_zero]
  | add U W hU hW =>
    rw [add_lie, map_add, hU, hW, add_zero]

/-- The enveloping algebra automorphism attached to the character. -/
def characterShift : EnvelopingAlgebra F n →ₐ[ℂ] EnvelopingAlgebra F n :=
  envelopingShift (complexCharacterDifferential c hc) (complexCharacterDifferential_lie c hc)

/-- The center automorphism attached to the character. -/
def characterCenterShift (z : EnvelopingCenter F n) : EnvelopingCenter F n :=
  centerShift (complexCharacterDifferential c hc) (complexCharacterDifferential_lie c hc) z

theorem smoothDifferential_characterMultiplier (X : RealLieAlgebra F n) :
    smoothDifferential F n X * characterMultiplier c hc =
      characterMultiplier c hc * (smoothDifferential F n X +
        algebraMap ℂ (Module.End ℂ (SmoothFunctions F n)) (characterDifferential c hc X)) := by
  apply LinearMap.ext
  intro f
  apply Subtype.ext
  funext g
  change (smoothDifferential F n X (characterMultiplier c hc f)).val g =
    (c g : ℂ) * ((smoothDifferential F n X f).val g + characterDifferential c hc X * f.val g)
  rw [smoothDifferential_characterMultiplier_apply, smoothDifferential_characterFunction]
  change (c g : ℂ) * _ + (characterDifferential c hc X * c g) * f.val g = _
  ring

theorem complexSmoothLieAction_characterMultiplier (U : ComplexLieAlgebra F n) :
    complexSmoothLieAction F n U * characterMultiplier c hc =
      characterMultiplier c hc * (complexSmoothLieAction F n U +
        algebraMap ℂ (Module.End ℂ (SmoothFunctions F n))
          (complexCharacterDifferential c hc U)) := by
  induction U using TensorProduct.inductionOn with
  | tmul z X =>
    rw [complexSmoothLieAction_tmul, complexCharacterDifferential_tmul, smul_mul_assoc,
      smoothDifferential_characterMultiplier, map_mul, Algebra.algebraMap_eq_smul_one z,
      smul_mul_assoc, one_mul, ← smul_add, mul_smul_comm]
  | add U V hU hV =>
    rw [map_add, map_add, map_add, add_mul, hU, hV, ← mul_add]
    congr 1
    abel

/-- Every enveloping operator, composed with multiplication by the character, equals the
multiplication composed with the shifted enveloping operator. -/
theorem envelopingAction_characterMultiplier (u : EnvelopingAlgebra F n) :
    envelopingAction F n u * characterMultiplier c hc =
      characterMultiplier c hc * envelopingAction F n (characterShift c hc u) := by
  obtain ⟨t, rfl⟩ := RingCon.mkₐ_surjective (α := ℂ)
    (UniversalEnvelopingAlgebra.ringCon ℂ (ComplexLieAlgebra F n)) u
  change envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t) *
      characterMultiplier c hc =
    characterMultiplier c hc * envelopingAction F n
      (characterShift c hc (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ t))
  induction t using TensorAlgebra.induction with
  | algebraMap z =>
    simp only [AlgHom.commutes]
    exact Algebra.commutes z (characterMultiplier c hc)
  | ι X =>
    change envelopingAction F n (envelopingGenerator F n X) * _ =
      _ * envelopingAction F n (characterShift c hc (envelopingGenerator F n X))
    rw [characterShift, envelopingShift_generator, map_add, AlgHom.commutes,
      envelopingAction_generator]
    exact complexSmoothLieAction_characterMultiplier c hc X
  | mul x y hx hy =>
    simp only [map_mul]
    calc
      _ = envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ x) *
          (envelopingAction F n (UniversalEnvelopingAlgebra.mkAlgHom ℂ _ y) *
            characterMultiplier c hc) := mul_assoc _ _ _
      _ = _ := by rw [hy, ← mul_assoc, hx, mul_assoc]
  | add x y hx hy =>
    simp only [map_add, add_mul, mul_add, hx, hy]

theorem envelopingAction_characterMultiplier_apply (u : EnvelopingAlgebra F n)
    (f : SmoothFunctions F n) :
    envelopingAction F n u (characterMultiplier c hc f) =
      characterMultiplier c hc (envelopingAction F n (characterShift c hc u) f) :=
  LinearMap.congr_fun (envelopingAction_characterMultiplier c hc u) f

theorem centerAction_characterMultiplier (z : EnvelopingCenter F n) (f : SmoothFunctions F n) :
    centerAction F n z (characterMultiplier c hc f) =
      characterMultiplier c hc (centerAction F n (characterCenterShift c hc z) f) :=
  envelopingAction_characterMultiplier_apply c hc (centerInclusion F n z) f

end Character

end Langlands.Global.ArchimedeanGL

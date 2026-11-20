import Langlands.Global.AdelicParabolicInduction
import Langlands.Global.ArchimedeanCompact
import Langlands.Global.ArchimedeanVectorDifferential

/-! # Archimedean actions on actual smooth adelic block sections -/

noncomputable section

universe uF uV

namespace Langlands.Global.AdelicParabolicInduction

open Langlands.GeneralLinear AdelicBlockParabolic ArchimedeanGL
open scoped Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

attribute [local instance 100] LieRing.ofAssociativeRing

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV} [NormedAddCommGroup V] [NormedSpace ℂ V]
variable (σ : Representation ℂ (FullLevi F B) V)

local instance : AddCommGroup (SmoothSections F B σ) := Submodule.addCommGroup _

/-- The standard infinite compact acts by adelic right translation. -/
def compactRepresentation :
    Representation ℂ (standardInfiniteCompact F n) (SmoothSections F B σ) :=
  (smoothInduced F B σ).comp
    ((AdelicGL.ofInfinite F n).toMonoidHom.comp (standardInfiniteCompact F n).subtype)

@[simp]
theorem evaluate_compactRepresentation (k : standardInfiniteCompact F n)
    (f : SmoothSections F B σ) (g : AdelicGL F n) :
    evaluate F B σ (compactRepresentation F B σ k f).val g =
      evaluate F B σ f.val (g * AdelicGL.ofInfinite F n k.val) := rfl

/-- Restrict a smooth section to its smooth archimedean slice. -/
def smoothInfiniteSlice (b : FiniteAdelicGL F n) :
    SmoothSections F B σ →ₗ[ℂ] VectorSmoothFunctions F n V where
  toFun f := ⟨infiniteSlice F B σ b f.val,
    (mem_infiniteSmoothSubrepresentation F B σ f.val).mp f.property.1 b⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem smoothInfiniteSlice_apply (b : FiniteAdelicGL F n)
    (f : SmoothSections F B σ) (a : InfiniteAdelicGL F n) :
    (smoothInfiniteSlice F B σ b f).val a = evaluate F B σ f.val (AdelicGL.pair F n a b) :=
  rfl

private theorem smoothSections_ext {f₁ f₂ : SmoothSections F B σ}
    (h : ∀ g, evaluate F B σ f₁.val g = evaluate F B σ f₂.val g) : f₁ = f₂ :=
  Subtype.ext (Subtype.ext (funext h))

private def directionalValue (X : RealLieAlgebra F n) (f : SmoothSections F B σ)
    (g : AdelicGL F n) : V :=
  (vectorSmoothDifferential F n X
    (smoothInfiniteSlice F B σ (AdelicGL.finite F n g) f)).val (AdelicGL.infinite F n g)

private theorem directionalValue_covariance
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (f : SmoothSections F B σ) (p : Full F B)
    (g : AdelicGL F n) :
    directionalValue F B σ X f (p.val * g) =
      inducingRepresentation F B σ p (directionalValue F B σ X f g) := by
  let T : V →L[ℂ] V := ⟨inducingRepresentation F B σ p, hσ p⟩
  have hT (v : V) : T v = inducingRepresentation F B σ p v := rfl
  have hs : vectorSmoothLeftTranslation F n (AdelicGL.infinite F n p.val)
        (smoothInfiniteSlice F B σ (AdelicGL.finite F n p.val * AdelicGL.finite F n g) f) =
      vectorSmoothMap F n V T (smoothInfiniteSlice F B σ (AdelicGL.finite F n g) f) := by
    apply Subtype.ext
    funext a
    simp only [vectorSmoothLeftTranslation_apply, smoothInfiniteSlice_apply,
      vectorSmoothMap_apply, ← AdelicGL.pair_mul, AdelicGL.pair_projections]
    exact f.val.property p _
  have hd := congrArg (vectorSmoothDifferential F n X) hs
  rw [vectorSmoothDifferential_leftTranslation, vectorSmoothDifferential_map] at hd
  simpa only [directionalValue, map_mul, vectorSmoothLeftTranslation_apply,
    vectorSmoothMap_apply, hT] using congrArg
      (fun s : VectorSmoothFunctions F n V => s.val (AdelicGL.infinite F n g)) hd

private theorem infiniteSlice_mul_finite (f : SmoothSections F B σ)
    (d b : FiniteAdelicGL F n) :
    smoothInfiniteSlice F B σ b (smoothInduced F B σ (AdelicGL.ofFinite F n d) f) =
      smoothInfiniteSlice F B σ (b * d) f := by
  apply Subtype.ext
  funext a
  simp only [smoothInfiniteSlice_apply, evaluate_smoothInduced, AdelicGL.ofFinite_eq_pair,
    AdelicGL.pair_mul, mul_one]

private def directionalSection (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (f : SmoothSections F B σ) : SmoothSections F B σ := by
  refine ⟨⟨directionalValue F B σ X f, directionalValue_covariance F B σ hσ X f⟩, ?_, ?_⟩
  · apply (mem_infiniteSmoothSubrepresentation F B σ _).mpr
    intro b
    simpa only [infiniteSlice, LinearMap.coe_mk, AddHom.coe_mk, evaluate, directionalValue,
      AdelicGL.finite_pair, AdelicGL.infinite_pair] using
      (vectorSmoothDifferential F n X (smoothInfiniteSlice F B σ b f)).property
  · obtain ⟨K, hK⟩ := f.property.2
    refine ⟨K, ?_⟩
    intro k
    have hf : smoothInduced F B σ (AdelicGL.ofFinite F n k.val) f = f :=
      Subtype.ext (hK k)
    apply Subtype.ext
    funext g
    change directionalValue F B σ X f (g * AdelicGL.ofFinite F n k.val) =
      directionalValue F B σ X f g
    dsimp only [directionalValue]
    simp only [map_mul, AdelicGL.ofFinite_eq_pair, AdelicGL.infinite_pair,
      AdelicGL.finite_pair, mul_one]
    rw [← infiniteSlice_mul_finite, hf]

private theorem infiniteSlice_directionalSection
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (f : SmoothSections F B σ) (b : FiniteAdelicGL F n) :
    smoothInfiniteSlice F B σ b (directionalSection F B σ hσ X f) =
      vectorSmoothDifferential F n X (smoothInfiniteSlice F B σ b f) := by
  apply Subtype.ext
  funext a
  simp only [smoothInfiniteSlice_apply, evaluate, directionalSection, directionalValue,
    AdelicGL.finite_pair, AdelicGL.infinite_pair]

/-- Right differentiation, keeping the same covariance and finite smoothness. -/
def sectionDifferential (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) : Module.End ℂ (SmoothSections F B σ) where
  toFun := directionalSection F B σ hσ X
  map_add' f₁ f₂ := by
    apply smoothSections_ext F B σ
    intro g
    change directionalValue F B σ X (f₁ + f₂) g =
      directionalValue F B σ X f₁ g + directionalValue F B σ X f₂ g
    simp only [directionalValue, map_add, Submodule.coe_add, Pi.add_apply]
  map_smul' c f := by
    apply smoothSections_ext F B σ
    intro g
    change directionalValue F B σ X (c • f) g = c • directionalValue F B σ X f g
    simp only [directionalValue, map_smul, Submodule.coe_smul, Pi.smul_apply]

@[simp]
theorem smoothInfiniteSlice_sectionDifferential
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (f : SmoothSections F B σ) (b : FiniteAdelicGL F n) :
    smoothInfiniteSlice F B σ b (sectionDifferential F B σ hσ X f) =
      vectorSmoothDifferential F n X (smoothInfiniteSlice F B σ b f) :=
  infiniteSlice_directionalSection F B σ hσ X f b

theorem evaluate_sectionDifferential
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (f : SmoothSections F B σ) (g : AdelicGL F n) :
    evaluate F B σ (sectionDifferential F B σ hσ X f).val g =
      (vectorSmoothDifferential F n X
        (smoothInfiniteSlice F B σ (AdelicGL.finite F n g) f)).val
        (AdelicGL.infinite F n g) := rfl

private theorem smoothSections_ext_of_slices {f₁ f₂ : SmoothSections F B σ}
    (h : ∀ b, smoothInfiniteSlice F B σ b f₁ = smoothInfiniteSlice F B σ b f₂) :
    f₁ = f₂ := by
  apply smoothSections_ext F B σ
  intro g
  simpa only [smoothInfiniteSlice_apply, AdelicGL.pair_projections] using
    congrArg (fun s : VectorSmoothFunctions F n V => s.val (AdelicGL.infinite F n g))
      (h (AdelicGL.finite F n g))

/-- The real archimedean matrix Lie algebra acts on the actual smooth section space. -/
def realLieAction (hσ : ∀ p, Continuous (inducingRepresentation F B σ p)) :
    RealLieAlgebra F n →ₗ⁅ℝ⁆ Module.End ℂ (SmoothSections F B σ) where
  toFun := sectionDifferential F B σ hσ
  map_add' X Y := by
    apply LinearMap.ext
    intro f
    apply smoothSections_ext_of_slices F B σ
    intro b
    simp only [LinearMap.add_apply, map_add, smoothInfiniteSlice_sectionDifferential,
      ← realVectorSmoothLieAction_apply]
  map_smul' c X := by
    apply LinearMap.ext
    intro f
    apply smoothSections_ext_of_slices F B σ
    intro b
    simp only [LinearMap.smul_apply, RingHom.id_apply, LinearMap.map_smul_of_tower,
      smoothInfiniteSlice_sectionDifferential, ← realVectorSmoothLieAction_apply, map_smul]
  map_lie' := by
    intro X Y
    apply LinearMap.ext
    intro f
    apply smoothSections_ext_of_slices F B σ
    intro b
    change smoothInfiniteSlice F B σ b (sectionDifferential F B σ hσ ⁅X, Y⁆ f) =
      smoothInfiniteSlice F B σ b
        (sectionDifferential F B σ hσ X (sectionDifferential F B σ hσ Y f) -
          sectionDifferential F B σ hσ Y (sectionDifferential F B σ hσ X f))
    simp only [map_sub, smoothInfiniteSlice_sectionDifferential, ← realVectorSmoothLieAction_apply]
    exact DFunLike.congr_fun ((realVectorSmoothLieAction F n (V := V)).map_lie X Y) _

@[simp]
theorem realLieAction_apply (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) :
    realLieAction F B σ hσ X = sectionDifferential F B σ hσ X := rfl

/-- Evaluation of the real action is the derivative of actual adelic right translation. -/
theorem evaluate_realLieAction_hasDerivAt
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (c : ℝ → InfiniteAdelicGL F n)
    (hc0 : c 0 = 1)
    (hc : HasDerivAt (fun t => (archimedeanGLCoordinates F n (c t) : ArchimedeanMatrix F n))
      (realLieAlgebraToMatrix F n X) 0)
    (f : SmoothSections F B σ) (g : AdelicGL F n) :
    HasDerivAt (fun t => evaluate F B σ f.val (g * AdelicGL.ofInfinite F n (c t)))
      (evaluate F B σ (realLieAction F B σ hσ X f).val g) 0 := by
  have h := vectorSmoothDifferential_hasDerivAt F n X c hc0 hc
    (smoothInfiniteSlice F B σ (AdelicGL.finite F n g) f) (AdelicGL.infinite F n g)
  have he : ∀ t, AdelicGL.pair F n (AdelicGL.infinite F n g * c t) (AdelicGL.finite F n g) =
      g * AdelicGL.ofInfinite F n (c t) := by
    intro t
    rw [AdelicGL.ofInfinite_eq_pair, ← AdelicGL.pair_projections F n g, AdelicGL.pair_mul]
    simp only [AdelicGL.infinite_pair, AdelicGL.finite_pair, mul_one]
  simpa only [smoothInfiniteSlice_apply, he, realLieAction_apply, evaluate_sectionDifferential]
    using h

/-- Differentiation commutes with right translation in the finite factor. -/
theorem sectionDifferential_finite
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (X : RealLieAlgebra F n) (d : FiniteAdelicGL F n) (f : SmoothSections F B σ) :
    sectionDifferential F B σ hσ X (smoothInduced F B σ (AdelicGL.ofFinite F n d) f) =
      smoothInduced F B σ (AdelicGL.ofFinite F n d) (sectionDifferential F B σ hσ X f) := by
  apply smoothSections_ext_of_slices F B σ
  intro b
  simp only [smoothInfiniteSlice_sectionDifferential, infiniteSlice_mul_finite]

private def complexDifferential (hσ : ∀ p, Continuous (inducingRepresentation F B σ p)) :
    ComplexLieAlgebra F n →ₗ[ℂ] Module.End ℂ (SmoothSections F B σ) :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realLieAction F B σ hσ).toLinearMap)

private theorem complexDifferential_tmul
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (z : ℂ) (X : RealLieAlgebra F n) :
    complexDifferential F B σ hσ (z ⊗ₜ[ℝ] X) = z • realLieAction F B σ hσ X := rfl

/-- Complex-linear extension of the real section action, preserving the Lie bracket. -/
def complexLieAction (hσ : ∀ p, Continuous (inducingRepresentation F B σ p)) :
    ComplexLieAlgebra F n →ₗ⁅ℂ⁆ Module.End ℂ (SmoothSections F B σ) where
  __ := complexDifferential F B σ hσ
  map_lie' := by
    intro U W
    change complexDifferential F B σ hσ ⁅U, W⁆ =
      ⁅complexDifferential F B σ hσ U, complexDifferential F B σ hσ W⁆
    induction U using TensorProduct.inductionOn with
    | tmul z X =>
      induction W using TensorProduct.inductionOn with
      | tmul w Y =>
        simp only [complexLieAlgebra_lie_tmul, complexDifferential_tmul,
          (realLieAction F B σ hσ).map_lie]
        let A := realLieAction F B σ hσ X
        let D := realLieAction F B σ hσ Y
        change (z * w) • (A * D - D * A) =
          (z • A) * (w • D) - (w • D) * (z • A)
        simp only [smul_sub, smul_mul_assoc, mul_smul_comm, smul_smul, mul_comm w z]
      | add U W hU hW => simp only [LieRing.lie_add, map_add, hU, hW]
    | add U W hU hW => simp only [add_lie, map_add, hU, hW]

@[simp]
theorem complexLieAction_tmul (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (z : ℂ) (X : RealLieAlgebra F n) :
    complexLieAction F B σ hσ (z ⊗ₜ[ℝ] X) = z • realLieAction F B σ hσ X := rfl

/-- The enveloping algebra acts by extending the complexified right differential. -/
def envelopingAction (hσ : ∀ p, Continuous (inducingRepresentation F B σ p)) :
    EnvelopingAlgebra F n →ₐ[ℂ] Module.End ℂ (SmoothSections F B σ) :=
  UniversalEnvelopingAlgebra.lift ℂ (complexLieAction F B σ hσ)

@[simp]
theorem envelopingAction_generator (hσ : ∀ p, Continuous (inducingRepresentation F B σ p))
    (U : ComplexLieAlgebra F n) :
    envelopingAction F B σ hσ (envelopingGenerator F n U) = complexLieAction F B σ hσ U :=
  UniversalEnvelopingAlgebra.lift_ι_apply ℂ (complexLieAction F B σ hσ) U

@[simp]
theorem envelopingAction_real_generator
    (hσ : ∀ p, Continuous (inducingRepresentation F B σ p)) (X : RealLieAlgebra F n) :
    envelopingAction F B σ hσ (envelopingGenerator F n (complexify F n X)) =
      realLieAction F B σ hσ X := by
  simp only [envelopingAction_generator, complexify_apply, complexLieAction_tmul, one_smul]

end Langlands.Global.AdelicParabolicInduction

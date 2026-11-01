import Langlands.Global.AdelicParabolicInduction
import Langlands.Global.AdelicBlockHeckeCharacter
import Langlands.Automorphic.SmoothDeterminantMultiplier

/-!
# Actual determinant twists of half-twisted adelic sections

The actual multiplier is `f(x) ↦ χ(det x) • f(x)`. Finite stabilizers and
archimedean slice smoothness are retained as separate conditions.
-/

noncomputable section

set_option backward.isDefEq.respectTransparency false

universe uF uV

namespace Langlands.Global.AdelicParabolicInduction

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic
open scoped Classical Manifold ContDiff Matrix.Norms.Operator

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)
variable {V : Type uV}

section Algebraic

variable [AddCommGroup V] [Module ℂ V]

local instance finiteSmoothSectionGroup (σ : Representation ℂ (FullLevi F B) V) :
    AddCommGroup (FiniteSmoothSections F B σ) := Submodule.addCommGroup _

/-- Twist the actual Levi coefficients by the common block determinant character. -/
def determinantTwist (χ : HeckeCharacter F) (σ : Representation ℂ (FullLevi F B) V) :
    Representation ℂ (FullLevi F B) V :=
  twist (AdelicBlockHeckeCharacter.leviCharacter F B (fun _ => χ)).toMonoidHom σ

/-- On the actual parabolic the block character is the ambient determinant character. -/
theorem inducingRepresentation_determinantTwist (χ : HeckeCharacter F)
    (σ : Representation ℂ (FullLevi F B) V) (p : Full F B) (v : V) :
    inducingRepresentation F B (determinantTwist F B χ σ) p v =
      (χ.adelicDeterminant n p.val : ℂ) • inducingRepresentation F B σ p v := by
  have h := AdelicBlockHeckeCharacter.parabolicCharacter_constant F B χ p
  change AdelicBlockHeckeCharacter.leviCharacter F B (fun _ => χ)
    (B.leviProjection (Adeles F) p) = χ.adelicDeterminant n p.val at h
  change (AdelicBlockDeterminantCharacter.leviHalfCharacter F B
      (B.leviProjection (Adeles F) p) : ℂ) •
      ((AdelicBlockHeckeCharacter.leviCharacter F B (fun _ => χ)
        (B.leviProjection (Adeles F) p) : ℂ) •
        σ (B.leviProjection (Adeles F) p) v) = _
  rw [h]
  exact smul_comm _ _ _

/-- Actual multiplication on covariant functions, with explicit inverse multiplication. -/
def sectionDeterminantEquiv (χ : HeckeCharacter F)
    (σ : Representation ℂ (FullLevi F B) V) :
    Sections F B σ ≃ₗ[ℂ] Sections F B (determinantTwist F B χ σ) where
  toFun f := ⟨fun x => (χ.adelicDeterminant n x : ℂ) • f.val x, by
    intro p x
    have hf : f.val (p.val * x) =
        inducingRepresentation F B σ p (f.val x) := f.property p x
    change (χ.adelicDeterminant n (p.val * x) : ℂ) • f.val (p.val * x) =
      inducingRepresentation F B (determinantTwist F B χ σ) p
        ((χ.adelicDeterminant n x : ℂ) • f.val x)
    rw [map_mul, Units.val_mul, hf, inducingRepresentation_determinantTwist,
      map_smul, mul_smul]⟩
  invFun f := ⟨fun x => ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) • f.val x, by
    intro p x
    have hf : f.val (p.val * x) =
        inducingRepresentation F B (determinantTwist F B χ σ) p (f.val x) :=
      f.property p x
    rw [inducingRepresentation_determinantTwist] at hf
    change ((χ.adelicDeterminant n (p.val * x))⁻¹ : ℂˣ) • f.val (p.val * x) =
      inducingRepresentation F B σ p (((χ.adelicDeterminant n x)⁻¹ : ℂˣ) • f.val x)
    simp only [Units.smul_def] at *
    rw [hf, map_mul, mul_inv_rev, Units.val_mul, map_smul, smul_smul]
    simp⟩
  left_inv f := by
    apply Subtype.ext
    funext x
    change ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
      ((χ.adelicDeterminant n x : ℂ) • f.val x) = f.val x
    simp [Units.smul_def, smul_smul]
  right_inv f := by
    apply Subtype.ext
    funext x
    change (χ.adelicDeterminant n x : ℂ) •
      (((χ.adelicDeterminant n x)⁻¹ : ℂˣ) • f.val x) = f.val x
    simp [Units.smul_def, smul_smul]
  map_add' f h := by
    apply Subtype.ext
    funext x
    exact smul_add _ _ _
  map_smul' c f := by
    apply Subtype.ext
    funext x
    exact smul_comm _ _ _

@[simp]
theorem evaluate_sectionDeterminantEquiv (χ : HeckeCharacter F)
    (σ : Representation ℂ (FullLevi F B) V) (f : Sections F B σ) (x : AdelicGL F n) :
    evaluate F B (determinantTwist F B χ σ) (sectionDeterminantEquiv F B χ σ f) x =
      (χ.adelicDeterminant n x : ℂ) • evaluate F B σ f x := rfl

@[simp]
theorem evaluate_sectionDeterminantEquiv_symm (χ : HeckeCharacter F)
    (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B (determinantTwist F B χ σ)) (x : AdelicGL F n) :
    evaluate F B σ ((sectionDeterminantEquiv F B χ σ).symm f) x =
      ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
        evaluate F B (determinantTwist F B χ σ) f x := rfl

/-- Actual determinant multiplication compares the ambient twist and the Levi twist. -/
def sectionDeterminantTwistEquiv (χ : HeckeCharacter F)
    (σ : Representation ℂ (FullLevi F B) V) :
    (twist (χ.adelicDeterminant n).toMonoidHom (rightAction F B σ)).Equiv
      (rightAction F B (determinantTwist F B χ σ)) where
  toLinearEquiv := sectionDeterminantEquiv F B χ σ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    funext x
    change (χ.adelicDeterminant n x : ℂ) •
      ((χ.adelicDeterminant n g : ℂ) • f.val (x * g)) =
        (χ.adelicDeterminant n (x * g) : ℂ) • f.val (x * g)
    rw [map_mul, Units.val_mul, mul_smul]

/-- Multiplication shrinks a common finite stabilizer by the actual determinant kernel. -/
theorem finiteSmooth_of_determinant_multiply (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ τ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (s : Sections F B τ)
    (hs : ∀ x, evaluate F B τ s x =
      (χ.adelicDeterminant n x : ℂ) • evaluate F B σ f x)
    (hf : f ∈ finiteSmoothSubrepresentation F B σ) :
    s ∈ finiteSmoothSubrepresentation F B τ := by
  obtain ⟨K, hK⟩ := hf
  refine ⟨K ⊓ χ.finiteDeterminantKernel n hχ, ?_⟩
  intro k
  have hk : χ.adelicDeterminant n (AdelicGL.ofFinite F n k.val) = 1 := k.property.2
  have hfix := congrArg (fun t => evaluate F B σ t)
    (hK ⟨k.val, k.property.1⟩)
  apply Subtype.ext
  funext x
  change evaluate F B τ s (x * AdelicGL.ofFinite F n k.val) = evaluate F B τ s x
  rw [hs, hs, map_mul, hk, mul_one]
  exact congrArg (fun v : V => (χ.adelicDeterminant n x : ℂ) • v)
    (congrFun hfix x)

theorem sectionDeterminant_finiteSmooth (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (hf : f ∈ finiteSmoothSubrepresentation F B σ) :
    sectionDeterminantEquiv F B χ σ f ∈
      finiteSmoothSubrepresentation F B (determinantTwist F B χ σ) :=
  finiteSmooth_of_determinant_multiply F B χ hχ _ _ f _ (fun _ => rfl) hf

theorem sectionDeterminant_symm_finiteSmooth (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B (determinantTwist F B χ σ))
    (hf : f ∈ finiteSmoothSubrepresentation F B (determinantTwist F B χ σ)) :
    (sectionDeterminantEquiv F B χ σ).symm f ∈
      finiteSmoothSubrepresentation F B σ :=
  finiteSmooth_of_determinant_multiply F B χ⁻¹ hχ.inv _ _ f _ (fun _ => rfl) hf

/-- Actual determinant multiplication on the spaces with finite regularity. -/
def finiteSmoothDeterminantEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    FiniteSmoothSections F B σ ≃ₗ[ℂ]
      FiniteSmoothSections F B (determinantTwist F B χ σ) where
  toFun f := ⟨sectionDeterminantEquiv F B χ σ f.val,
    sectionDeterminant_finiteSmooth F B χ hχ σ f.val f.property⟩
  invFun f := ⟨(sectionDeterminantEquiv F B χ σ).symm f.val,
    sectionDeterminant_symm_finiteSmooth F B χ hχ σ f.val f.property⟩
  left_inv f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).apply_symm_apply f.val)
  map_add' f h := Subtype.ext ((sectionDeterminantEquiv F B χ σ).map_add f.val h.val)
  map_smul' c f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).map_smul c f.val)

@[simp]
theorem evaluate_finiteSmoothDeterminantEquiv (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : FiniteSmoothSections F B σ) (x : AdelicGL F n) :
    evaluate F B (determinantTwist F B χ σ)
      (finiteSmoothDeterminantEquiv F B χ hχ σ f).val x =
        (χ.adelicDeterminant n x : ℂ) • evaluate F B σ f.val x := rfl

@[simp]
theorem evaluate_finiteSmoothDeterminantEquiv_symm (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : FiniteSmoothSections F B (determinantTwist F B χ σ)) (x : AdelicGL F n) :
    evaluate F B σ ((finiteSmoothDeterminantEquiv F B χ hχ σ).symm f).val x =
      ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
        evaluate F B (determinantTwist F B χ σ) f.val x := rfl

/-- Ambient and Levi twists agree on the actual finite-smooth sections. -/
def finiteSmoothDeterminantTwistEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    (twist (χ.adelicDeterminant n).toMonoidHom (finiteSmoothInduced F B σ)).Equiv
      (finiteSmoothInduced F B (determinantTwist F B χ σ)) where
  toLinearEquiv := finiteSmoothDeterminantEquiv F B χ hχ σ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact DFunLike.congr_fun ((sectionDeterminantTwistEquiv F B χ σ).isIntertwining' g) f.val

end Algebraic

section Normed

variable [NormedAddCommGroup V] [NormedSpace ℂ V]

local instance smoothSectionGroup (σ : Representation ℂ (FullLevi F B) V) :
    AddCommGroup (SmoothSections F B σ) := Submodule.addCommGroup _

/-- Local constancy of the actual scalar multiplier preserves real-smooth vector slices. -/
theorem infiniteSmooth_of_determinant_multiply (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ τ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (s : Sections F B τ)
    (hs : ∀ x, evaluate F B τ s x =
      (χ.adelicDeterminant n x : ℂ) • evaluate F B σ f x)
    (hf : f ∈ infiniteSmoothSubrepresentation F B σ) :
    s ∈ infiniteSmoothSubrepresentation F B τ := by
  let : CompleteSpace (ArchimedeanMatrix F n) :=
    inferInstanceAs (CompleteSpace
      (Fin n → Fin n → NumberField.mixedEmbedding.mixedSpace F))
  rw [mem_infiniteSmoothSubrepresentation] at hf ⊢
  intro b
  have hc : IsLocallyConstant (fun x : ArchimedeanGL F n =>
      (χ.adelicDeterminant n
        (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) b) : ℂ)) :=
    (hχ.isLocallyConstant_determinant n).comp_continuous
      ((AdelicGL.continuous_pair F n).comp
        ((archimedeanGLCoordinates F n).symm.continuous.prodMk continuous_const))
  intro x
  let c : ℂ := χ.adelicDeterminant n
    (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm x) b)
  have hsm := (ArchimedeanGL.vectorSmoothFunctions F n V).smul_mem c (hf b)
  refine ContMDiffAt.congr_of_eventuallyEq (hsm x) ?_
  filter_upwards [hc.eventually_eq x] with y hy
  change evaluate F B τ s
      (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm y) b) =
    c • evaluate F B σ f
      (AdelicGL.pair F n ((archimedeanGLCoordinates F n).symm y) b)
  rw [hs, hy]

theorem sectionDeterminant_infiniteSmooth (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B σ) (hf : f ∈ infiniteSmoothSubrepresentation F B σ) :
    sectionDeterminantEquiv F B χ σ f ∈
      infiniteSmoothSubrepresentation F B (determinantTwist F B χ σ) :=
  infiniteSmooth_of_determinant_multiply F B χ hχ _ _ f _ (fun _ => rfl) hf

theorem sectionDeterminant_symm_infiniteSmooth (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : Sections F B (determinantTwist F B χ σ))
    (hf : f ∈ infiniteSmoothSubrepresentation F B (determinantTwist F B χ σ)) :
    (sectionDeterminantEquiv F B χ σ).symm f ∈
      infiniteSmoothSubrepresentation F B σ :=
  infiniteSmooth_of_determinant_multiply F B χ⁻¹ hχ.inv _ _ f _ (fun _ => rfl) hf

/-- Actual determinant multiplication with both regularity conditions retained. -/
def smoothDeterminantEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    SmoothSections F B σ ≃ₗ[ℂ] SmoothSections F B (determinantTwist F B χ σ) where
  toFun f := ⟨sectionDeterminantEquiv F B χ σ f.val,
    sectionDeterminant_infiniteSmooth F B χ hχ σ f.val f.property.1,
    sectionDeterminant_finiteSmooth F B χ hχ σ f.val f.property.2⟩
  invFun f := ⟨(sectionDeterminantEquiv F B χ σ).symm f.val,
    sectionDeterminant_symm_infiniteSmooth F B χ hχ σ f.val f.property.1,
    sectionDeterminant_symm_finiteSmooth F B χ hχ σ f.val f.property.2⟩
  left_inv f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).apply_symm_apply f.val)
  map_add' f h := Subtype.ext ((sectionDeterminantEquiv F B χ σ).map_add f.val h.val)
  map_smul' c f := Subtype.ext ((sectionDeterminantEquiv F B χ σ).map_smul c f.val)

@[simp]
theorem evaluate_smoothDeterminantEquiv (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : SmoothSections F B σ) (x : AdelicGL F n) :
    evaluate F B (determinantTwist F B χ σ)
      (smoothDeterminantEquiv F B χ hχ σ f).val x =
        (χ.adelicDeterminant n x : ℂ) • evaluate F B σ f.val x := rfl

@[simp]
theorem evaluate_smoothDeterminantEquiv_symm (χ : HeckeCharacter F)
    (hχ : χ.HasFiniteOrder) (σ : Representation ℂ (FullLevi F B) V)
    (f : SmoothSections F B (determinantTwist F B χ σ)) (x : AdelicGL F n) :
    evaluate F B σ ((smoothDeterminantEquiv F B χ hχ σ).symm f).val x =
      ((χ.adelicDeterminant n x)⁻¹ : ℂˣ) •
        evaluate F B (determinantTwist F B χ σ) f.val x := rfl

/-- The ambient determinant twist agrees with the actual smooth Levi-coefficient twist. -/
def smoothDeterminantTwistEquiv (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (σ : Representation ℂ (FullLevi F B) V) :
    (twist (χ.adelicDeterminant n).toMonoidHom (smoothInduced F B σ)).Equiv
      (smoothInduced F B (determinantTwist F B χ σ)) where
  toLinearEquiv := smoothDeterminantEquiv F B χ hχ σ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact DFunLike.congr_fun ((sectionDeterminantTwistEquiv F B χ σ).isIntertwining' g) f.val

end Normed

end Langlands.Global.AdelicParabolicInduction

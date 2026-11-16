import Langlands.Representation.Archimedean.RealStandardModuleGKModule
import Langlands.Representation.Archimedean.RealLargeLanglandsQuotientReduction
import Langlands.Representation.Archimedean.Kostant.RealTransfer

/-!
# Right derivatives on smooth functions on `GL_n(ℝ)`, translations and `Ad(g)`

For a space `V` of smooth functions on `GL_n(ℝ)` that is stable under the right derivatives
`R(X)`, `lie V` is the Lie algebra action `z ⊗ X ↦ z R(X)` of `𝔤 = ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on `V`
(the construction of `kFiniteLie`, without `K`-finiteness). The inclusions of such spaces, and of
the `O(n)`-finite functions of a real standard module, intertwine the actions of `U(𝔤)`.

`adU g` is the automorphism of `U(𝔤)` induced by `X ↦ g X g⁻¹`. On the smooth functions, right
translation by `g` carries the action of `u` to the action of `adU g u`. Right derivatives commute
with left translations.
-/

noncomputable section

open scoped Manifold ContDiff TensorProduct Matrix.Norms.Operator

set_option autoImplicit false

set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.GeneralLinear Langlands.LocalFactor.Archimedean

namespace SmoothRightAction

variable {n : ℕ}

/-! ## Smooth functions -/

variable (n) in
/-- The smooth functions on `GL_n(ℝ)`. -/
def smoothFunctions : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) where
  carrier := {f | ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f}
  zero_mem' := contMDiff_const
  add_mem' hf₁ hf₂ := ContMDiff.add hf₁ hf₂
  smul_mem' c _ hf :=
    ((c • ContinuousLinearMap.id ℂ ℂ).restrictScalars ℝ).contDiff.contMDiff.comp hf

theorem mem_smoothFunctions {f : Langlands.GeneralLinear n ℝ → ℂ} :
    f ∈ smoothFunctions n ↔ ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f :=
  Iff.rfl

theorem rightDerivative_mem_smoothFunctions (X : Matrix (Fin n) (Fin n) ℝ)
    {f : Langlands.GeneralLinear n ℝ → ℂ} (hf : f ∈ smoothFunctions n) :
    rightDerivative (matrixModel ℝ n) X f ∈ smoothFunctions n :=
  contMDiff_rightDerivative hf X

/-! ## The Lie algebra action on a space of smooth functions -/

section Generic

variable (V : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ))
  (hV : ∀ f ∈ V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
  (hVX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ V, rightDerivative (matrixModel ℝ n) X f ∈ V)

/-- `R(X)` on `V`. -/
def derivative (X : Matrix (Fin n) (Fin n) ℝ) : Module.End ℂ V :=
  (rightDerivativeLinearMap V hV X).codRestrict V fun f => hVX X f f.2

@[simp]
theorem derivative_apply_coe (X : Matrix (Fin n) (Fin n) ℝ) (f : V) :
    ((derivative V hV hVX X f : V) : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X f :=
  rfl

/-- `X ↦ R(X)` is real linear. -/
def realDerivative : Matrix (Fin n) (Fin n) ℝ →ₗ[ℝ] Module.End ℂ V where
  toFun := derivative V hV hVX
  map_add' X Y := by
    ext f : 2
    simp only [derivative_apply_coe, LinearMap.add_apply, Submodule.coe_add,
      rightDerivative_add_left]
  map_smul' r X := by
    ext f : 2
    simp only [derivative_apply_coe, LinearMap.smul_apply, RingHom.id_apply,
      rightDerivative_smul_left]
    rfl

/-- The complex-linear extension `z ⊗ X ↦ z R(X)`. -/
def linear : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ[ℂ] Module.End ℂ V :=
  TensorProduct.AlgebraTensorModule.lift
    (LinearMap.toSpanSingleton ℂ _ (realDerivative V hV hVX))

theorem linear_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    linear V hV hVX (z ⊗ₜ X) = z • derivative V hV hVX X := by
  simp [linear, realDerivative]

theorem derivative_commutator (X Y : Matrix (Fin n) (Fin n) ℝ) :
    derivative V hV hVX X * derivative V hV hVX Y -
        derivative V hV hVX Y * derivative V hV hVX X =
      derivative V hV hVX (X * Y - Y * X) := by
  ext f : 2
  rw [LinearMap.sub_apply, Submodule.coe_sub, Module.End.mul_apply,
    Module.End.mul_apply, derivative_apply_coe, derivative_apply_coe,
    derivative_apply_coe, derivative_apply_coe, derivative_apply_coe]
  exact rightDerivative_commutator (hV _ f.2) X Y

/-- The Lie algebra action of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)` on `V`: `z ⊗ X ↦ z R(X)`. -/
def lie : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V :=
  { linear V hV hVX with
    map_lie' := by
      intro x y
      rw [LinearMap.toFun_eq_coe]
      induction x using TensorProduct.inductionOn with
      | add x₁ x₂ h₁ h₂ =>
        simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
        erw [add_lie x₁ x₂ y]
        rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
        abel
      | tmul z X =>
        induction y using TensorProduct.inductionOn with
        | add y₁ y₂ h₁ h₂ =>
          simp only [LieRing.of_associative_ring_bracket] at h₁ h₂ ⊢
          erw [lie_add]
          rw [map_add, h₁, h₂, map_add, add_mul, mul_add]
          abel
        | tmul w Y =>
          rw [LieAlgebra.ExtendScalars.bracket_tmul, linear_tmul, linear_tmul, linear_tmul]
          simp only [LieRing.of_associative_ring_bracket]
          rw [smul_mul_smul_comm, smul_mul_smul_comm, mul_comm w z,
            ← derivative_commutator]
          exact smul_sub (z * w)
            (derivative V hV hVX X * derivative V hV hVX Y)
            (derivative V hV hVX Y * derivative V hV hVX X) }

theorem lie_tmul (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    lie V hV hVX (z ⊗ₜ X) = z • derivative V hV hVX X :=
  linear_tmul V hV hVX z X

theorem lie_one_tmul_apply_coe (X : Matrix (Fin n) (Fin n) ℝ) (f : V) :
    ((lie V hV hVX (1 ⊗ₜ X) f : V) : Langlands.GeneralLinear n ℝ → ℂ) =
      rightDerivative (matrixModel ℝ n) X f := by
  rw [lie_tmul, one_smul, derivative_apply_coe]

/-- A linear map into `V` that intertwines the actions of the real matrices `1 ⊗ X` intertwines
the actions of `U(𝔤)`. -/
theorem envelopingAction_intertwine_of_tmul {W : Type*} [AddCommGroup W] [Module ℂ W]
    (σ : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W) (B : W →ₗ[ℂ] V)
    (h : ∀ (X : Matrix (Fin n) (Fin n) ℝ) (f : W), B (σ (1 ⊗ₜ X) f) = lie V hV hVX (1 ⊗ₜ X) (B f))
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) (f : W) :
    B (envelopingAction σ u f) = envelopingAction (lie V hV hVX) u (B f) := by
  refine envelopingAction_intertwine σ _ B (fun Y f => ?_) u f
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    have hz : z ⊗ₜ[ℝ] X = z • ((1 : ℂ) ⊗ₜ[ℝ] X) := by
      rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
    rw [hz, map_smul, map_smul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul, h]
  | add Y Z hY hZ =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hY, hZ]

end Generic

/-- The inclusion of a smaller space of smooth functions, both stable under right derivatives,
intertwines the actions of `U(𝔤)`. -/
theorem envelopingAction_inclusion_coe {V W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)}
    (hle : W ≤ V) (hV : ∀ f ∈ V, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hVX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ V, rightDerivative (matrixModel ℝ n) X f ∈ V)
    (hW : ∀ f ∈ W, ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f)
    (hWX : ∀ (X : Matrix (Fin n) (Fin n) ℝ), ∀ f ∈ W, rightDerivative (matrixModel ℝ n) X f ∈ W)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) (f : W) :
    ((envelopingAction (lie W hW hWX) u f : W) : Langlands.GeneralLinear n ℝ → ℂ) =
      (envelopingAction (lie V hV hVX) u (Submodule.inclusion hle f) :
        Langlands.GeneralLinear n ℝ → ℂ) := by
  have h := envelopingAction_intertwine_of_tmul V hV hVX (lie W hW hWX)
    (Submodule.inclusion hle) (fun X f => by
      apply Subtype.ext
      rw [Submodule.coe_inclusion, lie_one_tmul_apply_coe, lie_one_tmul_apply_coe,
        Submodule.coe_inclusion]) u f
  rw [← h, Submodule.coe_inclusion]

/-- The smooth functions are stable under right derivatives. -/
abbrev smoothLie : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ (smoothFunctions n) :=
  lie (smoothFunctions n) (fun _ hf => hf) fun X _ hf => rightDerivative_mem_smoothFunctions X hf

/-- The action of `U(𝔤)` on the `O(n)`-finite functions of a real standard module is the
restriction of its action on all smooth functions. -/
theorem realStandardLie_coe (ds : List RealBlock)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ))
    (h : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
    ((envelopingAction (realStandardLie n ds) u h :
        kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)) :
        Langlands.GeneralLinear n ℝ → ℂ) =
      (envelopingAction smoothLie u ⟨h, contMDiff_of_mem_realStandardModule h.2.1⟩ :
        Langlands.GeneralLinear n ℝ → ℂ) := by
  let B : kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n) →ₗ[ℂ]
      smoothFunctions n :=
    ((kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)).subtype).codRestrict _
      fun f => contMDiff_of_mem_realStandardModule f.2.1
  have hB := envelopingAction_intertwine_of_tmul (smoothFunctions n) (fun _ hf => hf)
    (fun X _ hf => rightDerivative_mem_smoothFunctions X hf) (realStandardLie n ds) B
    (fun X f => by
      apply Subtype.ext
      rw [lie_one_tmul_apply_coe]
      exact kFiniteLie_one_tmul_apply_coe _ _ _ _ X f) u h
  exact congrArg Subtype.val hB

/-! ## Left translations -/

/-- Right derivatives commute with left translations. -/
theorem rightDerivative_comp_mul_left {f : Langlands.GeneralLinear n ℝ → ℂ}
    (hf : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ f) (a : Langlands.GeneralLinear n ℝ)
    (X : Matrix (Fin n) (Fin n) ℝ) (g : Langlands.GeneralLinear n ℝ) :
    rightDerivative (matrixModel ℝ n) X (fun x => f (a * x)) g =
      rightDerivative (matrixModel ℝ n) X f (a * g) := by
  have hfa : ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (fun x => f (a * x)) :=
    hf.comp contMDiff_mul_left
  rw [rightDerivative_eq_fderiv_mul_left hfa, rightDerivative_eq_fderiv_mul_left hf]
  congr 2
  funext y
  by_cases h : IsUnit ((g : Matrix (Fin n) (Fin n) ℝ) * y)
  · obtain ⟨w, hw⟩ := h
    have he : ((a * g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * y =
        ((a * w : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) := by
      rw [Units.val_mul, Units.val_mul, hw, mul_assoc]
    rw [he, ← hw, unitsExtension_val, unitsExtension_val]
  · have h' : ¬ IsUnit (((a * g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * y) := by
      intro hu
      apply h
      have he : (g : Matrix (Fin n) (Fin n) ℝ) * y =
          ((a⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) *
            (((a * g : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) * y) := by
        rw [Units.val_mul, ← mul_assoc, ← mul_assoc, ← Units.val_mul, inv_mul_cancel,
          Units.val_one, one_mul]
      rw [he]
      exact (Units.isUnit _).mul hu
    rw [unitsExtension, unitsExtension, dite_eq_right h, dite_eq_right h']

/-! ## Conjugation and `Ad(g)` -/

/-- Conjugation `X ↦ g X g⁻¹` as an algebra automorphism of the real matrices. -/
def conjAlgHom (g : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ →ₐ[ℝ] Matrix (Fin n) (Fin n) ℝ where
  toFun X := (g : Matrix (Fin n) (Fin n) ℝ) * X * ((g⁻¹ : Langlands.GeneralLinear n ℝ) :
    Matrix (Fin n) (Fin n) ℝ)
  map_one' := by rw [mul_one, ← Units.val_mul, mul_inv_cancel, Units.val_one]
  map_mul' X Y := by
    have h : ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) *
        (g : Matrix (Fin n) (Fin n) ℝ) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    simp only [mul_assoc]
    rw [← mul_assoc ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), h,
      one_mul]
  map_zero' := by rw [mul_zero, zero_mul]
  map_add' X Y := by rw [mul_add, add_mul]
  commutes' r := by
    rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc,
      ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem conjAlgHom_apply (g : Langlands.GeneralLinear n ℝ) (X : Matrix (Fin n) (Fin n) ℝ) :
    conjAlgHom g X = (g : Matrix (Fin n) (Fin n) ℝ) * X *
      ((g⁻¹ : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ) :=
  rfl

/-- `z ⊗ X ↦ z ⊗ g X g⁻¹` as an algebra automorphism of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
def adAlg (g : Langlands.GeneralLinear n ℝ) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₐ[ℂ] (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  Algebra.TensorProduct.map (AlgHom.id ℂ ℂ) (conjAlgHom g)

theorem adAlg_tmul (g : Langlands.GeneralLinear n ℝ) (z : ℂ) (X : Matrix (Fin n) (Fin n) ℝ) :
    adAlg g (z ⊗ₜ X) = z ⊗ₜ conjAlgHom g X :=
  rfl

/-- `Ad(g)` as a Lie algebra endomorphism of `ℂ ⊗_ℝ 𝔤𝔩_n(ℝ)`. -/
def adLie (g : Langlands.GeneralLinear n ℝ) :
    (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  { (adAlg g).toLinearMap with
    map_lie' := by
      intro x y
      simp only [AlgHom.toLinearMap_apply, AddHom.toFun_eq_coe, LinearMap.coe_toAddHom]
      rw [Kostant.realGL_bracket_eq, Kostant.realGL_bracket_eq, map_sub, map_mul, map_mul] }

theorem adLie_apply (g : Langlands.GeneralLinear n ℝ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    adLie g x = adAlg g x :=
  rfl

/-- `Ad(g)` on the enveloping algebra. -/
def adU (g : Langlands.GeneralLinear n ℝ) :
    UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₐ[ℂ]
      UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :=
  UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp (adLie g))

theorem adU_ι (g : Langlands.GeneralLinear n ℝ) (x : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) :
    adU g (UniversalEnvelopingAlgebra.ι ℂ x) = UniversalEnvelopingAlgebra.ι ℂ (adLie g x) := by
  simp [adU]

/-- Composing a Lie algebra action with `Ad(g)` composes its enveloping action with `adU g`. -/
theorem envelopingAction_comp_adLie {W : Type*} [AddCommGroup W] [Module ℂ W]
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ W)
    (g : Langlands.GeneralLinear n ℝ)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) :
    envelopingAction (π.comp (adLie g)) u = envelopingAction π (adU g u) := by
  have h : envelopingAction (π.comp (adLie g)) = (envelopingAction π).comp (adU g) := by
    apply UniversalEnvelopingAlgebra.hom_ext
    ext x
    simp [adU]
  rw [h, AlgHom.comp_apply]

/-! ## Right translations -/

/-- Right translation by `g` on the smooth functions. -/
def rightTranslate (g : Langlands.GeneralLinear n ℝ) :
    smoothFunctions n →ₗ[ℂ] smoothFunctions n :=
  ((Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ) g).comp
    (smoothFunctions n).subtype).codRestrict _ fun f =>
      (show ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞ (f : Langlands.GeneralLinear n ℝ → ℂ) from
        f.2).comp contMDiff_mul_right

theorem rightTranslate_apply (g x : Langlands.GeneralLinear n ℝ) (f : smoothFunctions n) :
    (rightTranslate g f : Langlands.GeneralLinear n ℝ → ℂ) x =
      (f : Langlands.GeneralLinear n ℝ → ℂ) (x * g) :=
  rfl

/-- **Equivariance.** Right translation by `g` carries the action of `u` on the smooth functions
to the action of `Ad(g) u`: `ρ(g) (u f) = (Ad(g) u) (ρ(g) f)`. -/
theorem rightTranslate_envelopingAction (g : Langlands.GeneralLinear n ℝ)
    (u : UniversalEnvelopingAlgebra ℂ (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ)) (f : smoothFunctions n) :
    rightTranslate g (envelopingAction smoothLie u f) =
      envelopingAction smoothLie (adU g u) (rightTranslate g f) := by
  rw [← envelopingAction_comp_adLie]
  refine envelopingAction_intertwine smoothLie (smoothLie.comp (adLie g)) (rightTranslate g)
    (fun Y f => ?_) u f
  induction Y using TensorProduct.inductionOn with
  | tmul z X =>
    rw [LieHom.comp_apply, adLie_apply, adAlg_tmul]
    change rightTranslate g (lie _ _ _ (z ⊗ₜ X) f) = lie _ _ _ (z ⊗ₜ conjAlgHom g X) _
    rw [lie_tmul, lie_tmul, LinearMap.smul_apply, LinearMap.smul_apply, map_smul]
    congr 1
    apply Subtype.ext
    rw [derivative_apply_coe]
    exact rightTranslation_rightDerivative (show ContMDiff (matrixModel ℝ n) 𝓘(ℝ, ℂ) ∞
      (f : Langlands.GeneralLinear n ℝ → ℂ) from f.2) X g
  | add Y Z hY hZ =>
    rw [map_add, map_add, LinearMap.add_apply, LinearMap.add_apply, map_add, hY, hZ]

end SmoothRightAction

end Langlands.Archimedean

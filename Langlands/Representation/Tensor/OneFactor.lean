import Langlands.Representation.Smooth.SmoothPart.BasicProof
import Mathlib.Basic.Complex.Basic
import Mathlib.RepresentationTheory.Intertwining

/-!
# Tensor representations with one acting factor

The generic one-factor tensor actions, maps and smoothness results shared by
binary normalized induction and partial derivatives. These declarations retain
their original `Langlands.BinaryTensor` names and definitions.
-/

noncomputable section

open scoped TensorProduct

namespace Langlands.BinaryTensor

universe uG uV uW uX uY uZ uU

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {V' : Type uW} [AddCommGroup V'] [Module ℂ V']
variable {V'' : Type uZ} [AddCommGroup V''] [Module ℂ V'']
variable {W : Type uX} [AddCommGroup W] [Module ℂ W]
variable {W' : Type uY} [AddCommGroup W'] [Module ℂ W']
variable {W'' : Type uU} [AddCommGroup W''] [Module ℂ W'']

/-! ### Tensor products with one acting factor -/

/-- `G` acts on `V ⊗ W` through the second factor only. -/
def secondFactor (V : Type uV) [AddCommGroup V] [Module ℂ V] (σ : Representation ℂ G W) :
    Representation ℂ G (V ⊗[ℂ] W) :=
  Representation.tprod (Representation.trivial ℂ G V) σ

@[simp]
theorem secondFactor_apply (σ : Representation ℂ G W) (g : G) :
    secondFactor V σ g = LinearMap.lTensor V (σ g) := rfl

theorem secondFactor_tmul (σ : Representation ℂ G W) (g : G) (v : V) (w : W) :
    secondFactor V σ g (v ⊗ₜ w) = v ⊗ₜ σ g w := rfl

/-- `G` acts on `V ⊗ W` through the first factor only. -/
def firstFactor (ρ : Representation ℂ G V) (W : Type uX) [AddCommGroup W] [Module ℂ W] :
    Representation ℂ G (V ⊗[ℂ] W) :=
  Representation.tprod ρ (Representation.trivial ℂ G W)

@[simp]
theorem firstFactor_apply (ρ : Representation ℂ G V) (g : G) :
    firstFactor ρ W g = LinearMap.rTensor W (ρ g) := rfl

theorem firstFactor_tmul (ρ : Representation ℂ G V) (g : G) (v : V) (w : W) :
    firstFactor ρ W g (v ⊗ₜ w) = ρ g v ⊗ₜ w := rfl

/-- An arbitrary linear map of the first factor, tensored with an intertwiner. -/
def secondFactorMap {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : V →ₗ[ℂ] V') (g : σ.IntertwiningMap σ') :
    (secondFactor V σ).IntertwiningMap (secondFactor V' σ') where
  toLinearMap := TensorProduct.map f g.toLinearMap
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro v w
    change f v ⊗ₜ g (σ h w) = f v ⊗ₜ σ' h (g w)
    rw [g.isIntertwining]

@[simp]
theorem secondFactorMap_tmul {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : V →ₗ[ℂ] V') (g : σ.IntertwiningMap σ') (v : V) (w : W) :
    secondFactorMap f g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

theorem secondFactorMap_toLinearMap {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : V →ₗ[ℂ] V') (g : σ.IntertwiningMap σ') :
    (secondFactorMap f g).toLinearMap = TensorProduct.map f g.toLinearMap := rfl

theorem secondFactorMap_id (σ : Representation ℂ G W) :
    secondFactorMap (LinearMap.id : V →ₗ[ℂ] V) (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (secondFactor V σ) :=
  Representation.IntertwiningMap.ext TensorProduct.map_id

theorem secondFactorMap_comp {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    {σ'' : Representation ℂ G W''} (f : V →ₗ[ℂ] V') (f' : V' →ₗ[ℂ] V'')
    (g : σ.IntertwiningMap σ') (g' : σ'.IntertwiningMap σ'') :
    secondFactorMap (f' ∘ₗ f) (g'.comp g) = (secondFactorMap f' g').comp (secondFactorMap f g) :=
  Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl)

theorem secondFactorMap_zero_left {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (g : σ.IntertwiningMap σ') : secondFactorMap (0 : V →ₗ[ℂ] V') g = 0 :=
  Representation.IntertwiningMap.ext (TensorProduct.map_zero_left g.toLinearMap)

theorem secondFactorMap_zero_right {σ : Representation ℂ G W} {σ' : Representation ℂ G W'}
    (f : V →ₗ[ℂ] V') : secondFactorMap f (0 : σ.IntertwiningMap σ') = 0 :=
  Representation.IntertwiningMap.ext (TensorProduct.map_zero_right f)

/-- An intertwiner of the first factor, tensored with an arbitrary linear map. -/
def firstFactorMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (g : W →ₗ[ℂ] W') :
    (firstFactor ρ W).IntertwiningMap (firstFactor ρ' W') where
  toLinearMap := TensorProduct.map f.toLinearMap g
  isIntertwining' h := by
    apply TensorProduct.ext'
    intro v w
    change f (ρ h v) ⊗ₜ g w = ρ' h (f v) ⊗ₜ g w
    rw [f.isIntertwining]

@[simp]
theorem firstFactorMap_tmul {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (g : W →ₗ[ℂ] W') (v : V) (w : W) :
    firstFactorMap f g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

theorem firstFactorMap_toLinearMap {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') (g : W →ₗ[ℂ] W') :
    (firstFactorMap f g).toLinearMap = TensorProduct.map f.toLinearMap g := rfl

theorem firstFactorMap_id (ρ : Representation ℂ G V) :
    firstFactorMap (Representation.IntertwiningMap.id ρ) (LinearMap.id : W →ₗ[ℂ] W) =
      Representation.IntertwiningMap.id (firstFactor ρ W) :=
  Representation.IntertwiningMap.ext TensorProduct.map_id

theorem firstFactorMap_comp {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    {ρ'' : Representation ℂ G V''} (f : ρ.IntertwiningMap ρ') (f' : ρ'.IntertwiningMap ρ'')
    (g : W →ₗ[ℂ] W') (g' : W' →ₗ[ℂ] W'') :
    firstFactorMap (f'.comp f) (g' ∘ₗ g) = (firstFactorMap f' g').comp (firstFactorMap f g) :=
  Representation.IntertwiningMap.ext (TensorProduct.ext' fun _ _ => rfl)

theorem firstFactorMap_zero_left {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (g : W →ₗ[ℂ] W') : firstFactorMap (0 : ρ.IntertwiningMap ρ') g = 0 :=
  Representation.IntertwiningMap.ext (TensorProduct.map_zero_left g)

theorem firstFactorMap_zero_right {ρ : Representation ℂ G V} {ρ' : Representation ℂ G V'}
    (f : ρ.IntertwiningMap ρ') : firstFactorMap f (0 : W →ₗ[ℂ] W') = 0 :=
  Representation.IntertwiningMap.ext (TensorProduct.map_zero_right f.toLinearMap)

section Smooth

variable [TopologicalSpace G]

theorem isSmooth_secondFactor {σ : Representation ℂ G W} (hσ : IsSmooth σ) :
    IsSmooth (secondFactor V σ) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨K, hK⟩ := hσ w
    refine ⟨K, ?_⟩
    intro k
    change secondFactor V σ (k : G) (v ⊗ₜ w) = v ⊗ₜ w
    rw [secondFactor_tmul]
    exact congrArg (v ⊗ₜ ·) (hK k)
  | add x y hx hy => exact isSmoothVector_add hx hy

theorem isSmooth_firstFactor {ρ : Representation ℂ G V} (hρ : IsSmooth ρ) :
    IsSmooth (firstFactor ρ W) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w =>
    obtain ⟨K, hK⟩ := hρ v
    refine ⟨K, ?_⟩
    intro k
    change firstFactor ρ W (k : G) (v ⊗ₜ w) = v ⊗ₜ w
    rw [firstFactor_tmul]
    exact congrArg (· ⊗ₜ w) (hK k)
  | add x y hx hy => exact isSmoothVector_add hx hy

end Smooth

end Langlands.BinaryTensor

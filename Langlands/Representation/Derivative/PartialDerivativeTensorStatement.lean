import Langlands.Representation.Derivative.Partial
import Langlands.Representation.Derivative.Iteration
import Langlands.Representation.Tensor.OneFactor

/-!
# The partial derivative of an exterior tensor product

Zelevinsky 1980, Proposition 3.7(a): for every `k, m ≥ 0`, the partial derivative of
`A ⊠ B` for `GL_k × GL_m` is `A ⊗ B^(m)`, where `B^(m)` is the top derivative of `B`
and `GL_k` acts through `A` only. This module packages the raw binary exterior tensor
bifunctor, the first-factor tensor bifunctor and the top derivative, and states the
comparison as a natural isomorphism of actual functors. No proof is supplied.
-/

noncomputable section

open scoped TensorProduct
open CategoryTheory

namespace Langlands.Derivative

universe uF uG uV₁ uV₂ uV₃ uW₁ uW₂ uW₃ uV

namespace PartialTensor

variable {G H : Type uG} [Group G] [Group H]
variable {V₁ : Type uV₁} [AddCommGroup V₁] [Module ℂ V₁]
variable {V₂ : Type uV₂} [AddCommGroup V₂] [Module ℂ V₂]
variable {V₃ : Type uV₃} [AddCommGroup V₃] [Module ℂ V₃]
variable {W₁ : Type uW₁} [AddCommGroup W₁] [Module ℂ W₁]
variable {W₂ : Type uW₂} [AddCommGroup W₂] [Module ℂ W₂]
variable {W₃ : Type uW₃} [AddCommGroup W₃] [Module ℂ W₃]

/-! ## The raw exterior tensor product of `G × H` -/

/-- The ordinary exterior tensor product `ρ ⊠ σ` of `G × H` on `V ⊗[ℂ] W`: Mathlib's
diagonal tensor action after the two coordinate projections. -/
def exterior (ρ : Representation ℂ G V₁) (σ : Representation ℂ H W₁) :
    Representation ℂ (G × H) (V₁ ⊗[ℂ] W₁) :=
  Representation.tprod (ρ.comp (MonoidHom.fst G H)) (σ.comp (MonoidHom.snd G H))

/-- `(g, h) (v ⊗ w) = g v ⊗ h w`. -/
@[simp] theorem exterior_tmul (ρ : Representation ℂ G V₁) (σ : Representation ℂ H W₁)
    (x : G × H) (v : V₁) (w : W₁) :
    exterior ρ σ x (v ⊗ₜ w) = ρ x.1 v ⊗ₜ σ x.2 w := rfl

/-- The tensor product of a `G`-intertwiner and an `H`-intertwiner. -/
def exteriorMap {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ H W₁} {σ₂ : Representation ℂ H W₂}
    (f : ρ₁.IntertwiningMap ρ₂) (g : σ₁.IntertwiningMap σ₂) :
    (exterior ρ₁ σ₁).IntertwiningMap (exterior ρ₂ σ₂) :=
  Representation.IntertwiningMap.tensor
    (ρ := ρ₁.comp (MonoidHom.fst G H)) (σ := ρ₂.comp (MonoidHom.fst G H))
    (τ := σ₁.comp (MonoidHom.snd G H)) (π := σ₂.comp (MonoidHom.snd G H))
    ⟨f.toLinearMap, fun x => f.isIntertwining' x.1⟩
    ⟨g.toLinearMap, fun x => g.isIntertwining' x.2⟩

theorem exteriorMap_toLinearMap {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ H W₁} {σ₂ : Representation ℂ H W₂}
    (f : ρ₁.IntertwiningMap ρ₂) (g : σ₁.IntertwiningMap σ₂) :
    (exteriorMap f g).toLinearMap = TensorProduct.map f.toLinearMap g.toLinearMap := rfl

@[simp] theorem exteriorMap_tmul {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {σ₁ : Representation ℂ H W₁} {σ₂ : Representation ℂ H W₂}
    (f : ρ₁.IntertwiningMap ρ₂) (g : σ₁.IntertwiningMap σ₂) (v : V₁) (w : W₁) :
    exteriorMap f g (v ⊗ₜ w) = f v ⊗ₜ g w := rfl

@[simp] theorem exteriorMap_id (ρ : Representation ℂ G V₁) (σ : Representation ℂ H W₁) :
    exteriorMap (Representation.IntertwiningMap.id ρ) (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (exterior ρ σ) :=
  Representation.IntertwiningMap.ext TensorProduct.map_id

theorem exteriorMap_comp {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} {σ₁ : Representation ℂ H W₁}
    {σ₂ : Representation ℂ H W₂} {σ₃ : Representation ℂ H W₃}
    (f₁ : ρ₁.IntertwiningMap ρ₂) (f₂ : ρ₂.IntertwiningMap ρ₃)
    (g₁ : σ₁.IntertwiningMap σ₂) (g₂ : σ₂.IntertwiningMap σ₃) :
    exteriorMap (f₂.comp f₁) (g₂.comp g₁) = (exteriorMap f₂ g₂).comp (exteriorMap f₁ g₁) :=
  Representation.IntertwiningMap.ext (TensorProduct.map_comp _ _ _ _)

/-! ## `G` acting on `V ⊗[ℂ] W` through the first factor -/

/-- `G` acts on `V ⊗[ℂ] W` through `V` only: Mathlib's tensor action with the trivial
action on `W`. -/
def firstFactor (ρ : Representation ℂ G V₁) (W₁ : Type uW₁) [AddCommGroup W₁]
    [Module ℂ W₁] : Representation ℂ G (V₁ ⊗[ℂ] W₁) :=
  BinaryTensor.firstFactor ρ W₁

/-- `g (v ⊗ z) = g v ⊗ z`. -/
@[simp] theorem firstFactor_tmul (ρ : Representation ℂ G V₁) (g : G) (v : V₁) (z : W₁) :
    firstFactor ρ W₁ g (v ⊗ₜ z) = ρ g v ⊗ₜ z := rfl

/-- The tensor product of a `G`-intertwiner with an arbitrary linear map. -/
def firstFactorMap {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    (f : ρ₁.IntertwiningMap ρ₂) (h : W₁ →ₗ[ℂ] W₂) :
    (firstFactor ρ₁ W₁).IntertwiningMap (firstFactor ρ₂ W₂) :=
  BinaryTensor.firstFactorMap f h

theorem firstFactorMap_toLinearMap {ρ₁ : Representation ℂ G V₁}
    {ρ₂ : Representation ℂ G V₂} (f : ρ₁.IntertwiningMap ρ₂) (h : W₁ →ₗ[ℂ] W₂) :
    (firstFactorMap f h).toLinearMap = TensorProduct.map f.toLinearMap h := rfl

@[simp] theorem firstFactorMap_tmul {ρ₁ : Representation ℂ G V₁}
    {ρ₂ : Representation ℂ G V₂} (f : ρ₁.IntertwiningMap ρ₂) (h : W₁ →ₗ[ℂ] W₂)
    (v : V₁) (z : W₁) :
    firstFactorMap f h (v ⊗ₜ z) = f v ⊗ₜ h z := rfl

@[simp] theorem firstFactorMap_id (ρ : Representation ℂ G V₁) :
    firstFactorMap (W₁ := W₁) (Representation.IntertwiningMap.id ρ) LinearMap.id =
      Representation.IntertwiningMap.id (firstFactor ρ W₁) :=
  Representation.IntertwiningMap.ext TensorProduct.map_id

theorem firstFactorMap_comp {ρ₁ : Representation ℂ G V₁} {ρ₂ : Representation ℂ G V₂}
    {ρ₃ : Representation ℂ G V₃} (f₁ : ρ₁.IntertwiningMap ρ₂) (f₂ : ρ₂.IntertwiningMap ρ₃)
    (h₁ : W₁ →ₗ[ℂ] W₂) (h₂ : W₂ →ₗ[ℂ] W₃) :
    firstFactorMap (f₂.comp f₁) (h₂ ∘ₗ h₁) = (firstFactorMap f₂ h₂).comp (firstFactorMap f₁ h₁) :=
  Representation.IntertwiningMap.ext (TensorProduct.map_comp _ _ _ _)

/-! ## Smoothness -/

section Topology

variable [TopologicalSpace G] [TopologicalSpace H]

/-- A pure tensor of smooth vectors is fixed by the product of their open stabilizers. -/
theorem isSmoothVector_exterior_tmul {ρ : Representation ℂ G V₁}
    {σ : Representation ℂ H W₁} {v : V₁} {w : W₁}
    (hv : IsSmoothVector ρ v) (hw : IsSmoothVector σ w) :
    IsSmoothVector (exterior ρ σ) (v ⊗ₜ w) := by
  obtain ⟨K, hK⟩ := hv
  obtain ⟨L, hL⟩ := hw
  refine ⟨K.prod L, ?_⟩
  change ∀ x : K.prod L, exterior ρ σ (x : G × H) (v ⊗ₜ w) = v ⊗ₜ w
  intro x
  have h₁ : ρ (x : G × H).1 v = v := hK ⟨(x : G × H).1, x.property.1⟩
  have h₂ : σ (x : G × H).2 w = w := hL ⟨(x : G × H).2, x.property.2⟩
  rw [exterior_tmul, h₁, h₂]

theorem isSmooth_exterior (ρ : Representation ℂ G V₁) (σ : Representation ℂ H W₁)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ) : IsSmooth (exterior ρ σ) := by
  intro x
  induction x using TensorProduct.inductionOn with
  | tmul v w => exact isSmoothVector_exterior_tmul (hρ v) (hσ w)
  | add x y hx hy => exact isSmoothVector_add hx hy

/-- A pure tensor with smooth first factor is fixed by the stabilizer of that factor. -/
theorem isSmoothVector_firstFactor_tmul {ρ : Representation ℂ G V₁} {v : V₁}
    (hv : IsSmoothVector ρ v) (z : W₁) :
    IsSmoothVector (firstFactor ρ W₁) (v ⊗ₜ z) := by
  obtain ⟨K, hK⟩ := hv
  refine ⟨K, ?_⟩
  change ∀ g : K, firstFactor ρ W₁ (g : G) (v ⊗ₜ z) = v ⊗ₜ z
  intro g
  have h₁ : ρ (g : G) v = v := hK g
  rw [firstFactor_tmul, h₁]

theorem isSmooth_firstFactor (ρ : Representation ℂ G V₁) (W₁ : Type uW₁)
    [AddCommGroup W₁] [Module ℂ W₁] (hρ : IsSmooth ρ) :
    IsSmooth (firstFactor ρ W₁) :=
  BinaryTensor.isSmooth_firstFactor hρ

/-! ## The two bifunctors -/

/-- The exterior tensor bifunctor `(A, B) ↦ A ⊠ B`, retaining the carrier universe. -/
def exteriorFunctor :
    SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uG, uV} ℂ H ⥤
      SmoothRep.{0, uG, uV} ℂ (G × H) where
  obj X := SmoothRep.of (exterior X.1.representation X.2.representation)
    (isSmooth_exterior _ _ X.1.isSmooth X.2.isSmooth)
  map f := SmoothRep.ofHom (exteriorMap (SmoothRep.hom f.1) (SmoothRep.hom f.2))
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact TensorProduct.map_id
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact TensorProduct.map_comp _ _ _ _

/-- The bifunctor `(A, B) ↦ A ⊗[ℂ] B`, with `G` acting through `A` only and the action
of `H` on `B` forgotten; the map of `(f, g)` is `f ⊗ g` on underlying linear maps. -/
def firstFactorFunctor :
    SmoothRep.{0, uG, uV} ℂ G × SmoothRep.{0, uG, uV} ℂ H ⥤
      SmoothRep.{0, uG, uV} ℂ G where
  obj X := SmoothRep.of (firstFactor X.1.representation X.2)
    (isSmooth_firstFactor _ _ X.1.isSmooth)
  map f := SmoothRep.ofHom (firstFactorMap (SmoothRep.hom f.1) (SmoothRep.hom f.2).toLinearMap)
  map_id X := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact TensorProduct.map_id
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact TensorProduct.map_comp _ _ _ _

end Topology

end PartialTensor

/-! ## The functors for `GL_k × GL_m` -/

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}

/-- The exterior tensor bifunctor `(A, B) ↦ A ⊠ B` for `GL_k × GL_m`. -/
def exteriorTensor (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier × GeneralLinear m F.Carrier) := by
  letI := T.topology
  exact PartialTensor.exteriorFunctor

/-- The top derivative `GL_m → GL_0`: the published order-`m` derivative followed by the
rank transport along `m - m = 0`. -/
def topDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier) := by
  letI := T.topology
  exact generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙ generalLinearRankCast T (Nat.sub_self m)

/-- The bifunctor `(A, B) ↦ A ⊗[ℂ] D_m(B)` with `GL_k` acting through `A` only. -/
def firstFactorTopDerivative (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier) ⥤
      SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) := by
  letI := T.topology
  exact (𝟭 _).prod (topDerivative T ψ m) ⋙ PartialTensor.firstFactorFunctor

/-! ## Unfolding lemmas -/

theorem exteriorTensor_obj_carrier (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier),
      ((exteriorTensor T k m).obj X : Type uV) = (X.1 ⊗[ℂ] X.2) := by
  intros
  rfl

theorem exteriorTensor_action_tmul (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
      (g : GeneralLinear k F.Carrier) (h : GeneralLinear m F.Carrier) (v : X.1) (w : X.2),
      ((exteriorTensor T k m).obj X).representation (g, h) (v ⊗ₜ w) =
        (X.1.representation g v ⊗ₜ X.2.representation h w : X.1 ⊗[ℂ] X.2) := by
  intros
  rfl

theorem exteriorTensor_map_toLinearMap (T : F.TopologicalData) (k m : ℕ) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)} (f : X ⟶ Y),
      (SmoothRep.hom ((exteriorTensor T k m).map f)).toLinearMap =
        TensorProduct.map (SmoothRep.hom f.1).toLinearMap (SmoothRep.hom f.2).toLinearMap := by
  intros
  rfl

theorem topDerivative_eq (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (m : ℕ) :
    letI := T.topology
    topDerivative.{uF, uV} T ψ m =
      generalLinearDerivative T ψ m m (Nat.le_refl m) ⋙
        generalLinearRankCast T (Nat.sub_self m) :=
  rfl

/-- The zeroth top derivative is the identity functor of `GL_0`. -/
theorem topDerivative_zero (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) :
    letI := T.topology
    topDerivative.{uF, uV} T ψ 0 = 𝟭 (SmoothRep.{0, uF, uV} ℂ (GeneralLinear 0 F.Carrier)) :=
  rfl

theorem firstFactorTopDerivative_obj_carrier (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier),
      ((firstFactorTopDerivative T ψ k m).obj X : Type uV) =
        (X.1 ⊗[ℂ] (topDerivative T ψ m).obj X.2) := by
  intros
  rfl

theorem firstFactorTopDerivative_action_tmul (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ (X : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier))
      (g : GeneralLinear k F.Carrier) (v : X.1) (z : (topDerivative T ψ m).obj X.2),
      ((firstFactorTopDerivative T ψ k m).obj X).representation g (v ⊗ₜ z) =
        (X.1.representation g v ⊗ₜ z : X.1 ⊗[ℂ] (topDerivative T ψ m).obj X.2) := by
  intros
  rfl

theorem firstFactorTopDerivative_map_toLinearMap (T : F.TopologicalData)
    (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ) :
    letI := T.topology
    ∀ {X Y : SmoothRep.{0, uF, uV} ℂ (GeneralLinear k F.Carrier) ×
        SmoothRep.{0, uF, uV} ℂ (GeneralLinear m F.Carrier)} (f : X ⟶ Y),
      (SmoothRep.hom ((firstFactorTopDerivative T ψ k m).map f)).toLinearMap =
        TensorProduct.map (SmoothRep.hom f.1).toLinearMap
          (SmoothRep.hom ((topDerivative T ψ m).map f.2)).toLinearMap := by
  intros
  rfl

/-! ## The comparison -/

variable (F) in
/-- Zelevinsky 1980, Proposition 3.7(a), for all `k, m ≥ 0`: the partial derivative of
the exterior tensor bifunctor is naturally isomorphic to the first factor tensored with
the top derivative of the second factor. -/
def PartialDerivativeTensorStatement (T : F.TopologicalData) : Prop :=
  letI := T.topology
  ∀ (ψ : @HarmonicAnalysis.UnitaryAdditiveCharacter F.Carrier _ T.topology) (k m : ℕ),
    Nonempty (exteriorTensor.{uF, uV} T k m ⋙ partialDerivative T ψ k m ≅
      firstFactorTopDerivative T ψ k m)

end Langlands.Derivative

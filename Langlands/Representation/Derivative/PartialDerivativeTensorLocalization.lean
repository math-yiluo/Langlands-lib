import Langlands.Representation.Derivative.PartialDerivativeTensorStatement

/-! # Binary exterior tensors and partial localization -/

noncomputable section

open scoped TensorProduct
open CategoryTheory

namespace Langlands.Derivative.PartialTensor

universe uF uV uW uV' uW'

open GeneralLinear Jacquet.Localization

variable {F : Type uF} [CommRing F]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable (ψ : AddChar F ℂ) (k m : ℕ)
variable (ρ : Representation ℂ (GeneralLinear k F) V)
variable (σ : Representation ℂ (GeneralLinear m F) W)

/-- Localizing the second factor gives the forward tensor quotient map. -/
def localizationToTensor :
    Partial.Quotient ψ k m (exterior ρ σ) →ₗ[ℂ]
      V ⊗[ℂ] Coinvariants σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) :=
  lift (exterior ρ σ) (Partial.unipotent F k m) (Partial.character ψ k m)
    (TensorProduct.map LinearMap.id
      (mk σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m))) (by
    intro u x
    induction x using TensorProduct.inductionOn with
    | tmul v w =>
      have hu : u.val.1 = 1 := u.property.1
      change ρ u.val.1 v ⊗ₜ mk σ _ _ (σ u.val.2 w) =
        (Partial.character ψ k m u : ℂ) • (v ⊗ₜ mk σ _ _ w)
      rw [hu, map_one, Module.End.one_apply]
      rw [show σ u.val.2 w = σ (Partial.second F k m u) w from rfl,
        mk_apply_subgroup, TensorProduct.tmul_smul]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy, smul_add])

@[simp] theorem localizationToTensor_mk_tmul (v : V) (w : W) :
    localizationToTensor ψ k m ρ σ (Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ w)) =
      v ⊗ₜ mk σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) w := rfl

/-- Descend the second variable of the quotient-valued bilinear tensor map. -/
def localizationTensorBilinear :
    Coinvariants σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) →ₗ[ℂ]
      V →ₗ[ℂ] Partial.Quotient ψ k m (exterior ρ σ) :=
  lift σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m)
    ((TensorProduct.mk ℂ V W).flip.compr₂ (Partial.mk ψ k m (exterior ρ σ))) (by
    intro u w
    apply LinearMap.ext
    intro v
    change Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ σ u w) =
      (Whittaker.entrywiseCharacter ψ m u : ℂ) •
        Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ w)
    have h := Partial.mk_unipotent ψ k m (exterior ρ σ) u (v ⊗ₜ w)
    simpa only [exterior_tmul, map_one, Module.End.one_apply] using h)

/-- Tensor a vector with a localized class and take its class in the tensor quotient. -/
def tensorToLocalization :
    V ⊗[ℂ] Coinvariants σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) →ₗ[ℂ]
      Partial.Quotient ψ k m (exterior ρ σ) :=
  TensorProduct.lift (localizationTensorBilinear ψ k m ρ σ).flip

@[simp] theorem tensorToLocalization_tmul_mk (v : V) (w : W) :
    tensorToLocalization ψ k m ρ σ
      (v ⊗ₜ mk σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) w) =
      Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ w) := rfl

theorem localizationToTensor_comp_tensorToLocalization :
    (localizationToTensor ψ k m ρ σ).comp (tensorToLocalization ψ k m ρ σ) =
      LinearMap.id := by
  apply TensorProduct.ext'
  intro v q
  obtain ⟨w, rfl⟩ := mk_surjective σ (upperUnipotent m F)
    (Whittaker.entrywiseCharacter ψ m) q
  rfl

theorem tensorToLocalization_comp_localizationToTensor :
    (tensorToLocalization ψ k m ρ σ).comp (localizationToTensor ψ k m ρ σ) =
      LinearMap.id := by
  apply hom_ext
  apply TensorProduct.ext'
  intro v w
  rfl

/-- The two quotient universal properties give inverse linear maps. -/
def localizationTensorLinearEquiv :
    Partial.Quotient ψ k m (exterior ρ σ) ≃ₗ[ℂ]
      V ⊗[ℂ] Coinvariants σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) :=
  LinearEquiv.ofLinearMap (localizationToTensor ψ k m ρ σ)
    (tensorToLocalization ψ k m ρ σ)
    (localizationToTensor_comp_tensorToLocalization ψ k m ρ σ)
    (tensorToLocalization_comp_localizationToTensor ψ k m ρ σ)

/-- The tensor quotient comparison respects the actual first-factor action. -/
def localizationTensorEquiv :
    (Partial.action ψ k m (exterior ρ σ)).Equiv
      (firstFactor ρ
        (Coinvariants σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m))) where
  toLinearEquiv := localizationTensorLinearEquiv ψ k m ρ σ
  isIntertwining' g := by
    apply hom_ext
    apply TensorProduct.ext'
    intro v w
    change localizationToTensor ψ k m ρ σ
        (Partial.mk ψ k m (exterior ρ σ) (exterior ρ σ (g, 1) (v ⊗ₜ w))) =
      firstFactor ρ _ g
        (localizationToTensor ψ k m ρ σ (Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ w)))
    simp only [exterior_tmul, map_one, Module.End.one_apply,
      localizationToTensor_mk_tmul, firstFactor_tmul]

@[simp] theorem localizationTensorEquiv_mk_tmul (v : V) (w : W) :
    localizationTensorEquiv ψ k m ρ σ
      (Partial.mk ψ k m (exterior ρ σ) (v ⊗ₜ w)) =
      v ⊗ₜ mk σ (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) w := rfl

variable {V' : Type uV'} [AddCommGroup V'] [Module ℂ V']
variable {W' : Type uW'} [AddCommGroup W'] [Module ℂ W']

/-- Naturality in both representations, for arbitrary intertwiners. -/
theorem localizationTensorEquiv_natural
    {ρ' : Representation ℂ (GeneralLinear k F) V'}
    {σ' : Representation ℂ (GeneralLinear m F) W'}
    (f : ρ.IntertwiningMap ρ') (g : σ.IntertwiningMap σ') :
    (firstFactorMap f
      (mapLinear (upperUnipotent m F) (Whittaker.entrywiseCharacter ψ m) g)).comp
        (localizationTensorEquiv ψ k m ρ σ).toIntertwiningMap =
      (localizationTensorEquiv ψ k m ρ' σ').toIntertwiningMap.comp
        (Partial.map ψ k m (exteriorMap f g)) := by
  apply Representation.IntertwiningMap.ext
  apply hom_ext
  apply TensorProduct.ext'
  intro v w
  rfl

section Smooth

variable [TopologicalSpace F]

/-- Full upper-unipotent coinvariants, retaining the entire carrier as a trivial
representation of `GL_0`. -/
def upperCoinvariantsFunctor (ψ : AddChar F ℂ) (m : ℕ) :
    SmoothRep.{0,uF,uV} ℂ (GeneralLinear m F) ⥤
      SmoothRep.{0,uF,uV} ℂ (GeneralLinear 0 F) where
  obj A := SmoothRep.of
    (1 : Representation ℂ (GeneralLinear 0 F)
      (Coinvariants A.representation (upperUnipotent m F)
        (Whittaker.entrywiseCharacter ψ m)))
    (fun _ => ⟨⊤, fun _ => rfl⟩)
  map f := SmoothRep.ofHom
    { toLinearMap := mapLinear (upperUnipotent m F)
        (Whittaker.entrywiseCharacter ψ m) (SmoothRep.hom f)
      isIntertwining' _ := rfl }
  map_id A := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hom_ext rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    exact hom_ext rfl

/-- The smooth binary tensor quotient comparison, natural in both factors. -/
def localizationTensorIso (ψ : AddChar F ℂ) (k m : ℕ) :
    exteriorFunctor.{uF,uV} ⋙ Partial.smoothFunctor ψ k m ≅
      (𝟭 _).prod (upperCoinvariantsFunctor ψ m) ⋙ firstFactorFunctor :=
  NatIso.ofComponents
    (fun X => SmoothRep.mkIso (localizationTensorEquiv ψ k m
      X.1.representation X.2.representation)) (by
      intro X Y f
      apply ObjectProperty.hom_ext
      apply Rep.hom_ext
      exact (localizationTensorEquiv_natural ψ k m X.1.representation
        X.2.representation (SmoothRep.hom f.1) (SmoothRep.hom f.2)).symm)

end Smooth

end Langlands.Derivative.PartialTensor

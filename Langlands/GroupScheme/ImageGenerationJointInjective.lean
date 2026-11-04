import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage

/-! # Joint injectivity of global sections of tensor products over a field -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory

namespace Langlands.GroupScheme.ImageGeneration

section Linear

variable {k : Type*} [Field k]

/-- Coordinates of an element of `M ⊗ Q` along the chosen basis of the vector space `M`. -/
def basisTensorEquiv (M Q : Type*) [AddCommGroup M] [Module k M] [AddCommGroup Q]
    [Module k Q] : M ⊗[k] Q ≃ₗ[k] (Module.Free.ChooseBasisIndex k M →₀ Q) :=
  TensorProduct.congr (Module.Free.chooseBasis k M).repr (LinearEquiv.refl k Q) ≪≫ₗ
    finsuppScalarLeft k Q _

theorem basisTensorEquiv_lTensor {M Q Q' : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup Q] [Module k Q] [AddCommGroup Q'] [Module k Q'] (v : Q →ₗ[k] Q')
    (x : M ⊗[k] Q) (i : Module.Free.ChooseBasisIndex k M) :
    basisTensorEquiv M Q' (v.lTensor M x) i = v (basisTensorEquiv M Q x i) := by
  induction x using TensorProduct.inductionOn with
  | tmul m q => simp [basisTensorEquiv]
  | add x y hx hy => simp [hx, hy]

variable {M N : Type*} [AddCommGroup M] [Module k M] [AddCommGroup N] [Module k N]

/-- Left tensoring with a vector space preserves joint injectivity of linear maps. -/
theorem lTensor_eq_zero_of_forall {J : Type*} {P : J → Type*} [∀ j, AddCommGroup (P j)]
    [∀ j, Module k (P j)] (v : ∀ j, N →ₗ[k] P j) (hv : ∀ y, (∀ j, v j y = 0) → y = 0)
    (x : M ⊗[k] N) (hx : ∀ j, (v j).lTensor M x = 0) : x = 0 := by
  have h : basisTensorEquiv M N x = 0 := by
    ext i
    rw [Finsupp.coe_zero, Pi.zero_apply]
    refine hv _ fun j => ?_
    rw [← basisTensorEquiv_lTensor, hx j, map_zero, Finsupp.coe_zero, Pi.zero_apply]
  exact (basisTensorEquiv M N).injective (h.trans (map_zero _).symm)

/-- Right tensoring with a vector space preserves joint injectivity of linear maps. -/
theorem rTensor_eq_zero_of_forall {I : Type*} {P : I → Type*} [∀ i, AddCommGroup (P i)]
    [∀ i, Module k (P i)] (u : ∀ i, M →ₗ[k] P i) (hu : ∀ y, (∀ i, u i y = 0) → y = 0)
    (x : M ⊗[k] N) (hx : ∀ i, (u i).rTensor N x = 0) : x = 0 := by
  have hc : ∀ i (y : M ⊗[k] N), (u i).lTensor N (TensorProduct.comm k M N y) =
      TensorProduct.comm k (P i) N ((u i).rTensor N y) := by
    intro i y
    induction y using TensorProduct.inductionOn with
    | tmul m n => simp
    | add y z hy hz => simp only [map_add, hy, hz]
  have h := lTensor_eq_zero_of_forall u hu (TensorProduct.comm k M N x) fun i => by
    rw [hc, hx i, map_zero]
  exact (TensorProduct.comm k M N).injective (h.trans (map_zero _).symm)

/-- Over a field, tensor products of jointly injective families are jointly injective. -/
theorem map_eq_zero_of_forall {I J : Type*} {P : I → Type*} {Q : J → Type*}
    [∀ i, AddCommGroup (P i)] [∀ i, Module k (P i)] [∀ j, AddCommGroup (Q j)]
    [∀ j, Module k (Q j)] (u : ∀ i, M →ₗ[k] P i) (v : ∀ j, N →ₗ[k] Q j)
    (hu : ∀ y, (∀ i, u i y = 0) → y = 0) (hv : ∀ y, (∀ j, v j y = 0) → y = 0)
    (x : M ⊗[k] N) (hx : ∀ i j, TensorProduct.map (u i) (v j) x = 0) : x = 0 := by
  refine rTensor_eq_zero_of_forall u hu x fun i => ?_
  refine lTensor_eq_zero_of_forall v hv _ fun j => ?_
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor, hx i j]

end Linear

section Sections

variable {k : Type u} [Field k]

/-- The `k`-algebra structure on the global sections of a scheme over `Spec k`. -/
abbrev sectionsAlgebra (X : Over (Spec (CommRingCat.of k))) : Algebra k Γ(X.left, ⊤) :=
  Scheme.TwoAffineOpenCover.algebraOfHom X.hom ⊤

attribute [local instance] sectionsAlgebra

open P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.P2mKDeg0
  (appLE_top_top)

/-- `appLE` at the top opens, with the inclusion proof stated as `⊤ ≤ ⊤` as it appears in
`Scheme.TwoAffineOpenCover.algebraOfHom`. -/
theorem appLE_top_top_of_le {P Q : Scheme.{u}} (φ : P ⟶ Q) (e : (⊤ : P.Opens) ≤ ⊤) :
    φ.appLE ⊤ ⊤ e = φ.appTop :=
  appLE_top_top φ e

/-- Global sections of a morphism over `Spec k`, as a homomorphism of `k`-algebras. -/
def sectionsHom {X Y : Over (Spec (CommRingCat.of k))} (a : X ⟶ Y) :
    Γ(Y.left, ⊤) →ₐ[k] Γ(X.left, ⊤) where
  toRingHom := a.left.appTop.hom
  commutes' r := by
    change a.left.appTop.hom ((Y.hom.appLE ⊤ ⊤ _).hom _) = (X.hom.appLE ⊤ ⊤ _).hom _
    rw [appLE_top_top_of_le, appLE_top_top_of_le, ← Over.w a, Scheme.Hom.comp_appTop,
      CommRingCat.comp_apply]

@[simp] theorem sectionsHom_apply {X Y : Over (Spec (CommRingCat.of k))} (a : X ⟶ Y)
    (s : Γ(Y.left, ⊤)) : sectionsHom a s = a.left.appTop.hom s := rfl

/-- The comparison map from the tensor product of global sections to the global sections of
the tensor product. -/
def tensorSections (X Y : Over (Spec (CommRingCat.of k))) :
    Γ(X.left, ⊤) ⊗[k] Γ(Y.left, ⊤) →ₐ[k] Γ((X ⊗ Y).left, ⊤) :=
  Algebra.TensorProduct.productMap (sectionsHom (fst X Y)) (sectionsHom (snd X Y))

theorem tensorSections_tmul (X Y : Over (Spec (CommRingCat.of k))) (a : Γ(X.left, ⊤))
    (b : Γ(Y.left, ⊤)) : tensorSections X Y (a ⊗ₜ b) =
      (fst X Y).left.appTop.hom a * (snd X Y).left.appTop.hom b := rfl

/-- Naturality of the comparison map for tensor products of morphisms. -/
theorem appTop_tensorHom_tensorSections {X X' Y Y' : Over (Spec (CommRingCat.of k))}
    (a : X' ⟶ X) (b : Y' ⟶ Y) (x : Γ(X.left, ⊤) ⊗[k] Γ(Y.left, ⊤)) :
    (a ⊗ₘ b).left.appTop.hom (tensorSections X Y x) =
      tensorSections X' Y' (TensorProduct.map (sectionsHom a).toLinearMap
        (sectionsHom b).toLinearMap x) := by
  induction x using TensorProduct.inductionOn with
  | tmul x y =>
    rw [TensorProduct.map_tmul, tensorSections_tmul, tensorSections_tmul, map_mul]
    congr 1
    · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, tensorHom_fst,
        Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
    · rw [← CommRingCat.comp_apply, ← Scheme.Hom.comp_appTop, ← Over.comp_left, tensorHom_snd,
        Over.comp_left, Scheme.Hom.comp_appTop, CommRingCat.comp_apply]
      rfl
  | add x y hx hy => rw [map_add, map_add, hx, hy, map_add, map_add]

theorem bijective_presheaf_map_of_eq_top {P : Scheme.{u}} {W : P.Opens} (h : W = ⊤) :
    Function.Bijective (P.presheaf.map (homOfLE (le_top : W ≤ ⊤)).op).hom := by
  subst h
  have : (homOfLE (le_top : (⊤ : P.Opens) ≤ ⊤)).op = 𝟙 _ := Subsingleton.elim _ _
  rw [this, P.presheaf.map_id]
  exact Function.bijective_id

/-- For affine schemes over a field, the comparison map is bijective. -/
theorem tensorSections_bijective (X Y : Over (Spec (CommRingCat.of k))) [IsAffine X.left]
    [IsAffine Y.left] : Function.Bijective (tensorSections X Y) := by
  let := Scheme.TwoAffineOpenCover.algebraOfHom (pullback.fst X.hom Y.hom ≫ X.hom)
    (pullback.fst X.hom Y.hom ⁻¹ᵁ ⊤ ⊓ pullback.snd X.hom Y.hom ⁻¹ᵁ ⊤)
  obtain ⟨-, e, he⟩ :=
    P2MW.S_AlgebraicGeometry_Scheme_Pullback_isAffineOpen_and_exists_algEquiv_tensor_sections_fst_preimage_inf_snd_preimage.solution
      X.hom Y.hom ⊤ (isAffineOpen_top _) ⊤ (isAffineOpen_top _)
  have hW : pullback.fst X.hom Y.hom ⁻¹ᵁ ⊤ ⊓ pullback.snd X.hom Y.hom ⁻¹ᵁ ⊤ = ⊤ := by simp
  have hρ := bijective_presheaf_map_of_eq_top hW
  have key : ∀ x, ((pullback X.hom Y.hom).presheaf.map (homOfLE le_top).op).hom
      (tensorSections X Y x) = e x := by
    intro x
    induction x using TensorProduct.inductionOn with
    | tmul a b => rw [tensorSections_tmul, map_mul, he]; rfl
    | add x y hx hy => rw [map_add, map_add, hx, hy, map_add]
  constructor
  · intro x y hxy
    apply e.injective
    rw [← key, ← key, hxy]
  · intro s
    obtain ⟨x, hx⟩ := e.surjective (((pullback X.hom Y.hom).presheaf.map
      (homOfLE le_top).op).hom s)
    exact ⟨x, hρ.1 ((key x).trans hx)⟩

/-- Over a field, tensor products of morphisms of affine schemes whose global-section maps
are jointly injective again have jointly injective global-section maps. -/
theorem appTop_tensorHom_eq_zero {X Y : Over (Spec (CommRingCat.of k))} {I J : Type*}
    {X' : I → Over (Spec (CommRingCat.of k))} {Y' : J → Over (Spec (CommRingCat.of k))}
    (a : ∀ i, X' i ⟶ X) (b : ∀ j, Y' j ⟶ Y) [IsAffine X.left] [IsAffine Y.left]
    [∀ i, IsAffine (X' i).left] [∀ j, IsAffine (Y' j).left]
    (ha : ∀ s : Γ(X.left, ⊤), (∀ i, (a i).left.appTop.hom s = 0) → s = 0)
    (hb : ∀ s : Γ(Y.left, ⊤), (∀ j, (b j).left.appTop.hom s = 0) → s = 0)
    (s : Γ((X ⊗ Y).left, ⊤)) (hs : ∀ i j, (a i ⊗ₘ b j).left.appTop.hom s = 0) : s = 0 := by
  obtain ⟨x, rfl⟩ := (tensorSections_bijective X Y).2 s
  have hx : x = 0 := by
    refine map_eq_zero_of_forall (fun i => (sectionsHom (a i)).toLinearMap)
      (fun j => (sectionsHom (b j)).toLinearMap) ha hb x fun i j => ?_
    apply (tensorSections_bijective (X' i) (Y' j)).1
    rw [← appTop_tensorHom_tensorSections, hs i j, map_zero]
  rw [hx, map_zero]

end Sections

end Langlands.GroupScheme.ImageGeneration

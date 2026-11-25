/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Cohomology.DirectImage.Basic
public import WeilConjectures.AlgebraicGeometry.Modules.Dual
public import WeilConjectures.AlgebraicGeometry.Modules.ProjectionFormula
public import WeilConjectures.CategoryTheory.Abelian.RightDerived.Comp

/-!
# The projection formula for higher direct images

For `f : X ⟶ T`, an `𝒪_X`-module `ℱ` and an invertible `𝒪_T`-module `𝒩`,
`R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩`
(`AlgebraicGeometry.Scheme.Modules.higherDirectImageTensorObjPullbackIso`).

The projection morphism `f_* ℱ ⊗ 𝒩 ⟶ f_* (ℱ ⊗ f^* 𝒩)` is natural in `ℱ`
(`AlgebraicGeometry.Scheme.Modules.projectionHom_naturality`), so it is a natural isomorphism
`f_* ⋙ (- ⊗ 𝒩) ≅ (- ⊗ f^* 𝒩) ⋙ f_*`. Twisting by an invertible module is an autoequivalence, hence
exact and preserving injective objects, so taking right derived functors of both sides gives the
projection formula.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory Opposite

namespace AlgebraicGeometry.Scheme.Modules

variable {X Y : Scheme.{u}}

section ProjectionHom

attribute [local instance] presheafMonoidalCategory presheafSymmetricCategory
  SheafOfModules.sheafificationMonoidal SheafOfModules.sheafificationBraided
  sheafificationMonoidal sheafificationBraided forgetToPresheafOfModulesLaxMonoidal

/-- Morphisms out of a tensor product of `𝒪_Y`-modules are determined by their restriction to
the presheaf tensor product. -/
lemma tensorObj_hom_ext {M N P : Y.Modules} {a b : M ⊗ N ⟶ P}
    (h : Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) M N ≫
        (forgetToPresheafOfModules Y).map a =
      Functor.LaxMonoidal.μ (forgetToPresheafOfModules Y) M N ≫
        (forgetToPresheafOfModules Y).map b) : a = b := by
  rw [Adjunction.rightAdjointLaxMonoidal_μ, ← Adjunction.homEquiv_naturality_right,
    ← Adjunction.homEquiv_naturality_right] at h
  exact (cancel_epi _).1 (((sheafificationAdjunction Y).homEquiv _ _).injective h)

variable (g : X ⟶ Y) (N : Y.Modules)

/-- **Naturality of the projection morphism** `g_* F ⊗ N ⟶ g_* (F ⊗ g^* N)` in `F`. -/
lemma projectionHom_naturality {F F' : X.Modules} (φ : F ⟶ F') :
    ((pushforward g).map φ ▷ N) ≫ projectionHom g F' N =
      projectionHom g F N ≫ (pushforward g).map (φ ▷ (pullback g).obj N) := by
  refine tensorObj_hom_ext ?_
  rw [Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Functor.LaxMonoidal.μ_natural_left,
    Category.assoc, μ_comp_map_projectionHom, ← Category.assoc, μ_comp_map_projectionHom]
  ext U x
  induction x using TensorProduct.inductionOn with
  | tmul a n =>
    rw [PresheafOfModules.comp_app, PresheafOfModules.comp_app, ModuleCat.hom_comp,
      ModuleCat.hom_comp, LinearMap.comp_apply, LinearMap.comp_apply]
    exact (whiskerRight_app_tmulSection (U := g ⁻¹ᵁ U.unop) φ a _).symm
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/-- The projection formula `g_* F ⊗ N ≅ g_* (F ⊗ g^* N)` for an invertible `N`, as a natural
isomorphism `g_* ⋙ (- ⊗ N) ≅ (- ⊗ g^* N) ⋙ g_*`. -/
noncomputable def projectionNatIso [N.IsInvertible] :
    pushforward g ⋙ tensorRight N ≅ tensorRight ((pullback g).obj N) ⋙ pushforward g :=
  NatIso.ofComponents (fun F ↦ have := isIso_projectionHom g F N; asIso (projectionHom g F N))
    (fun φ ↦ projectionHom_naturality g N φ)

end ProjectionHom

/-- Tensoring with an invertible module is an autoequivalence. -/
lemma isEquivalence_tensorRight_of_isInvertible (P : X.Modules) [P.IsInvertible] :
    (tensorRight P).IsEquivalence :=
  (BraidedCategory.tensorRightEquivalence P Pᵛ
    (nonempty_tensorObj_dual_iso_unit P).some).isEquivalence_functor

/-- **The projection formula for higher direct images** and an invertible module: for
`f : X ⟶ Y`, an `𝒪_X`-module `ℱ` and an invertible `𝒪_Y`-module `𝒩`,
`R^q f_* (ℱ ⊗ f^* 𝒩) ≅ R^q f_* ℱ ⊗ 𝒩`. Twisting by `f^* 𝒩` is an autoequivalence of `X.Modules`,
so it is exact and preserves injective objects, and
`R^q (f_* ∘ (- ⊗ f^* 𝒩)) ≅ R^q f_* ∘ (- ⊗ f^* 𝒩)`;
twisting by `𝒩` is exact, so `R^q ((- ⊗ 𝒩) ∘ f_*) ≅ (- ⊗ 𝒩) ∘ R^q f_*`; and the two composites
are isomorphic by the projection formula `projectionNatIso`.

(blueprint: `lem-pc-projection-formula`) -/
noncomputable def higherDirectImageTensorObjPullbackIso [HasInjectiveResolutions X.Modules]
    (f : X ⟶ Y) (ℱ : X.Modules) (𝒩 : Y.Modules) [𝒩.IsInvertible] (q : ℕ) :
    (higherDirectImage f q).obj (ℱ ⊗ (pullback f).obj 𝒩) ≅ (higherDirectImage f q).obj ℱ ⊗ 𝒩 :=
  have := isEquivalence_tensorRight_of_isInvertible ((pullback f).obj 𝒩)
  have := isEquivalence_tensorRight_of_isInvertible 𝒩
  have := Functor.additive_of_preserves_binary_products (tensorRight ((pullback f).obj 𝒩))
  have := Functor.additive_of_preserves_binary_products (tensorRight 𝒩)
  (Functor.compRightDerivedObjIso (tensorRight ((pullback f).obj 𝒩)) (pushforward f)
    (fun _ _ ↦ Functor.rightAcyclic_of_injective _) q ℱ).symm ≪≫
  Functor.rightDerivedObjIsoOfIso (projectionNatIso f 𝒩).symm q ℱ ≪≫
  Functor.rightDerivedCompObjIso (pushforward f) (tensorRight 𝒩) q ℱ

end AlgebraicGeometry.Scheme.Modules

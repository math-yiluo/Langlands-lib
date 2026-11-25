/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.ModuleObjects.ExtendScalars

/-! # Scalar extension of the regular module and its endomorphisms -/

@[expose] public section
set_option backward.isDefEq.respectTransparency.types false

universe u v
open CategoryTheory Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace CategoryTheory.Mod
variable {C : Type u} [Category.{v} C] [MonoidalCategory C] [BraidedCategory C]
  [HasCoequalizers C] [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : C, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  {R S : C} [MonObj R] [MonObj S] [IsCommMonObj R]
  (φ : R ⟶ S) [IsMonHom φ]

/-- The coefficient map as a map of regular modules.
Source: the extension--restriction adjunction.
(auxiliary; not a blueprint node) -/
noncomputable def regularCoefficientMap : regular R ⟶ (comap φ).obj (regular S) :=
  homMk φ (by
    change μ[R] ≫ φ = R ◁ φ ≫ φ ▷ S ≫ μ[S]
    rw [IsMonHom.mul_hom, tensorHom_def']
    exact Category.assoc _ _ _)

/-- Extension of scalars sends the regular module to the regular module.
Source: the extension--restriction adjunction and the universal property of the regular module.
(auxiliary; not a blueprint node)

Proof: extend the coefficient map. In the other direction use the unique S-linear map
sending 1 to the image of 1 under the adjunction unit. The two composite identities follow
from the regular-module universal property and the adjunction identities. -/
noncomputable def regularExtensionIso :
    (extendScalars φ).obj (regular R) ≅ regular S := by
  let h := regularCoefficientMap φ
  let f := extendHom φ h
  let g := regularLift ((extendScalars φ).obj (regular R))
    (η[R] ≫ extendUnitHom φ (regular R))
  have hf : extendUnitHom φ (regular R) ≫ f.hom = φ :=
    extendUnitHom_extendHom φ h
  have hg : η[S] ≫ g.hom = η[R] ≫ extendUnitHom φ (regular R) :=
    one_comp_regularLift _ _
  have hgf : g ≫ f = 𝟙 _ := by
    apply regular_hom_ext
    change η[S] ≫ g.hom ≫ f.hom = η[S] ≫ 𝟙 S
    rw [← Category.assoc, hg, Category.assoc, hf, IsMonHom.one_hom (f := φ)]
    exact (Category.comp_id _).symm
  have hfg : f ≫ g = 𝟙 _ := by
    apply (extendHomEquiv φ (regular R) ((extendScalars φ).obj (regular R))).injective
    apply regular_hom_ext
    change η[R] ≫ (extendUnitHom φ (regular R) ≫ f.hom ≫ g.hom) =
      η[R] ≫ (extendUnitHom φ (regular R) ≫ 𝟙 _)
    rw [← Category.assoc (extendUnitHom φ (regular R)) f.hom g.hom, hf,
      ← Category.assoc, IsMonHom.one_hom (f := φ), hg, Category.comp_id]
  exact ⟨f, g, hfg, hgf⟩

/-- A commuting square of regular endomorphisms extends to its scalar-extension square.
Source: naturality of the extension--restriction adjunction.
(auxiliary; not a blueprint node) -/
theorem regularExtensionIso_naturality
    (p : regular R ⟶ regular R) (q : regular S ⟶ regular S)
    (h : p.hom ≫ φ = φ ≫ q.hom) :
    (extendScalars φ).map p ≫ (regularExtensionIso φ).hom =
      (regularExtensionIso φ).hom ≫ q := by
  apply (extendHomEquiv φ (regular R) (regular S)).injective
  apply hom_ext
  have hn : p.hom ≫ extendUnitHom φ (regular R) =
      extendUnitHom φ (regular R) ≫ ((extendScalars φ).map p).hom :=
    by
      change p.hom ≫ extendUnitHom φ (regular R) =
        extendUnitHom φ (regular R) ≫ (extendScalarsMap φ p).hom
      dsimp only [extendUnitHom]
      simp only [Category.assoc, extendπ_extendScalarsMap]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc]
  change extendUnitHom φ (regular R) ≫ ((extendScalars φ).map p).hom ≫
      (extendHom φ (regularCoefficientMap φ)).hom =
    extendUnitHom φ (regular R) ≫ (extendHom φ (regularCoefficientMap φ)).hom ≫ q.hom
  rw [← Category.assoc (extendUnitHom φ (regular R))
      ((extendScalars φ).map p).hom _, ← hn, Category.assoc,
    extendUnitHom_extendHom, ← Category.assoc, extendUnitHom_extendHom]
  exact h

end CategoryTheory.Mod

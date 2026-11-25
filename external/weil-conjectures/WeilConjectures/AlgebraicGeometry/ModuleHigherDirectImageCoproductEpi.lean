/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.CategoryTheory.Limits.Shapes.Products
import WeilConjectures.AlgebraicGeometry.QcqsCohomologyDirectSum
import WeilConjectures.AlgebraicGeometry.HigherDirectImageAffineCohomologyPresentation
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-! # Surjectivity of ordinary higher direct image on coproducts

Source: Stacks Project, Tag 07TB, with Tags 01FF and 01FE.
(blueprint: lem-pc-module-higher-direct-image-coproduct-epi).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open Classical in
private theorem addHom_eq_of_directSum_surjective
    {S : Type u} [Ring S] {J : Type u} {L : J → Type u}
    [∀ j, AddCommGroup (L j)] [∀ j, Module S (L j)]
    {P : Type u} [AddCommGroup P] [Module S P]
    (φ : ∀ j, L j →ₗ[S] P)
    (hs : Function.Surjective (DirectSum.toModule S J P φ))
    {Q : Type u} [AddCommGroup Q] (a b : P →+ Q)
    (h : ∀ j x, a (φ j x) = b (φ j x)) : a = b := by
  classical
  ext x
  obtain ⟨z, rfl⟩ := hs x
  induction z using DirectSum.induction_on with
  | zero => simp only [map_zero]
  | of j y =>
      rw [← DirectSum.lof_eq_of S J L j y, DirectSum.toModule_lof]
      exact h j y
  | add z w hz hw => simp only [map_add, hz, hw]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
-- The restriction and derived-functor comparisons require substantial elaboration.
/-- Ordinary higher direct image sends a module-sheaf coproduct cofan to a jointly
surjective family. No quasi-coherence hypothesis is needed.
Source: Stacks Project, Tag 07TB, proof using cohomology on inverse images of affine
opens, with Tags 01FF and 01FE.
(blueprint: lem-pc-module-higher-direct-image-coproduct-epi).

Proof: Restriction to an open subspace preserves coproducts of module sheaves, since
it is left adjoint to direct image for the open immersion. For an affine open V of Y,
its inverse image under f is quasi-compact and quasi-separated. The cohomology
coproduct theorem on this inverse image says that every class with coefficients in
the restricted coproduct is a finite sum of classes coming from its summands.
This theorem applies to all module sheaves, not only quasi-coherent ones.
Compute the ordinary higher direct images with injective resolutions. Their
cohomology presheaves have values H^p(f^{-1}(V), -); the canonical maps from these
presheaves to the higher direct image sheaves induce isomorphisms after
sheafification, naturally in the coefficient module. Thus every germ in the target
higher direct image is represented, on some affine neighborhood, by a cohomology
class on its inverse image. Express this class as a finite sum as above. Each
summand class maps to a section of the corresponding higher direct image; their
finite sum lifts the original germ through the sheaf coproduct comparison.
Consequently the comparison is surjective on every stalk. A map of module sheaves
surjective on stalks is epic, proving the assertion. For an empty family, its
coproduct is zero and additivity makes the target zero; for p = 0 this is the same
argument with ordinary sections. Naturality of the resolution comparison identifies
the maps from summands with the displayed rightDerived functor maps. -/
theorem moduleHigherDirectImage_coproduct_epi
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (I : Type u) (M : I → SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (N : SheafOfModules.{u} (moduleRings X.toRingedSpace)) (ι : ∀ i, M i ⟶ N)
    (hc : IsColimit (Cofan.mk N ι)) (p : ℕ) :
    Epi (Sigma.desc (fun i ↦
      ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p).map (ι i))) := by
  classical
  obtain ⟨c, hdetect⟩ := higherDirectImage_affine_cohomology_presentation f p
  let R := (RingedSpace.moduleDirectImage f.toLRSHom.toShHom).rightDerived p
  constructor
  intro Q a b hab
  apply hdetect N Q a b
  intro V hV
  let U := f ⁻¹ᵁ V
  let T := Scheme.Modules.restrictFunctor U.ι
  let H := RingedSpace.moduleCohomology U.toScheme.toRingedSpace p
  have : CompactSpace U :=
    (isCompact_iff_compactSpace).mp (f.isCompact_preimage hV.isCompact)
  have : QuasiSeparatedSpace U :=
    (isQuasiSeparated_iff_quasiSeparatedSpace _ U.2).mp
      (f.isQuasiSeparated_preimage hV.isQuasiSeparated)
  have hT : IsColimit (Cofan.mk (T.obj N) (fun i ↦ T.map (ι i))) :=
    isColimitMapCoconeCofanMkEquiv T M ι (isColimitOfPreserves T hc)
  have hsurj := (Scheme.moduleCohomology_directSum_bijective U.toScheme I
    (fun i ↦ T.obj (M i)) (T.obj N) (fun i ↦ T.map (ι i)) hT p).2
  let A := (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map a
  let B := (c V).app N ≫ (RingedSpace.openModuleSections Y.toRingedSpace V).map b
  have hi (i : I) : R.map (ι i) ≫ a = R.map (ι i) ≫ b := by
    have h := congrArg (fun k ↦ Sigma.ι (fun i ↦ R.obj (M i)) i ≫ k) hab
    change Sigma.ι (fun i ↦ R.obj (M i)) i ≫
      (Sigma.desc (fun i ↦ R.map (ι i)) ≫ a) =
        Sigma.ι (fun i ↦ R.obj (M i)) i ≫
          (Sigma.desc (fun i ↦ R.map (ι i)) ≫ b) at h
    simpa only [colimit.ι_desc_assoc, Cofan.mk_ι_app] using h
  have hAB (i : I) :
      (forget₂ _ AddCommGrpCat).map (H.map (T.map (ι i))) ≫ A =
        (forget₂ _ AddCommGrpCat).map (H.map (T.map (ι i))) ≫ B := by
    have hn := (c V).naturality (ι i)
    change (forget₂ _ AddCommGrpCat).map (H.map (T.map (ι i))) ≫
        (c V).app N = (c V).app (M i) ≫
          (RingedSpace.openModuleSections Y.toRingedSpace V).map (R.map (ι i)) at hn
    dsimp only [A, B]
    rw [← Category.assoc, hn, Category.assoc, ← Functor.map_comp, hi,
      Functor.map_comp, ← Category.assoc, ← hn, Category.assoc]
  apply AddCommGrpCat.hom_ext
  apply addHom_eq_of_directSum_surjective
    (fun i ↦ (H.map (T.map (ι i))).hom) hsurj
  intro i y
  exact ConcreteCategory.congr_hom (hAB i) y

end AlgebraicGeometry

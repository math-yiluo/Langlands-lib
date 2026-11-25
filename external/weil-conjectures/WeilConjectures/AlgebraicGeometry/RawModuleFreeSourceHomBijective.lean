/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.ModuleAbelianCoefficientComparison


public import WeilConjectures.AlgebraicGeometry.RawModuleScalarPullbackComparison

/-! # Underived free-source scalar comparison

Source: Stacks Project, Tags 03FD, 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).
-/

@[expose] public section

universe u
open CategoryTheory Limits Opposite
open scoped CategoryTheory.Functor AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

-- Sheafification, the free abelian group adjunction, and Yoneda identify Hom with sections.
private noncomputable def abelianSections (S : Scheme.{u}) (U : S.Etale)
    (N : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    (RawModuleScalarComparison.freeAbelian S U ⟶ N) ≃ N.obj.obj (op U) :=
  ((sheafificationAdjunction S.smallEtaleTopology AddCommGrpCat.{u + 1}).homEquiv
    (uliftYoneda.{u + 1}.obj U ⋙ AddCommGrpCat.free) N).trans
      ((((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv)

private lemma abelianSections_comp (S : Scheme.{u}) (U : S.Etale)
    {N N' : Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (a : RawModuleScalarComparison.freeAbelian S U ⟶ N) (b : N ⟶ N') :
    abelianSections S U N' (a ≫ b) = b.hom.app (op U) (abelianSections S U N a) := by
  dsimp only [abelianSections, Equiv.trans_apply]
  rw [Adjunction.homEquiv_naturality_right]
  change uliftYonedaEquiv
    (((AddCommGrpCat.adj).whiskerRight S.Etaleᵒᵖ).homEquiv _ _
      (((sheafificationAdjunction _ _).homEquiv _ _ a) ≫ b.hom)) = _
  rw [Adjunction.homEquiv_naturality_right]
  rfl

private lemma freeMap_sections (Λ : Type (u + 1)) [CommRing Λ]
    (S : Scheme.{u}) (U : S.Etale)
    (N : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (g : (freeSheaf Λ S).obj U ⟶ N) :
    abelianSections S U ((moduleAbelianForget Λ S).obj N)
      (RawModuleScalarComparison.freeMap Λ S U ≫
        (moduleAbelianForget Λ S).map g) = freeSheafHomEquiv Λ U N g := by
  rw [abelianSections_comp]
  have hg := freeSheafHomEquiv_comp Λ U (𝟙 ((freeSheaf Λ S).obj U)) g
  change (g.hom.app (op U)).hom
    (abelianSections S U ((moduleAbelianForget Λ S).obj
      ((freeSheaf Λ S).obj U))
      ((abelianSections S U ((moduleAbelianForget Λ S).obj
        ((freeSheaf Λ S).obj U))).symm
      (freeSheafHomEquiv Λ U ((freeSheaf Λ S).obj U) (𝟙 _)))) = _
  rw [Equiv.apply_symm_apply]
  simpa using hg.symm

-- The canonical adjunction mate satisfies its defining unit equation.
private lemma scalar_unit (Λ : Type (u + 1)) [CommRing Λ]
    {X S : Scheme.{u}} (f : X ⟶ S)
    (G : Sheaf S.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((moduleAbelianForget Λ S).obj G) ≫
      (lowerStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.pullback Λ f G) =
      (moduleAbelianForget Λ S).map
        ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).unit.app G) := by
  change (upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv _ _
    ((moduleAbelianUpperStarComparison Λ f).app G) = _
  exact Equiv.apply_symm_apply _ _

/-- The explicit generator comparison is bijective on underived Hom.
Source: Stacks Project, Tag 03FD, equality of section complexes; Tags 03D3 and 03D7.
(blueprint: lem-sbc-raw-module-free-source-hom-bijective).

Proof: Apply the inverse-image/direct-image adjunction in modules and in
abelian sheaves. Then apply sheafification adjunction, the free-module/free-group
adjunction and Yoneda. Both Hom groups become the same section group of f_*M
at U. The two units commute with the Kan-extension/sheafification comparison
pullbackIso. The definition of freeMap sends the identity generator to the
identity generator, so f ↦ a ≫ forget(f) becomes the identity on that section
group. It is therefore bijective. This works for every M, independently of
injectivity, in degree zero, over the zero ring, and on empty schemes. -/
theorem rawModuleFreeSourceHom_bijective
    (Λ : Type (u + 1)) [CommRing Λ] {X S : Scheme.{u}} (f : X ⟶ S)
    (U : S.Etale) (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Function.Bijective (fun g :
        (upperStar (ModuleCat.{u + 1} Λ) f).obj ((freeSheaf Λ S).obj U) ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
          (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f ((freeSheaf Λ S).obj U)) ≫
          (moduleAbelianForget Λ X).map g) := by
  let L := (freeSheaf Λ S).obj U
  -- Both equivalences have the same section group as codomain.
  let em := ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv L M).trans
    (freeSheafHomEquiv Λ U ((lowerStar (ModuleCat.{u + 1} Λ) f).obj M))
  let ea := ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).homEquiv
    (RawModuleScalarComparison.freeAbelian S U)
    ((moduleAbelianForget Λ X).obj M)).trans
      (abelianSections S U ((lowerStar AddCommGrpCat.{u + 1} f).obj
        ((moduleAbelianForget Λ X).obj M)))
  let e := em.trans ea.symm
  have he : (fun g : (upperStar (ModuleCat.{u + 1} Λ) f).obj L ⟶ M ↦
      ((upperStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.freeMap Λ S U) ≫
        RawModuleScalarComparison.pullback Λ f L) ≫
        (moduleAbelianForget Λ X).map g) = e := by
    funext g
    apply ea.injective
    change ea _ = ea (ea.symm (em g))
    rw [Equiv.apply_symm_apply]
    dsimp only [ea, em, Equiv.trans_apply]
    rw [Category.assoc, Adjunction.homEquiv_naturality_left]
    rw [Adjunction.homEquiv_apply, Functor.map_comp]
    rw [← Category.assoc
      ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} f).unit.app
        ((moduleAbelianForget Λ S).obj L))
      ((lowerStar AddCommGrpCat.{u + 1} f).map
        (RawModuleScalarComparison.pullback Λ f L))]
    rw [scalar_unit Λ f L]
    change abelianSections S U ((moduleAbelianForget Λ S).obj
      ((lowerStar (ModuleCat.{u + 1} Λ) f).obj M))
      (RawModuleScalarComparison.freeMap Λ S U ≫
        (moduleAbelianForget Λ S).map
          ((upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).homEquiv L M g)) = _
    exact freeMap_sections Λ S U _ _
  change Function.Bijective (fun g : (upperStar (ModuleCat.{u + 1} Λ) f).obj L ⟶ M ↦ _)
  rw [he]
  exact e.bijective

end AlgebraicGeometry.Etale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtaleGeometricStalk
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.ColimitFunctor
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleLocallyConstantSheaf
import Mathlib.CategoryTheory.Limits.Connected
import WeilConjectures.AlgebraicGeometry.ProEtale.ProEtaleSheafificationGeometricStalk

/-!
# Stalks of constant module sheaves on the pro-etale site

The additive germ map is specified by the actual sheafification unit and the
coprojection at `(Y,y)`. Scalar compatibility uses the constant-ring germ map;
thus bijectivity expresses an isomorphism over the original coefficient ring.

## References

* Bhatt--Scholze, The pro-etale topology for schemes, Sections 6.5 and 6.8
* Stacks Project, Tags 0F6B, 0F6C, 00Y8(3), and 03CY
* Stacks Project, before Tag 0F6B
* Stacks Project, Tags 00Y8(3), 03CY
* Bhatt--Scholze, Sections 6.5, 6.8
* Stacks Project, Tags 0F6B, 0F6C, 00Y8(3), 03CY
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

variable {Y : Scheme.{u}} {Ω : Type u} [Field Ω] [IsAlgClosed Ω]

/-- The pointed neighbourhood `(Y,y)`. -/
noncomputable def proEtaleConstantGermNeighbourhood (y : Spec (.of Ω) ⟶ Y) :
    ProEtaleGeometricNeighbourhood y :=
  StructuredArrow.mk (Y := ProEt.mk (𝟙 Y)) (Over.homMk y (Category.comp_id y))

/-- The coefficient homomorphism sending a scalar to its constant germ at `(Y,y)`. -/
noncomputable def proEtaleConstantRingGerm (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] :
    ULift.{u + 1, u} A →+* proEtaleGeometricStalkRing y
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) :=
  ((colimit.ι (proEtaleGeometricStalkRingDiagram y
    ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
      (CommRingCat.of (ULift.{u + 1, u} A))))
        (op (proEtaleConstantGermNeighbourhood y))).hom).comp
    (((CategoryTheory.toSheafify (ProEt.topology Y)
      ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A)))).app
        (op (ProEt.mk (𝟙 Y)))).hom)

/-- The canonical additive germ map: sheafify a constant section, then take its
class in the pointed-neighbourhood colimit at `(Y,y)`. -/
noncomputable def proEtaleConstantModuleGerm (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    M →+ proEtaleGeometricModuleStalk y
      ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))) (proEtaleConstantModuleSheaf Y A M) :=
  ((colimit.ι
    ((proEtaleGeometricNeighbourhoodForget y).op ⋙
      (proEtaleConstantModuleSheaf Y A M).val.presheaf)
        (op (proEtaleConstantGermNeighbourhood y))).hom).comp
    (((CategoryTheory.toSheafify (ProEt.topology Y)
      (proEtaleConstantModulePresheaf Y.ProEt A M).presheaf).app
        (op (ProEt.mk (𝟙 Y)))).hom)

/-- The canonical constant-section map is an isomorphism of coefficient modules:
it is an additive bijection and respects scalars via the constant-ring germ map.
Consequently its stalk is finite whenever the constant module is finite. -/
theorem proEtaleConstantModuleGerm_bijective (y : Spec (.of Ω) ⟶ Y)
    (A : Type u) [CommRing A] (M : ModuleCat.{u + 1} (ULift.{u + 1, u} A)) :
    Function.Bijective (proEtaleConstantModuleGerm y A M) ∧
      (∀ (a : ULift.{u + 1, u} A) (m : M),
        proEtaleConstantModuleGerm y A M (a • m) =
          proEtaleConstantRingGerm y A a • proEtaleConstantModuleGerm y A M m) ∧
      (Finite M → Finite (proEtaleGeometricModuleStalk y
        ((constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
          (CommRingCat.of (ULift.{u + 1, u} A))) (proEtaleConstantModuleSheaf Y A M))) := by
  let P := proEtaleConstantModulePresheaf Y.ProEt A M
  let D := (proEtaleGeometricNeighbourhoodForget y).op ⋙ P.presheaf
  have hD : D = (Functor.const (ProEtaleGeometricNeighbourhood y)ᵒᵖ).obj
      (AddCommGrpCat.of M) := by
    rfl
  have hconn : IsConnected (ProEtaleGeometricNeighbourhood y)ᵒᵖ := by infer_instance
  have hc : IsColimit (constCocone (ProEtaleGeometricNeighbourhood y)ᵒᵖ
      (AddCommGrpCat.of M)) := isColimitConstCocone _ _
  have hi : IsIso (colimit.ι D (op (proEtaleConstantGermNeighbourhood y))) := by
    rw [hD]
    let e := colimit.isoColimitCocone ⟨_, hc⟩
    have hfac : colimit.ι ((Functor.const (ProEtaleGeometricNeighbourhood y)ᵒᵖ).obj
        (AddCommGrpCat.of M)) (op (proEtaleConstantGermNeighbourhood y)) ≫ e.hom = 𝟙 _ := by
      simp [e, colimit.isoColimitCocone_ι_hom]
    exact IsIso.of_isIso_fac_right hfac
  let α := CategoryTheory.toSheafify (ProEt.topology Y) P.presheaf
  let f := colim.map (Functor.whiskerLeft (proEtaleGeometricNeighbourhoodForget y).op α)
  have hf : IsIso f := (proEtaleGeometricStalk_sheafification y P.presheaf).1
  have hg : AddCommGrpCat.ofHom (proEtaleConstantModuleGerm y A M) =
      colimit.ι D (op (proEtaleConstantGermNeighbourhood y)) ≫ f := by
    rw [colimit.ι_map]
    rfl
  have hgi : IsIso (AddCommGrpCat.ofHom (proEtaleConstantModuleGerm y A M)) := by
    rw [hg]
    infer_instance
  have hbij : Function.Bijective (proEtaleConstantModuleGerm y A M) := by
    exact ConcreteCategory.bijective_of_isIso (AddCommGrpCat.ofHom
      (proEtaleConstantModuleGerm y A M))
  refine ⟨hbij, ?_, ?_⟩
  · intro a m
    let F := proEtaleConstantModuleSheaf Y A M
    let O := (constantSheaf (ProEt.topology Y) CommRingCat.{u + 1}).obj
        (CommRingCat.of (ULift.{u + 1, u} A))
    let R := proEtaleGeometricStalkRingDiagram y O
    let P := proEtaleConstantModulePresheaf Y.ProEt A M
    let α := Functor.whiskerRight (CategoryTheory.toSheafify (ProEt.topology Y)
        ((Functor.const Y.ProEtᵒᵖ).obj (CommRingCat.of (ULift.{u + 1, u} A))))
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})
    have := (proEtaleConstantRingUnit_locallyBijective Y A).1
    have := (proEtaleConstantRingUnit_locallyBijective Y A).2
    let SM := (PresheafOfModules.pushforward₀ (proEtaleGeometricNeighbourhoodForget y)
        (O.obj ⋙ forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj F.val
    let cR := colimit.isColimit R
    let cM := colimit.isColimit SM.presheaf
    let η := (PresheafOfModules.sheafificationAdjunction.{u + 1}
      (R := (sheafCompose (ProEt.topology Y)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj O) α).unit.app P
    have hη := LinearMap.map_smul (η.app (op (ProEt.mk (𝟙 Y)))).hom
      (a : ULift.{u + 1, u} A) m
    have hsmul := PresheafOfModules.ModuleColimit.smul_eq cR cM
        (U := op (proEtaleConstantGermNeighbourhood y))
        (α.app (op (ProEt.mk (𝟙 Y))) a)
        (show (SM.obj (op (proEtaleConstantGermNeighbourhood y))) from
          (η.app (op (ProEt.mk (𝟙 Y)))).hom m)
    change ((colimit.ι SM.presheaf (op (proEtaleConstantGermNeighbourhood y))).hom
        (((η.app (op (ProEt.mk (𝟙 Y)))).hom (a • m)))) = _
    rw [hη]
    exact hsmul.symm
  · intro hM
    exact Finite.of_surjective (proEtaleConstantModuleGerm y A M) hbij.2

end AlgebraicGeometry.Scheme

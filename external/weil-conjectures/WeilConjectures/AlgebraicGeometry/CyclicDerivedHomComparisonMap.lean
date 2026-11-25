/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import WeilConjectures.AlgebraicGeometry.EtaleOpenCohomologyComparison
public import WeilConjectures.SixFunctors.Etale.Derived.UpperLowerStarCoherence

/-! # The explicit free-representable cohomology comparison map
Source: Stacks Project, Tag 03Q8; the free-sheaf adjunction.
(blueprint: def-sbc-abelian-representable-cohomology-map). -/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open scoped AlgebraicGeometry.Etale
namespace AlgebraicGeometry.Etale

/-- The free abelian sheaf on an étale representable. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable abbrev abelianRepresentable (X : Scheme.{u}) :=
  AlgebraicGeometry.etaleOpenFreeSheaf X

/-- The free/sheafification/Yoneda adjunction, evaluated at an étale object. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable def abelianRepresentableHomEquiv {X : Scheme.{u}} (W : X.Etale)
    (G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    ((abelianRepresentable X).obj W ⟶ G) ≃ G.obj.obj (op W) :=
  (EtaleOpenComparison.sectionsEquiv X.smallEtaleTopology W G).toEquiv

/-- The final object of the small étale site. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable abbrev abelianEtaleFinal (T : Scheme.{u}) : T.Etale :=
  MorphismProperty.Over.mk ⊤ (𝟙 T) (inferInstance : AlgebraicGeometry.Etale (𝟙 T))

/-- The universal section of `h^* Z[W]`, restricted to `Y ×_X W`, as a morphism
from the constant integer sheaf. Constructed from the adjunction unit. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable def abelianRepresentableGenerator {X Y : Scheme.{u}}
    (h : Y ⟶ X) (W : X.Etale) :
    (constantSheaf (pullback h W.hom).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift ℤ)) ⟶
      (upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)) := by
  let A := (upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)
  let B := (MorphismProperty.Over.pullback @AlgebraicGeometry.Etale ⊤ h).obj W
  let R : Y.Etale := MorphismProperty.Over.mk ⊤ (pullback.fst h W.hom) inferInstance
  let i : R ≅ B := MorphismProperty.Over.isoMk (pullbackSymmetry h W.hom) (by
    dsimp [B, R]
    simp)
  let s := abelianRepresentableHomEquiv W _
    ((upperStarLowerStarAdjunction AddCommGrpCat.{u + 1} h).unit.app
      ((abelianRepresentable X).obj W))
  let T := pullback h W.hom
  let r := pullback.fst h W.hom
  let t := abelianEtaleFinal T
  let O := (MorphismProperty.Over.map ⊤ (inferInstance : AlgebraicGeometry.Etale r)).obj t
  let j : O ≅ R := MorphismProperty.Over.isoMk (Iso.refl _) (by
    dsimp [O, t, abelianEtaleFinal, R, r]
    exact (Category.id_comp _).symm)
  let z := A.obj.map j.hom.op (A.obj.map i.hom.op s)
  let z' := ((upperStarIsoLocalizationRestriction AddCommGrpCat.{u + 1} r
    inferInstance).inv.app A).hom.app (op t) z
  exact Ext.addEquiv₀ ((Sheaf.H.equiv₀ _
    (MorphismProperty.Over.mkIdTerminal @AlgebraicGeometry.Etale T)).symm z')

/-- Bounded below derived Hom between single objects is Ext. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable def abelianPlusHomExtEquiv {X : Scheme.{u}}
    (A F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj A ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) ≃+ Ext A F q := by
  let C := Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}
  let I : DerivedCategory.Plus C ⥤ DerivedCategory C := DerivedCategory.Plus.ι
  let M := (DerivedCategory.Plus.singleFunctor C 0).obj A
  let N := (DerivedCategory.Plus.singleFunctor C 0).obj F
  let E : (M ⟶ N⟦(q : ℤ)⟧) ≃+ (I.obj M ⟶ I.obj (N⟦(q : ℤ)⟧)) :=
    InducedCategory.homAddEquiv
  let i : I.obj (N⟦(q : ℤ)⟧) ≅ ((DerivedCategory.singleFunctor C 0).obj F)⟦(q : ℤ)⟧ :=
    (I.commShiftIso (q : ℤ)).app N
  let j : I.obj M ≅ (DerivedCategory.singleFunctor C 0).obj A :=
    (DerivedCategory.Plus.singleFunctorιIso C 0).app A
  let E' : (I.obj M ⟶ I.obj (N⟦(q : ℤ)⟧)) ≃+
      ((DerivedCategory.singleFunctor C 0).obj A ⟶
        ((DerivedCategory.singleFunctor C 0).obj F)⟦(q : ℤ)⟧) :=
    AddEquiv.mk' (j.homCongr i) (by
      intro f g
      simp only [Iso.homCongr_apply, Preadditive.comp_add, Preadditive.add_comp])
  exact (E.trans E').trans (Ext.homAddEquiv (X := A) (Y := F) (n := q)).symm

/-- Pull back a derived class and evaluate it at the universal section. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable def abelianRepresentableCohomologyMap {X Y : Scheme.{u}}
    (h : Y ⟶ X) (F : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1})
    (q : ℕ) (W : X.Etale) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)⟦(q : ℤ)⟧) →+
      Sheaf.H ((upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).obj F) q :=
  ((Ext.mk₀ (abelianRepresentableGenerator h W)).precomp _ (zero_add q)).comp
    (((upperStar AddCommGrpCat.{u + 1} (pullback.fst h W.hom)).mapExtAddHom _ _ q).comp
      (abelianPlusHomExtEquiv _ F q).toAddMonoidHom)

/-- The canonical comparison with constant cyclic coefficients. 
(blueprint: def-sbc-abelian-representable-cohomology-map)
-/
noncomputable def cyclicRepresentableCohomologyMap {X Y : Scheme.{u}}
    (h : Y ⟶ X) (e q : ℕ) (W : X.Etale) :
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((upperStar AddCommGrpCat.{u + 1} h).obj ((abelianRepresentable X).obj W)) ⟶
      ((DerivedCategory.Plus.singleFunctor _ 0).obj (Y.constantZMod e))⟦(q : ℤ)⟧) →+
      Sheaf.H ((pullback h W.hom).constantZMod e) q :=
  (Sheaf.H.map ((Scheme.upperStarConstantSheafIso AddCommGrpCat.{u + 1}
    (pullback.fst h W.hom)).app (AddCommGrpCat.of (ULift (ZMod e)))).hom q).comp
      (abelianRepresentableCohomologyMap h (Y.constantZMod e) q W)

end AlgebraicGeometry.Etale

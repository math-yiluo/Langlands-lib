/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import WeilConjectures.Mathlib.CategoryTheory.Limits.Shapes.Products
public import WeilConjectures.CategoryTheory.DerivedCategory.DegreewiseLimits
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-!
# Coproducts in the derived category

Let `C` be an abelian category with K-injective resolutions. We show that a coproduct of
cochain complexes (which is computed degreewise) is also a coproduct in the derived category
(`DerivedCategory.isColimitCofanMkQObj`). No exactness of coproducts is needed: for a K-injective
complex `I`, morphisms `Q.obj X ⟶ Q.obj I` in the derived category are homotopy classes of
morphisms `X ⟶ I` (`DerivedCategory.homEquivOfIsKInjective`), and homotopy classes of morphisms
out of a coproduct are families of homotopy classes of morphisms out of the summands
(`HomotopyCategory.isColimitCofanQuotient`).

## Main definitions and statements

- `DerivedCategory.homEquivOfIsKInjective`: morphisms `Q.obj K ⟶ Q.obj L` for `L` K-injective
  are morphisms in the homotopy category.
- `DerivedCategory.isColimitCofanMkQObj`: coproducts of cochain complexes are coproducts in the
  derived category.
- `DerivedCategory.preservesColimitsOfShape_Q`, `DerivedCategory.hasColimitsOfShape_discrete`:
  `Q` preserves coproducts and `D(C)` has coproducts of shape `J` if `C` does.
- `CategoryTheory.Functor.preservesColimitsOfShape_mapDerivedCategory`: the functor induced on
  derived categories by an exact functor preserving coproducts preserves coproducts.
-/

@[expose] public section

open CategoryTheory Limits Category

namespace DerivedCategory

variable {C : Type*} [Category* C] [Abelian C] [HasDerivedCategory C]

/-- For a K-injective complex `L`, morphisms `Q.obj K ⟶ Q.obj L` in the derived category
identify with morphisms in the homotopy category. -/
noncomputable def homEquivOfIsKInjective (K L : CochainComplex C ℤ) [L.IsKInjective] :
    ((HomotopyCategory.quotient C (.up ℤ)).obj K ⟶ (HomotopyCategory.quotient C (.up ℤ)).obj L) ≃
      (Q.obj K ⟶ Q.obj L) :=
  (Equiv.ofBijective _ (CochainComplex.IsKInjective.Qh_map_bijective _ L)).trans
    (Iso.homCongr ((quotientCompQhIso C).app K) ((quotientCompQhIso C).app L))

@[simp]
lemma homEquivOfIsKInjective_quotient_map {K L : CochainComplex C ℤ} [L.IsKInjective]
    (f : K ⟶ L) :
    homEquivOfIsKInjective K L ((HomotopyCategory.quotient C (.up ℤ)).map f) = Q.map f := by
  simp [homEquivOfIsKInjective]

lemma homEquivOfIsKInjective_quotient_map_comp {K K' L : CochainComplex C ℤ} [L.IsKInjective]
    (u : K' ⟶ K) (g : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) :
    homEquivOfIsKInjective K' L ((HomotopyCategory.quotient C (.up ℤ)).map u ≫ g) =
      Q.map u ≫ homEquivOfIsKInjective K L g := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  rw [← Functor.map_comp, homEquivOfIsKInjective_quotient_map,
    homEquivOfIsKInjective_quotient_map, Functor.map_comp]

lemma homEquivOfIsKInjective_comp_quotient_map {K L L' : CochainComplex C ℤ} [L.IsKInjective]
    [L'.IsKInjective] (g : (HomotopyCategory.quotient C (.up ℤ)).obj K ⟶
      (HomotopyCategory.quotient C (.up ℤ)).obj L) (v : L ⟶ L') :
    homEquivOfIsKInjective K L' (g ≫ (HomotopyCategory.quotient C (.up ℤ)).map v) =
      homEquivOfIsKInjective K L g ≫ Q.map v := by
  obtain ⟨g, rfl⟩ := (HomotopyCategory.quotient C (.up ℤ)).map_surjective g
  rw [← Functor.map_comp, homEquivOfIsKInjective_quotient_map,
    homEquivOfIsKInjective_quotient_map, Functor.map_comp]

variable [Abelian.HasKInjectiveResolutions C]

/-- If `C` has K-injective resolutions, a coproduct of cochain complexes (which is computed
degreewise) is also a coproduct in the derived category. -/
noncomputable def isColimitCofanMkQObj {β : Type*} {K : β → CochainComplex C ℤ} {s : Cofan K}
    (hs : IsColimit s) : IsColimit (Cofan.mk (Q.obj s.pt) fun j ↦ Q.map (s.inj j)) := by
  refine Cofan.IsColimit.ofBijective _ fun Y ↦ ?_
  obtain ⟨I, _, ⟨e⟩⟩ := exists_iso_Q_obj_of_isKInjective Y
  refine Cofan.bijective_of_iso _ e.symm ?_
  have h := Cofan.IsColimit.bijective (HomotopyCategory.isColimitCofanQuotient hs)
    ((HomotopyCategory.quotient C (.up ℤ)).obj I)
  have : (fun (g : Q.obj s.pt ⟶ Q.obj I) (j : β) ↦ Q.map (s.inj j) ≫ g) =
      (Equiv.piCongrRight fun j ↦ homEquivOfIsKInjective (K j) I) ∘
        (fun g (j : β) ↦ (HomotopyCategory.quotient C (.up ℤ)).map (s.inj j) ≫ g) ∘
          (homEquivOfIsKInjective s.pt I).symm := by
    ext g j
    simp [homEquivOfIsKInjective_quotient_map_comp]
  exact this ▸ (Equiv.bijective _).comp (h.comp (Equiv.bijective _))


/-- The localization functor `Q : CochainComplex C ℤ ⥤ D(C)` preserves coproducts: a
coproduct of complexes is a coproduct in the derived category. -/
instance preservesColimitsOfShape_Q (J : Type*) :
    PreservesColimitsOfShape (Discrete J) (Q (C := C)) := by
  have (K : J → CochainComplex C ℤ) : PreservesColimit (Discrete.functor K) Q :=
    ⟨fun {s} hs ↦ ⟨(isColimitMapCoconeCofanMkEquiv Q K (Cofan.inj (f := K) s)).symm
      (isColimitCofanMkQObj (s := Cofan.mk s.pt (Cofan.inj (f := K) s)) hs)⟩⟩
  exact preservesColimitsOfShape_of_discrete Q

/-- Every family of objects of `D(C)` is isomorphic to the image under `Q` of a family of
complexes. -/
noncomputable def discreteFunctorIsoQ {J : Type*} (F : Discrete J ⥤ DerivedCategory C) :
    F ≅ Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q :=
  Discrete.natIso fun j ↦ (Q.objObjPreimageIso (F.obj j)).symm

/-- The derived category has coproducts of shape `J` if `C` does. -/
instance hasColimitsOfShape_discrete (J : Type*) [HasColimitsOfShape (Discrete J) C] :
    HasColimitsOfShape (Discrete J) (DerivedCategory C) where
  has_colimit F := by
    have : HasColimit (Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q) :=
      ⟨⟨⟨_, isColimitOfPreserves Q (colimit.isColimit _)⟩⟩⟩
    exact hasColimit_of_iso (discreteFunctorIsoQ F)

/-- A functor `G` out of the derived category preserves coproducts of shape `J` as soon as
`Q ⋙ G` does. -/
lemma preservesColimitsOfShape_of_Q_comp {E : Type*} [Category* E] (J : Type*)
    [HasColimitsOfShape (Discrete J) C] (G : DerivedCategory C ⥤ E)
    [PreservesColimitsOfShape (Discrete J) (Q ⋙ G)] :
    PreservesColimitsOfShape (Discrete J) G where
  preservesColimit {F} := by
    have : PreservesColimit (Discrete.functor (fun j ↦ Q.objPreimage (F.obj ⟨j⟩)) ⋙ Q) G :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves Q (colimit.isColimit _))
        (isColimitOfPreserves (Q ⋙ G) (colimit.isColimit _))
    exact preservesColimit_of_iso_diagram G (discreteFunctorIsoQ F).symm

end DerivedCategory

namespace CategoryTheory.Functor

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [Abelian.HasKInjectiveResolutions C]
  [Abelian.HasKInjectiveResolutions D] (F : C ⥤ D) [F.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The functor induced on cochain complexes by a functor preserving coproducts of shape `J`
preserves coproducts of shape `J`. -/
instance preservesColimitsOfShape_mapHomologicalComplex {ι : Type*} (c : ComplexShape ι)
    (J : Type*) [HasColimitsOfShape (Discrete J) C] [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) (F.mapHomologicalComplex c) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun i ↦
    preservesColimitsOfShape_of_natIso
      (NatIso.ofComponents (fun K ↦ Iso.refl _) (by simp) : HomologicalComplex.eval C c i ⋙ F ≅
        F.mapHomologicalComplex c ⋙ HomologicalComplex.eval D c i)

/-- The functor induced on derived categories by an exact functor preserving coproducts of
shape `J` preserves coproducts of shape `J`. -/
instance preservesColimitsOfShape_mapDerivedCategory (J : Type*)
    [HasColimitsOfShape (Discrete J) C] [HasColimitsOfShape (Discrete J) D]
    [PreservesColimitsOfShape (Discrete J) F] :
    PreservesColimitsOfShape (Discrete J) F.mapDerivedCategory := by
  have : PreservesColimitsOfShape (Discrete J) (DerivedCategory.Q ⋙ F.mapDerivedCategory) :=
    preservesColimitsOfShape_of_natIso F.mapDerivedCategoryFactors.symm
  exact DerivedCategory.preservesColimitsOfShape_of_Q_comp J _

end CategoryTheory.Functor

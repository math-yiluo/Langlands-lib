import Langlands.Cohomology.HyperextScalarExtension
import Langlands.Cohomology.HyperextEdgeMapLinear
import Langlands.Cohomology.HyperextEdgeMap
import Langlands.Cohomology.DerivedExactComposition
import Langlands.Cohomology.HyperextDegeneration.Proof

/-!
# Edge maps and extension of scalars

Let `F : C ⥤ D` be an exact functor of abelian categories, `K` an object of the derived
category of `C`, `W` an object of `C` and `W₀` the complex `W` placed in degree `0`. The edge
map `HyperextDegeneration.edgeMap K W n : Hom(K, W₀⟦n⟧) → Hom(H^{-n} K, W)` of the Library
applies the cohomology functor. This module proves that edge maps commute with the comparison
maps of `Langlands.Cohomology.HyperextScalarExtension`.

* `edgeMap_abutmentMap`: the edge map of `abutmentMap F K W n f` is `cohomologyHomMap F K W (-n)`
  applied to the edge map of `f`.
* `edgeMapLinearMap_comp_abutmentBaseChangeMap`, `edgeMap_abutmentBaseChangeMap`: for `F`
  semilinear along `R → S`, the edge maps over `R` and `S` intertwine the base-change maps
  `abutmentBaseChangeMap` and `cohomologyHomBaseChangeMap`.
* `abutmentBaseChangeMap_eq_degeneration`: under the hypotheses of the hyperext degeneration
  over `R` and over `S`, the first base-change map is the second one transported along the
  degeneration isomorphisms; `abutmentBaseChangeMap_bijective_iff`, `_injective_iff` and
  `_surjective_iff` follow, and `abutmentBaseChangeLinearEquiv` is the first map as an
  `S`-linear equivalence when the second one is bijective (an explicit hypothesis).
* `smoothEdgeMapLinearMap_comp_abutmentBaseChangeMap`,
  `smoothAbutmentBaseChangeMap_bijective_iff`, `smoothAbutmentBaseChangeLinearEquiv`: the case
  of extension of scalars of smooth representations along a flat `R → S`.
* Auxiliary lemmas: compatibility of the Library's `exactDerivedHomologyIso F` with the shift
  isomorphisms of cohomology (`exactDerivedHomologyIso_shiftIso`,
  `exactDerivedHomologyIso_shiftMap`) and with single complexes
  (`exactDerivedHomologyIso_singleFunctor`).

No base-change map is claimed to be injective, surjective or bijective. See
`HyperextScalarEdgeMap.md`.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

namespace Langlands.Cohomology

namespace HyperextScalarExtension

universe w uR uS uG uC vC uD vD t t' s s'

section Complexes

variable {C : Type uC} [Category.{vC} C] [Abelian C]
variable {D : Type uD} [Category.{vD} D] [Abelian D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

set_option backward.isDefEq.respectTransparency false in
/-- `mapHomologicalComplexHomologyIso F`, the comparison `H^a(F L) ≅ F(H^a L)` for complexes,
is compatible with the shift isomorphisms `H^a(L⟦n⟧) ≅ H^{a'} L` (`n + a = a'`) and with the
commutation `F(L⟦n⟧) ≅ (F L)⟦n⟧` of `F.mapHomologicalComplex` with the shift. -/
@[reassoc]
lemma mapHomologicalComplexHomologyIso_shiftIso (n a a' : ℤ) (ha' : n + a = a')
    (L : CochainComplex C ℤ) :
    HomologicalComplex.homologyMap
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L) a ≫
      ((HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) 0).shiftIso n a a' ha').hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
      (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) a').hom.app L =
    (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) a).hom.app (L⟦n⟧) ≫
      F.map (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
        n a a' ha').hom.app L) := by
  have key : (HomologicalComplex.shortComplexFunctor D (ComplexShape.up ℤ) a).map
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L) ≫
      (CochainComplex.shiftShortComplexFunctorIso D n a a' ha').hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) =
      F.mapShortComplex.map
        ((CochainComplex.shiftShortComplexFunctorIso C n a a' ha').hom.app L) := by
    ext <;> simp [Functor.map_units_smul, HomologicalComplex.XIsoOfEq, eqToHom_map] <;>
      exact Category.id_comp _
  have h := ShortComplex.mapHomologyIso_hom_naturality
    ((CochainComplex.shiftShortComplexFunctorIso C n a a' ha').hom.app L) F
  simp only [Functor.shiftIso, Functor.ShiftSequence.shiftIso,
    CochainComplex.ShiftSequence.shiftIso_hom_app]
  change ShortComplex.homologyMap ((HomologicalComplex.shortComplexFunctor D
      (ComplexShape.up ℤ) a).map
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L)) ≫ _ ≫ _ = _
  rw [← Category.assoc, ← ShortComplex.homologyMap_comp, key]
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- On a complex `W₀` concentrated in degree `0`, the comparison
`H^0(F(W₀)) ≅ F(H^0(W₀))` of `mapHomologicalComplexHomologyIso F` agrees, after the
identifications `H^0(W₀) ≅ W` and `H^0((F W)₀) ≅ F W`, with the isomorphism
`F(W₀) ≅ (F W)₀` of `F.mapCochainComplexSingleFunctor 0`. -/
lemma homologyMap_mapCochainComplexSingleFunctor (W : C) :
    HomologicalComplex.homologyMap ((F.mapCochainComplexSingleFunctor 0).hom.app W) 0 ≫
      (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 (F.obj W)).hom =
    (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) 0).hom.app
        ((CochainComplex.singleFunctor C 0).obj W) ≫
      F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 W).hom := by
  rw [← cancel_epi (HomologicalComplex.homologyπ _ 0)]
  have hR := DerivedPlus.homologyπ_mapHomologyIso_hom_assoc F
    (((CochainComplex.singleFunctor C 0).obj W).sc 0)
    (F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) 0 W).hom)
  have hc := ShortComplex.mapCyclesIso_hom_iCycles_assoc
    (((CochainComplex.singleFunctor C 0).obj W).sc 0) F
    (F.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 W).hom)
  rw [HomologicalComplex.homologyπ_naturality_assoc]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom]
  erw [HomologicalComplex.cyclesMap_i_assoc]
  erw [hR]
  rw [← F.map_comp]
  erw [HomologicalComplex.homologyπ_singleObjHomologySelfIso_hom]
  rw [HomologicalComplex.singleObjCyclesSelfIso_hom, F.map_comp]
  erw [hc]
  simp only [Functor.mapCochainComplexSingleFunctor,
    HomologicalComplex.singleMapHomologicalComplex_hom_app_self, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rfl

end Complexes

section Derived

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{s} C]

/-- In the derived category, the shift isomorphism `H^a(Q(M)⟦n⟧) ≅ H^{a'}(Q M)` composed
with the commutation `Q(M⟦n⟧) ≅ Q(M)⟦n⟧` of the localization functor `Q` with the shift is the
shift isomorphism of complexes, transported along `DerivedCategory.homologyFunctorFactors`. -/
lemma homologyFunctor_map_commShiftIso_shiftIso (n a a' : ℤ) (ha' : n + a = a')
    (M : CochainComplex C ℤ) :
    (DerivedCategory.homologyFunctor C a).map
        ((DerivedCategory.Q.commShiftIso n).hom.app M) ≫
      ((DerivedCategory.homologyFunctor C 0).shiftIso n a a' ha').hom.app
        (DerivedCategory.Q.obj M) =
    (DerivedCategory.homologyFunctorFactors C a).hom.app (M⟦n⟧) ≫
      ((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
        n a a' ha').hom.app M ≫
      (DerivedCategory.homologyFunctorFactors C a').inv.app M := by
  have h := DerivedCategory.shiftMap_homologyFunctor_map_Q (𝟙 (M⟦n⟧)) a a' ha'
  simp only [Functor.shiftMap, ShiftedHom.map, CategoryTheory.Functor.map_id,
    Category.id_comp] at h
  exact h

end Derived


section Exact

variable {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The component of `exactDerivedHomologyIso F q` at `Q L`, written as the composite of its
four constituent isomorphisms. -/
lemma exactDerivedHomologyIso_hom_app_Q_obj' (q : ℤ) (L : CochainComplex C ℤ) :
    (exactDerivedHomologyIso F q).hom.app (DerivedCategory.Q.obj L) =
      (DerivedCategory.homologyFunctor D q).map (F.mapDerivedCategoryFactors.hom.app L) ≫
        (DerivedCategory.homologyFunctorFactors D q).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) ≫
        (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) q).hom.app L ≫
        F.map ((DerivedCategory.homologyFunctorFactors C q).inv.app L) := by
  rw [exactDerivedHomologyIso_hom_app_Q_obj]
  dsimp [exactDerivedHomologyIsoOnComplexes]
  simp only [Category.id_comp, Category.comp_id]

/-- On `Q L`, the commutation of `F.mapDerivedCategory` with the shift is the commutation of
`F.mapHomologicalComplex` with the shift, transported along `F.mapDerivedCategoryFactors` and
the commutation of `Q` with the shift. -/
lemma mapDerivedCategory_commShiftIso_hom_app_Q_obj (n : ℤ) (L : CochainComplex C ℤ) :
    F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app L) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj L) ≫
      (F.mapDerivedCategoryFactors.hom.app L)⟦n⟧' =
    F.mapDerivedCategoryFactors.hom.app (L⟦n⟧) ≫
      DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
        L) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) := by
  have h := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom n L
  simp only [Functor.commShiftIso_comp_hom_app, Category.assoc] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
/-- `exactDerivedHomologyIso_shiftIso` on objects of the form `Q L`. -/
lemma exactDerivedHomologyIso_shiftIso_Q_obj (n a a' : ℤ) (ha' : n + a = a')
    (L : CochainComplex C ℤ) :
    (DerivedCategory.homologyFunctor D a).map
        ((F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj L)) ≫
      ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
      (exactDerivedHomologyIso F a').hom.app (DerivedCategory.Q.obj L) =
    (exactDerivedHomologyIso F a).hom.app ((DerivedCategory.Q.obj L)⟦n⟧) ≫
      F.map (((DerivedCategory.homologyFunctor C 0).shiftIso n a a' ha').hom.app
        (DerivedCategory.Q.obj L)) := by
  have h3 : F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app L) ≫
      (F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj L) =
    (F.mapDerivedCategoryFactors.hom.app (L⟦n⟧) ≫
      DerivedCategory.Q.map (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app
        L) ≫
      (DerivedCategory.Q.commShiftIso n).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≫
      (F.mapDerivedCategoryFactors.inv.app L)⟦n⟧' :=
    (Iso.eq_comp_inv ((shiftFunctor (DerivedCategory D) n).mapIso
      (F.mapDerivedCategoryFactors.app L))).2
      ((Category.assoc _ _ _).trans (mapDerivedCategory_commShiftIso_hom_app_Q_obj F n L))
  have hn : (DerivedCategory.homologyFunctor D a).map
        ((F.mapDerivedCategoryFactors.inv.app L)⟦n⟧') ≫
      ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
      (DerivedCategory.homologyFunctor D a').map (F.mapDerivedCategoryFactors.hom.app L) =
    ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
        (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) := by
    have h := Functor.shiftIso_hom_naturality (DerivedCategory.homologyFunctor D 0) n a a' ha'
      (F.mapDerivedCategoryFactors.inv.app L)
    have h2 : (DerivedCategory.homologyFunctor D a').map (F.mapDerivedCategoryFactors.inv.app L) ≫
        (DerivedCategory.homologyFunctor D a').map (F.mapDerivedCategoryFactors.hom.app L) =
          𝟙 _ := by
      rw [← Functor.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
    calc _ = (((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
          (DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) ≫
          (DerivedCategory.homologyFunctor D a').map (F.mapDerivedCategoryFactors.inv.app L)) ≫
          (DerivedCategory.homologyFunctor D a').map (F.mapDerivedCategoryFactors.hom.app L) :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) h)
      _ = _ := (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h2).trans (Category.comp_id _))
  have hRHS : (DerivedCategory.homologyFunctor D a).map
        (F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app L)) ≫
      (exactDerivedHomologyIso F a).hom.app ((DerivedCategory.Q.obj L)⟦n⟧) ≫
      F.map (((DerivedCategory.homologyFunctor C 0).shiftIso n a a' ha').hom.app
        (DerivedCategory.Q.obj L)) =
    (DerivedCategory.homologyFunctor D a).map (F.mapDerivedCategoryFactors.hom.app (L⟦n⟧)) ≫
      (DerivedCategory.homologyFunctorFactors D a).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (L⟦n⟧)) ≫
      (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) a).hom.app (L⟦n⟧) ≫
      F.map (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
        n a a' ha').hom.app L) ≫
      F.map ((DerivedCategory.homologyFunctorFactors C a').inv.app L) := by
    erw [exactDerivedHomologyIso_naturality_assoc]
    rw [← F.map_comp]
    erw [homologyFunctor_map_commShiftIso_shiftIso]
    erw [exactDerivedHomologyIso_hom_app_Q_obj' F a (L⟦n⟧)]
    simp only [Functor.map_comp, Category.assoc]
    rw [← F.map_comp_assoc ((DerivedCategory.homologyFunctorFactors C a).inv.app (L⟦n⟧)),
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  have hLHS : (DerivedCategory.homologyFunctor D a).map
        (F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app L)) ≫
      (DerivedCategory.homologyFunctor D a).map
        ((F.mapDerivedCategory.commShiftIso n).hom.app (DerivedCategory.Q.obj L)) ≫
      ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj L)) ≫
      (exactDerivedHomologyIso F a').hom.app (DerivedCategory.Q.obj L) =
    (DerivedCategory.homologyFunctor D a).map (F.mapDerivedCategoryFactors.hom.app (L⟦n⟧)) ≫
      (DerivedCategory.homologyFunctorFactors D a).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj (L⟦n⟧)) ≫
      (mapHomologicalComplexHomologyIso F (ComplexShape.up ℤ) a).hom.app (L⟦n⟧) ≫
      F.map (((HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) 0).shiftIso
        n a a' ha').hom.app L) ≫
      F.map ((DerivedCategory.homologyFunctorFactors C a').inv.app L) := by
    rw [← Functor.map_comp_assoc, h3, exactDerivedHomologyIso_hom_app_Q_obj' F a']
    simp only [Functor.map_comp, Category.assoc]
    rw [reassoc_of% hn]
    rw [← Category.assoc ((DerivedCategory.homologyFunctor D a).map
        ((DerivedCategory.Q.commShiftIso n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L))),
      homologyFunctor_map_commShiftIso_shiftIso n a a' ha'
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L)]
    simp only [Category.assoc, Iso.inv_hom_id_app_assoc]
    erw [DerivedCategory.homologyFunctorFactors_hom_naturality_assoc
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso n).hom.app L) a]
    erw [mapHomologicalComplexHomologyIso_shiftIso_assoc]
    rfl
  rw [← cancel_epi ((DerivedCategory.homologyFunctor D a).map
      (F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso n).hom.app L))), hRHS]
  exact hLHS

/-- `exactDerivedHomologyIso F`, the comparison `H^a(F Y) ≅ F(H^a Y)` in the derived category,
is compatible with the shift isomorphisms `H^a(Y⟦n⟧) ≅ H^{a'} Y` (`n + a = a'`) and with the
commutation of `F.mapDerivedCategory` with the shift. -/
lemma exactDerivedHomologyIso_shiftIso (n a a' : ℤ) (ha' : n + a = a') (Y : DerivedCategory C) :
    (DerivedCategory.homologyFunctor D a).map ((F.mapDerivedCategory.commShiftIso n).hom.app Y) ≫
      ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom.app
        (F.mapDerivedCategory.obj Y) ≫
      (exactDerivedHomologyIso F a').hom.app Y =
    (exactDerivedHomologyIso F a).hom.app (Y⟦n⟧) ≫
      F.map (((DerivedCategory.homologyFunctor C 0).shiftIso n a a' ha').hom.app Y) := by
  let τ : shiftFunctor (DerivedCategory C) n ⋙ F.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor D a ⟶ DerivedCategory.homologyFunctor C a' ⋙ F :=
    Functor.whiskerRight (F.mapDerivedCategory.commShiftIso n).hom
        (DerivedCategory.homologyFunctor D a) ≫
      Functor.whiskerLeft F.mapDerivedCategory
        ((DerivedCategory.homologyFunctor D 0).shiftIso n a a' ha').hom ≫
      (exactDerivedHomologyIso F a').hom
  let τ' : shiftFunctor (DerivedCategory C) n ⋙ F.mapDerivedCategory ⋙
      DerivedCategory.homologyFunctor D a ⟶ DerivedCategory.homologyFunctor C a' ⋙ F :=
    Functor.whiskerLeft (shiftFunctor (DerivedCategory C) n) (exactDerivedHomologyIso F a).hom ≫
      Functor.whiskerRight ((DerivedCategory.homologyFunctor C 0).shiftIso n a a' ha').hom F
  have hτ : τ = τ' :=
    Localization.natTrans_ext DerivedCategory.Q
      (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
      (fun L => exactDerivedHomologyIso_shiftIso_Q_obj F n a a' ha' L)
  exact congrArg (fun φ => φ.app Y) hτ

set_option backward.isDefEq.respectTransparency false in
/-- For a shifted morphism `f : X ⟶ Y⟦n⟧`, the map `H^a X → H^{a'} Y` induced by the image
`f.map F.mapDerivedCategory` is the image under `F` of the map induced by `f`, through
`exactDerivedHomologyIso F`. -/
lemma exactDerivedHomologyIso_shiftMap {X Y : DerivedCategory C} {n : ℤ}
    (f : ShiftedHom X Y n) (a a' : ℤ) (ha' : n + a = a') :
    (DerivedCategory.homologyFunctor D 0).shiftMap (f.map F.mapDerivedCategory) a a' ha' ≫
      (exactDerivedHomologyIso F a').hom.app Y =
    (exactDerivedHomologyIso F a).hom.app X ≫
      F.map ((DerivedCategory.homologyFunctor C 0).shiftMap f a a' ha') := by
  have hB := exactDerivedHomologyIso_shiftIso F n a a' ha' Y
  have hN := exactDerivedHomologyIso_naturality F a f
  simp only [Functor.shiftMap, ShiftedHom.map, Functor.map_comp, Category.assoc]
  erw [hB]
  rw [← Category.assoc]
  erw [hN]
  rw [Category.assoc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- In degree `0`, on a single complex `W₀`, `exactDerivedHomologyIso F 0` agrees with the
isomorphism `F(W₀) ≅ (F W)₀` of `F.mapDerivedCategorySingleFunctor 0`, after the
identifications `H^0(W₀) ≅ W` of `DerivedCategory.singleFunctorCompHomologyFunctorIso`. -/
lemma exactDerivedHomologyIso_singleFunctor (W : C) :
    (DerivedCategory.homologyFunctor D 0).map ((F.mapDerivedCategorySingleFunctor 0).hom.app W) ≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso D 0).hom.app (F.obj W) =
    (exactDerivedHomologyIso F 0).hom.app ((DerivedCategory.singleFunctor C 0).obj W) ≫
      F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso C 0).hom.app W) := by
  have hσ : (F.mapDerivedCategorySingleFunctor 0).hom.app W =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C 0).obj W) ≫
        DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app W) :=
    (Iso.inv_comp_eq (F.mapDerivedCategoryFactors.app
      ((CochainComplex.singleFunctor C 0).obj W))).1
      (F.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app W)
  have hC := HyperextEdgeMap.homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso W
  have hD := (Iso.inv_comp_eq ((DerivedCategory.homologyFunctorFactors D 0).app
      ((CochainComplex.singleFunctor D 0).obj (F.obj W)))).1
    (HyperextEdgeMap.homologyFunctorFactors_inv_app_singleFunctorCompHomologyFunctorIso (F.obj W))
  have hnat := DerivedCategory.homologyFunctorFactors_hom_naturality
    ((F.mapCochainComplexSingleFunctor 0).hom.app W) 0
  erw [exactDerivedHomologyIso_hom_app_Q_obj' F 0 ((CochainComplex.singleFunctor C 0).obj W)]
  rw [hσ, Functor.map_comp, Category.assoc]
  erw [hD]
  rw [← Category.assoc ((DerivedCategory.homologyFunctor D 0).map
    (DerivedCategory.Q.map ((F.mapCochainComplexSingleFunctor 0).hom.app W)))]
  erw [hnat]
  simp only [Category.assoc]
  erw [homologyMap_mapCochainComplexSingleFunctor F W]
  rw [← F.map_comp]
  erw [hC]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- **Compatibility of the edge maps with an exact functor.** For an exact functor `F` and
`f : K ⟶ W₀⟦n⟧`, the edge map of `abutmentMap F K W n f : F K ⟶ (F W)₀⟦n⟧` is
`cohomologyHomMap F K W (-n)` applied to the edge map of `f`, that is, the composite of
`H^{-n}(F K) ≅ F(H^{-n} K)` with `F` applied to the edge map of `f`. -/
theorem edgeMap_abutmentMap (K : DerivedCategory C) (W : C) (n : ℤ)
    (f : ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap (F.mapDerivedCategory.obj K) (F.obj W) n
        (abutmentMap F K W n f) =
      cohomologyHomMap F K W (-n) (HyperextDegeneration.edgeMap K W n f) := by
  rw [abutmentMap_apply, cohomologyHomMap_apply]
  simp only [HyperextDegeneration.edgeMap]
  rw [Functor.shiftMap_comp, Category.assoc]
  erw [exactDerivedHomologyIso_singleFunctor F W]
  rw [← Category.assoc, exactDerivedHomologyIso_shiftMap F f (-n) 0, Category.assoc,
    ← F.map_comp]

/-- If `H^i K` vanishes, then so does `H^i (F K)`. -/
theorem mapDerivedCategory_homology_isZero (K : DerivedCategory C) {i : ℤ}
    (hK : IsZero ((DerivedCategory.homologyFunctor C i).obj K)) :
    IsZero ((DerivedCategory.homologyFunctor D i).obj (F.mapDerivedCategory.obj K)) :=
  (F.map_isZero hK).of_iso ((exactDerivedHomologyIso F i).app K)

end Exact

section Semilinear

variable {R : Type uR} [CommRing R] {S : Type uS} [CommRing S] [Algebra R S]
variable {C : Type uC} [Category.{vC} C] [Abelian C] [Linear R C] [HasDerivedCategory.{s} C]
variable {D : Type uD} [Category.{vD} D] [Abelian D] [Linear S D] [HasDerivedCategory.{s'} D]
variable (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- **Compatibility of the edge maps with extension of scalars.** For an exact functor `F`
that is semilinear along `R → S`, as `S`-linear maps
`S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(H^{-n}(F K), F W)`: the edge map over `S` after
`abutmentBaseChangeMap` equals `cohomologyHomBaseChangeMap` after the base change to `S` of
the edge map over `R`. -/
theorem edgeMapLinearMap_comp_abutmentBaseChangeMap (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (W : C) (n : ℤ) :
    HyperextAbutment.edgeMapLinearMap S (F.mapDerivedCategory.obj K) (F.obj W) n ∘ₗ
        abutmentBaseChangeMap F hF K W n =
      cohomologyHomBaseChangeMap F hF K W (-n) ∘ₗ
        (HyperextAbutment.edgeMapLinearMap R K W n).baseChange S := by
  refine LinearMap.ext fun z => ?_
  induction z using TensorProduct.inductionOn with
  | tmul x f =>
    rw [LinearMap.comp_apply, LinearMap.comp_apply, abutmentBaseChangeMap_tmul,
      LinearMap.baseChange_tmul, cohomologyHomBaseChangeMap_tmul, LinearMap.map_smul,
      HyperextAbutment.edgeMapLinearMap_apply, HyperextAbutment.edgeMapLinearMap_apply,
      edgeMap_abutmentMap]
  | add a b ha hb => rw [LinearMap.map_add, LinearMap.map_add, ha, hb]

/-- `edgeMapLinearMap_comp_abutmentBaseChangeMap`, applied to an element. -/
theorem edgeMap_abutmentBaseChangeMap (hF : IsSemilinear R S F) (K : DerivedCategory C) (W : C)
    (n : ℤ) (x : S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    HyperextDegeneration.edgeMap (F.mapDerivedCategory.obj K) (F.obj W) n
        (abutmentBaseChangeMap F hF K W n x) =
      cohomologyHomBaseChangeMap F hF K W (-n)
        ((HyperextAbutment.edgeMapLinearMap R K W n).baseChange S x) :=
  LinearMap.congr_fun (edgeMapLinearMap_comp_abutmentBaseChangeMap F hF K W n) x

variable [HasExt.{t} C] [HasExt.{t'} D]

/-- When the edge maps over `R` and over `S` are bijective (the hyperext degeneration of the
Library, under its hypotheses for `K`, `W` and for `F K`, `F W`), the base-change map on
`Hom(K, W₀⟦n⟧)` is the base-change map on `Hom(H^{-n} K, W)` transported along the two
degeneration isomorphisms. -/
theorem abutmentBaseChangeMap_eq_degeneration (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) :
    abutmentBaseChangeMap F hF K W n =
      (HyperextAbutment.degenerationLinearEquiv S (hyperextDegenerationStatement_proof D)
          (F.mapDerivedCategory.obj K) b
          (fun i hi => mapDerivedCategory_homology_isZero F K (hK i hi)) (F.obj W) hW'
          n).symm.toLinearMap ∘ₗ
        cohomologyHomBaseChangeMap F hF K W (-n) ∘ₗ
        ((HyperextAbutment.degenerationLinearEquiv R (hyperextDegenerationStatement_proof C) K b
          hK W hW n).baseChange R S _ _).toLinearMap :=
  LinearMap.ext fun x => (LinearEquiv.eq_symm_apply _).2
    (edgeMap_abutmentBaseChangeMap F hF K W n x)

/-- Under the degeneration hypotheses, the base-change map on `Hom(K, W₀⟦n⟧)` is bijective if
and only if the base-change map on `Hom(H^{-n} K, W)` is. -/
theorem abutmentBaseChangeMap_bijective_iff (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) :
    Function.Bijective (abutmentBaseChangeMap F hF K W n) ↔
      Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n)) := by
  rw [abutmentBaseChangeMap_eq_degeneration F hF K b hK W hW hW' n]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_bijective,
    EquivLike.bijective_comp]

/-- Under the degeneration hypotheses, the base-change map on `Hom(K, W₀⟦n⟧)` is injective if
and only if the base-change map on `Hom(H^{-n} K, W)` is. -/
theorem abutmentBaseChangeMap_injective_iff (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) :
    Function.Injective (abutmentBaseChangeMap F hF K W n) ↔
      Function.Injective (cohomologyHomBaseChangeMap F hF K W (-n)) := by
  rw [abutmentBaseChangeMap_eq_degeneration F hF K b hK W hW hW' n]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_injective,
    EquivLike.injective_comp]

/-- Under the degeneration hypotheses, the base-change map on `Hom(K, W₀⟦n⟧)` is surjective if
and only if the base-change map on `Hom(H^{-n} K, W)` is. -/
theorem abutmentBaseChangeMap_surjective_iff (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) :
    Function.Surjective (abutmentBaseChangeMap F hF K W n) ↔
      Function.Surjective (cohomologyHomBaseChangeMap F hF K W (-n)) := by
  rw [abutmentBaseChangeMap_eq_degeneration F hF K b hK W hW hW' n]
  simp only [LinearMap.coe_comp, LinearEquiv.coe_coe, EquivLike.comp_surjective,
    EquivLike.surjective_comp]

/-- Under the degeneration hypotheses, and if the base-change map on `Hom(H^{-n} K, W)` is
bijective (the hypothesis `h`), the base-change map
`S ⊗[R] Hom(K, W₀⟦n⟧) → Hom(F K, (F W)₀⟦n⟧)` as an `S`-linear equivalence. -/
def abutmentBaseChangeLinearEquiv (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n))) :
    S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n ≃ₗ[S]
      ShiftedHom (F.mapDerivedCategory.obj K)
        ((DerivedCategory.singleFunctor D 0).obj (F.obj W)) n :=
  LinearEquiv.ofBijective (abutmentBaseChangeMap F hF K W n)
    ((abutmentBaseChangeMap_bijective_iff F hF K b hK W hW hW' n).2 h)

/-- The underlying map of `abutmentBaseChangeLinearEquiv` is `abutmentBaseChangeMap`. -/
@[simp]
theorem abutmentBaseChangeLinearEquiv_apply (hF : IsSemilinear R S F)
    (K : DerivedCategory C) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor C i).obj K)) (W : C)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor C k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'}
        ((DerivedCategory.homologyFunctor D k).obj (F.mapDerivedCategory.obj K)) (F.obj W) i))
    (n : ℤ) (h : Function.Bijective (cohomologyHomBaseChangeMap F hF K W (-n)))
    (x : S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor C 0).obj W) n) :
    abutmentBaseChangeLinearEquiv F hF K b hK W hW hW' n h x =
      abutmentBaseChangeMap F hF K W n x :=
  rfl

end Semilinear

section Smooth

variable (R : Type uR) [CommRing R] (S : Type uS) [CommRing S] [Algebra R S] [Module.Flat R S]
  (G : Type uG) [Group G] [TopologicalSpace G]
variable [HasDerivedCategory.{s} (SmoothRep.{uR, uG, w} R G)]
  [HasDerivedCategory.{s'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- `edgeMapLinearMap_comp_abutmentBaseChangeMap` for extension of scalars of smooth
representations along a flat `R → S`. -/
theorem smoothEdgeMapLinearMap_comp_abutmentBaseChangeMap
    (K : DerivedCategory (SmoothRep.{uR, uG, w} R G)) (W : SmoothRep.{uR, uG, w} R G) (n : ℤ) :
    HyperextAbutment.edgeMapLinearMap S
        ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).mapDerivedCategory.obj K)
        ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).obj W) n ∘ₗ
        smoothAbutmentBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W n =
      smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n) ∘ₗ
        (HyperextAbutment.edgeMapLinearMap R K W n).baseChange S :=
  edgeMapLinearMap_comp_abutmentBaseChangeMap (smoothRepExtendScalars.{w, uR, uS, uG} R S G)
    (smoothRepExtendScalars_isSemilinear.{w, uR, uS, uG} R S G) K W n

variable [HasExt.{t} (SmoothRep.{uR, uG, w} R G)] [HasExt.{t'} (SmoothRep.{uS, uG, max uS w} S G)]

/-- `abutmentBaseChangeMap_bijective_iff` for extension of scalars of smooth representations
along a flat `R → S`. -/
theorem smoothAbutmentBaseChangeMap_bijective_iff
    (K : DerivedCategory (SmoothRep.{uR, uG, w} R G)) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (W : SmoothRep.{uR, uG, w} R G)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((DerivedCategory.homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).obj W) i))
    (n : ℤ) :
    Function.Bijective (smoothAbutmentBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W n) ↔
      Function.Bijective
        (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n)) :=
  abutmentBaseChangeMap_bijective_iff (smoothRepExtendScalars.{w, uR, uS, uG} R S G)
    (smoothRepExtendScalars_isSemilinear.{w, uR, uS, uG} R S G) K b hK W hW hW' n

/-- `abutmentBaseChangeLinearEquiv` for extension of scalars of smooth representations along a
flat `R → S`: under the degeneration hypotheses and if `smoothCohomologyHomBaseChangeMap` is
bijective (the hypothesis `h`), `smoothAbutmentBaseChangeMap` as an `S`-linear equivalence. -/
def smoothAbutmentBaseChangeLinearEquiv
    (K : DerivedCategory (SmoothRep.{uR, uG, w} R G)) (b : ℤ)
    (hK : ∀ i : ℤ, b < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj K))
    (W : SmoothRep.{uR, uG, w} R G)
    (hW : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t} ((DerivedCategory.homologyFunctor _ k).obj K) W i))
    (hW' : ∀ (k : ℤ) (i : ℕ), 0 < i →
      Subsingleton (Abelian.Ext.{t'} ((DerivedCategory.homologyFunctor _ k).obj
          ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).mapDerivedCategory.obj K))
        ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).obj W) i))
    (n : ℤ)
    (h : Function.Bijective
      (smoothCohomologyHomBaseChangeMap.{w, uR, uS, uG, s, s'} R S G K W (-n))) :
    S ⊗[R] ShiftedHom K ((DerivedCategory.singleFunctor _ 0).obj W) n ≃ₗ[S]
      ShiftedHom ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).mapDerivedCategory.obj K)
        ((DerivedCategory.singleFunctor _ 0).obj
          ((smoothRepExtendScalars.{w, uR, uS, uG} R S G).obj W)) n :=
  abutmentBaseChangeLinearEquiv (smoothRepExtendScalars.{w, uR, uS, uG} R S G)
    (smoothRepExtendScalars_isSemilinear.{w, uR, uS, uG} R S G) K b hK W hW hW' n h

end Smooth

end HyperextScalarExtension

end Langlands.Cohomology

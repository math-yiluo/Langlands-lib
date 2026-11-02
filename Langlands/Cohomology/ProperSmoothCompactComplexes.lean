import Langlands.Sheaf.Equivariant.ProperSmoothCompactSections
import Langlands.Cohomology.LocalCompactComparison
import Langlands.Cohomology.DerivedExactComposition
import Langlands.Representation.Category.ExactInclusion

/-! # Proper spatial maps on compact-section complexes of smooth sheaves -/

noncomputable section

namespace Langlands.Cohomology.ProperSmoothCompactComplexes

open CategoryTheory CategoryTheory.Limits HomologicalComplex
open Langlands.Sheaf.Equivariant

universe u t

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]
  {I : Type t} (c : ComplexShape I)

/-- The original equivariant sheaf complex, forgetting only local smoothness. -/
def underlyingComplex :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤
      HomologicalComplex (TopologicalSheaf G X (ModuleCat.{u} R)) c :=
  (Langlands.Sheaf.Equivariant.smoothInclusion R G X).mapHomologicalComplex c

/-- Full compact sections of each smooth sheaf, in the smooth category. -/
def compactComplex :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤
      HomologicalComplex (Langlands.SmoothRep.{u, u, u} R G) c :=
  (smoothSheafCompactSections R G X).mapHomologicalComplex c

/-- Forgetting smoothness of the terms retains all compact sections of the
underlying sheaves, with their original actions and differentials. -/
def compactComplexToRepIso :
    compactComplex R G X c ⋙
        (Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex c ≅
      underlyingComplex R G X c ⋙ EquivariantSections.compactComplex R G X c :=
  Functor.mapHomologicalComplexCompIso (smoothSheafCompactSectionsToRepIso R G X) c

/-- Global sections of the original underlying sheaf complex. -/
def globalComplex :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤
      HomologicalComplex (Rep.{u} R G) c :=
  underlyingComplex R G X c ⋙ EquivariantSections.globalComplex R G X c

/-- The original compact-support submodule inclusions in every degree. -/
def forgetSupportComplex :
    compactComplex R G X c ⋙
        (Langlands.SmoothRep.toRep (R := R) (G := G)).mapHomologicalComplex c ⟶
      globalComplex R G X c :=
  (compactComplexToRepIso R G X c).hom ≫
    Functor.whiskerLeft (underlyingComplex R G X c)
      (EquivariantSections.forgetSupportComplex R G X c)

/-- Homology formed in the existing abelian category of smooth representations. -/
def compactHomology (i : I) :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤
      Langlands.SmoothRep.{u, u, u} R G :=
  compactComplex R G X c ⋙ homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i

/-- The exact inclusion identifies smooth-category homology with the actual
algebraic homology of the full compact-section complex. -/
def compactHomologyToRepIso (i : I) :
    compactHomology R G X c i ⋙ Langlands.SmoothRep.toRep ≅
      underlyingComplex R G X c ⋙ EquivariantSections.compactHomology R G X c i :=
  (Functor.isoWhiskerLeft (compactComplex R G X c)
    (DerivedPlus.mapHomologicalComplexHomologyIso
      (Langlands.SmoothRep.toRep (R := R) (G := G)) c i)).symm ≪≫
    Functor.isoWhiskerRight (compactComplexToRepIso R G X c)
      (homologyFunctor (Rep.{u} R G) c i)

/-- The comparison first uses exactness of the inclusion and then the actual
identity-on-sections compact-complex comparison. -/
theorem compactHomologyToRepIso_hom_app (i : I)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (compactHomologyToRepIso R G X c i).hom.app F =
      (DerivedPlus.mapHomologicalComplexHomologyIso
        (Langlands.SmoothRep.toRep (R := R) (G := G)) c i).inv.app
          ((compactComplex R G X c).obj F) ≫
        (homologyFunctor (Rep.{u} R G) c i).map
          ((compactComplexToRepIso R G X c).hom.app F) := rfl

/-- Homology of the original global-section complex. -/
def globalHomology (i : I) :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤ Rep.{u} R G :=
  globalComplex R G X c ⋙ homologyFunctor (Rep.{u} R G) c i

/-- Forget compact support after identifying the actual underlying homology. -/
def forgetSupportHomology (i : I) :
    compactHomology R G X c i ⋙ Langlands.SmoothRep.toRep ⟶
      globalHomology R G X c i :=
  (compactHomologyToRepIso R G X c i).hom ≫
    Functor.whiskerLeft (underlyingComplex R G X c)
      (EquivariantSections.forgetSupportHomology R G X c i)

set_option backward.isDefEq.respectTransparency false in
/-- Support forgetting is the homology of the actual chain inclusion, after
the exact-inclusion homology comparison. -/
theorem forgetSupportHomology_app (i : I)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (forgetSupportHomology R G X c i).app F =
      (DerivedPlus.mapHomologicalComplexHomologyIso
        (Langlands.SmoothRep.toRep (R := R) (G := G)) c i).inv.app
          ((compactComplex R G X c).obj F) ≫
        (homologyFunctor (Rep.{u} R G) c i).map
          ((forgetSupportComplex R G X c).app F) := by
  simp only [forgetSupportHomology, NatTrans.comp_app, Functor.whiskerLeft_app,
    compactHomologyToRepIso_hom_app, forgetSupportComplex,
    EquivariantSections.forgetSupportHomology, Functor.whiskerRight_app,
    Functor.comp_obj, Functor.map_comp, Category.assoc]

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G Y] [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Apply the constructed smooth direct image to terms, differentials and maps. -/
def directImageComplex :
    HomologicalComplex (SmoothTopologicalSheaf R G X) c ⥤
      HomologicalComplex (SmoothTopologicalSheaf R G Y) c :=
  (SmoothDirectImage.functor (R := R) f hf).mapHomologicalComplex c

/-- The actual smooth identity comparison, applied to every term. -/
def directImageIdIso :
    𝟭 (HomologicalComplex (SmoothTopologicalSheaf R G X) c) ≅
      directImageComplex (R := R) c (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) := by
  letI : (SmoothDirectImage.functor (R := R) (ContinuousMap.id X)
      (fun (_ : G) (_ : X) => rfl)).Additive := SmoothDirectImage.additive _ _
  exact (Functor.mapHomologicalComplexIdIso (SmoothTopologicalSheaf R G X) c).symm ≪≫
    NatIso.mapHomologicalComplex (SmoothDirectImage.idIso (R := R) (G := G) (X := X)) c

/-- Iterated smooth direct image has its original lax comparison termwise. -/
def directImageCompMap
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) :
    directImageComplex (R := R) c f hf ⋙ directImageComplex c g hg ⟶
      directImageComplex c (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) :=
  NatTrans.mapHomologicalComplex (SmoothDirectImage.compMap f hf g hg) c

/-- The termwise actual inclusion into ordinary equivariant direct image. -/
def directImageInclusionComplex :
    directImageComplex c f hf ⋙ underlyingComplex R G Y c ⟶
      underlyingComplex R G X c ⋙ ProperCompactComplexes.directImageComplex c f hf :=
  NatTrans.mapHomologicalComplex (SmoothDirectImage.inclusion f hf) c

/-- The proper compact-section natural transformation is a genuine smooth
chain map on arbitrary supplied complexes of smooth sheaves. -/
def properComplex (hp : IsProperMap f) :
    directImageComplex c f hf ⋙ compactComplex R G Y c ⟶ compactComplex R G X c :=
  NatTrans.mapHomologicalComplex (ProperSmoothCompactSections.natTrans f hf hp) c

/-- The degreewise morphism is exactly the previously constructed smooth
compact-section pullback. -/
@[simp]
theorem properComplex_f (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I) :
    ((properComplex c f hf hp).app F).f i =
      (ProperSmoothCompactSections.natTrans f hf hp).app (F.X i) := rfl

/-- The map acts on each original section by forgetting the local smoothness
witness on the smooth direct image. -/
@[simp]
theorem properComplex_apply (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I)
    (s : (smoothSheafCompactSections R G Y).obj
      ((SmoothDirectImage.functor f hf).obj (F.X i))) :
    (Langlands.SmoothRep.hom (((properComplex c f hf hp).app F).f i) s).val =
      s.val.val := rfl

/-- Inclusion into the full direct image followed by the ordinary global-section
identification, applied in every degree. -/
def globalComplexMap :
    directImageComplex c f hf ⋙ globalComplex R G Y c ⟶ globalComplex R G X c :=
  Functor.whiskerRight (directImageInclusionComplex c f hf)
      (EquivariantSections.globalComplex R G Y c) ≫
    Functor.whiskerLeft (underlyingComplex R G X c)
      (ProperCompactComplexes.globalComplexIso c f hf).hom

/-- The underlying smooth chain map is the actual ordinary compact pullback
of the smooth-image subsheaf inclusion. -/
theorem properComplex_comparison (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (Langlands.SmoothRep.toRep.mapHomologicalComplex c).map
          ((properComplex c f hf hp).app F) ≫
        (compactComplexToRepIso R G X c).hom.app F =
      (compactComplexToRepIso R G Y c).hom.app ((directImageComplex c f hf).obj F) ≫
        LocalCompactComparison.pullbackComplex f hf hp
          ((directImageInclusionComplex c f hf).app F) := by
  ext i s
  rfl

/-- Proper smooth spatial pullback commutes with forgetting compact support. -/
theorem properComplex_inclusion_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (Langlands.SmoothRep.toRep.mapHomologicalComplex c).map
          ((properComplex c f hf hp).app F) ≫
        (forgetSupportComplex R G X c).app F =
      (forgetSupportComplex R G Y c).app ((directImageComplex c f hf).obj F) ≫
        (globalComplexMap c f hf).app F := by
  ext i s
  rfl

/-- Proper pullback along the identity gives the identity after the actual
smooth-direct-image identification. -/
@[simp]
theorem properComplex_id
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (compactComplex R G X c).map ((directImageIdIso (R := R) c).hom.app F) ≫
        (properComplex c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id).app F =
      𝟙 ((compactComplex R G X c).obj F) := by
  ext i s
  rfl

/-- Proper smooth chain maps compose through the actual lax direct-image map. -/
theorem properComplex_comp
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (compactComplex R G Z c).map ((directImageCompMap c f hf g hg).app F) ≫
        (properComplex c (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp)).app F =
      (properComplex c g hg hq).app ((directImageComplex c f hf).obj F) ≫
        (properComplex c f hf hp).app F := by
  ext i s
  rfl

/-- Apply smooth-category homology to the actual proper chain map. -/
def properHomology (hp : IsProperMap f) (i : I) :
    directImageComplex c f hf ⋙ compactHomology R G Y c i ⟶
      compactHomology R G X c i :=
  Functor.whiskerRight (properComplex c f hf hp)
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i)

/-- Global homology of the actual inclusion into ordinary direct image. -/
def globalHomologyMap (i : I) :
    directImageComplex c f hf ⋙ globalHomology R G Y c i ⟶
      globalHomology R G X c i :=
  Functor.whiskerRight (globalComplexMap c f hf) (homologyFunctor (Rep.{u} R G) c i)

set_option backward.isDefEq.respectTransparency false in
/-- Smooth homology retains the ordinary compact pullback of the actual
smooth-image inclusion, under the proved exact-inclusion comparison. -/
theorem properHomology_comparison (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I) :
    Langlands.SmoothRep.toRep.map ((properHomology c f hf hp i).app F) ≫
        (compactHomologyToRepIso R G X c i).hom.app F =
      (compactHomologyToRepIso R G Y c i).hom.app ((directImageComplex c f hf).obj F) ≫
        LocalCompactComparison.pullbackHomology f hf hp
          ((directImageInclusionComplex c f hf).app F) i := by
  let H := homologyFunctor (Rep.{u} R G) c i
  let e := DerivedPlus.mapHomologicalComplexHomologyIso
    (Langlands.SmoothRep.toRep (R := R) (G := G)) c i
  have hn := e.inv.naturality ((properComplex c f hf hp).app F)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg H.map (properComplex_comparison c f hf hp F)
  simp only [Functor.map_comp] at hc
  simp only [compactHomologyToRepIso_hom_app]
  simp only [properHomology, Functor.whiskerRight_app]
  change _ ≫ (e.inv.app _ ≫ H.map _) = e.inv.app _ ≫ H.map _ ≫ H.map _
  rw [← Category.assoc, hn, Category.assoc, hc]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- Proper smooth homology pullback commutes with support forgetting. -/
theorem properHomology_inclusion_triangle (hp : IsProperMap f)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I) :
    Langlands.SmoothRep.toRep.map ((properHomology c f hf hp i).app F) ≫
        (forgetSupportHomology R G X c i).app F =
      (forgetSupportHomology R G Y c i).app ((directImageComplex c f hf).obj F) ≫
        (globalHomologyMap c f hf i).app F := by
  let H := homologyFunctor (Rep.{u} R G) c i
  let e := DerivedPlus.mapHomologicalComplexHomologyIso
    (Langlands.SmoothRep.toRep (R := R) (G := G)) c i
  have hn := e.inv.naturality ((properComplex c f hf hp).app F)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg H.map (properComplex_inclusion_triangle c f hf hp F)
  simp only [Functor.map_comp] at hc
  simp only [forgetSupportHomology_app, properHomology, globalHomologyMap,
    Functor.whiskerRight_app]
  change _ ≫ (e.inv.app _ ≫ H.map _) = e.inv.app _ ≫ H.map _ ≫ H.map _
  rw [← Category.assoc, hn, Category.assoc, hc]
  rfl

@[simp]
theorem properHomology_id
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I) :
    (compactHomology R G X c i).map ((directImageIdIso (R := R) c).hom.app F) ≫
        (properHomology c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id i).app F =
      𝟙 ((compactHomology R G X c i).obj F) := by
  change (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i).map _ ≫
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i).map _ = _
  rw [← CategoryTheory.Functor.map_comp, properComplex_id]
  exact (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i).map_id _

theorem properHomology_comp
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) (i : I) :
    (compactHomology R G Z c i).map ((directImageCompMap c f hf g hg).app F) ≫
        (properHomology c (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp) i).app F =
      (properHomology c g hg hq i).app ((directImageComplex c f hf).obj F) ≫
        (properHomology c f hf hp i).app F := by
  change (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i).map _ ≫
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) c i).map _ = _
  rw [← Functor.map_comp, properComplex_comp c f hf g hg hp hq F, Functor.map_comp]
  rfl

end Langlands.Cohomology.ProperSmoothCompactComplexes

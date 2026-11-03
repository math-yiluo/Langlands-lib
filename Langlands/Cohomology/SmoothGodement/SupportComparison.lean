import Langlands.Cohomology.SmoothGodement.Spatial

/-! # Global sections and support forgetting for the separate smooth Godement complex -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

open CategoryTheory HomologicalComplex
open Langlands.Sheaf.Equivariant

universe u t

namespace Langlands.Cohomology.ProperSmoothCompactComplexes

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  {I : Type t} (c : ComplexShape I)

/-- The actual smooth identity comparison gives the identity on global sections. -/
theorem globalComplexMap_id
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (globalComplex R G X c).map ((directImageIdIso (R := R) c).hom.app F) ≫
        (globalComplexMap c (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)).app F =
      𝟙 ((globalComplex R G X c).obj F) := by
  ext i s
  rfl

/-- The global-section maps respect the actual lax composition of smooth images. -/
theorem globalComplexMap_comp
    (f : C(X, Y)) (hf : ∀ (k : G) (x : X), f (k • x) = k • f x)
    (g : C(Y, Z)) (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : HomologicalComplex (SmoothTopologicalSheaf R G X) c) :
    (globalComplex R G Z c).map ((directImageCompMap c f hf g hg).app F) ≫
        (globalComplexMap c (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])).app F =
      (globalComplexMap c g hg).app ((directImageComplex c f hf).obj F) ≫
        (globalComplexMap c f hf).app F := by
  ext i s
  rfl

end Langlands.Cohomology.ProperSmoothCompactComplexes

namespace Langlands.Cohomology.SmoothGodementCohomology

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- All global sections of the actual separate smooth Godement complex. -/
def smoothGodementGlobalComplex :
    SmoothTopologicalSheaf R G X ⥤ CochainComplex (Rep.{u} R G) ℕ :=
  Godement.smoothComplexFunctor R G X ⋙
    ProperSmoothCompactComplexes.globalComplex R G X (ComplexShape.up ℕ)

/-- Homology of the actual global-section complex in algebraic representations. -/
def smoothGodementGlobalCohomology (q : ℕ) :
    SmoothTopologicalSheaf R G X ⥤ Rep.{u} R G :=
  smoothGodementGlobalComplex R G X ⋙
    homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q

/-- The original compact-support inclusions, applied to the separate smooth
Godement complex after forgetting the smoothness witnesses of representations. -/
def forgetSupportComplex :
    smoothGodementCompactComplex R G X ⋙
        Langlands.SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ) ⟶
      smoothGodementGlobalComplex R G X :=
  Functor.whiskerLeft (Godement.smoothComplexFunctor R G X)
    (ProperSmoothCompactComplexes.forgetSupportComplex R G X (ComplexShape.up ℕ))

/-- Support forgetting retains each original global section. -/
@[simp]
theorem forgetSupportComplex_apply (F : SmoothTopologicalSheaf R G X) (n : ℕ)
    (s : ((smoothGodementCompactComplex R G X).obj F).X n) :
    (((forgetSupportComplex R G X).app F).f n).hom s = s.val := rfl

/-- Support forgetting on smooth-category homology uses the proved exactness
of the inclusion into algebraic representations. -/
def forgetSupport (q : ℕ) :
    smoothGodementCompactCohomology R G X q ⋙ Langlands.SmoothRep.toRep ⟶
      smoothGodementGlobalCohomology R G X q :=
  Functor.whiskerLeft (Godement.smoothComplexFunctor R G X)
    (ProperSmoothCompactComplexes.forgetSupportHomology R G X (ComplexShape.up ℕ) q)

/-- The support-forgetting cohomology map is homology of the actual chain
inclusion, preceded by the inverse exact-inclusion homology comparison. -/
theorem forgetSupport_app (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (forgetSupport R G X q).app F =
      (DerivedPlus.mapHomologicalComplexHomologyIso
        (Langlands.SmoothRep.toRep (R := R) (G := G)) (ComplexShape.up ℕ) q).inv.app
          ((smoothGodementCompactComplex R G X).obj F) ≫
        (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map
          ((forgetSupportComplex R G X).app F) :=
  ProperSmoothCompactComplexes.forgetSupportHomology_app
    R G X (ComplexShape.up ℕ) q (Godement.smoothComplex R G X F)

namespace Spatial

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G Y] [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Apply global sections to the constructed higher smooth Godement map and
then the actual smooth-image inclusion into ordinary direct image. -/
def globalNatTrans :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothGodementGlobalComplex R G Y ⟶
      smoothGodementGlobalComplex R G X :=
  Functor.whiskerRight (Godement.SmoothSpatial.complexNatTrans f hf)
      (ProperSmoothCompactComplexes.globalComplex R G Y (ComplexShape.up ℕ)) ≫
    Functor.whiskerLeft (Godement.smoothComplexFunctor R G X)
      (ProperSmoothCompactComplexes.globalComplexMap (ComplexShape.up ℕ) f hf)

/-- The actual global spatial chain map requires no properness hypothesis. -/
abbrev globalMap (F : SmoothTopologicalSheaf R G X) :=
  (globalNatTrans (R := R) f hf).app F

/-- Both factors of the spatial map are constructed chain maps. -/
theorem globalMap_eq (F : SmoothTopologicalSheaf R G X) :
    globalMap f hf F =
      (ProperSmoothCompactComplexes.globalComplex R G Y (ComplexShape.up ℕ)).map
          (Godement.SmoothSpatial.complexMap f hf F) ≫
        (ProperSmoothCompactComplexes.globalComplexMap (ComplexShape.up ℕ) f hf).app
          (Godement.smoothComplex R G X F) := rfl

/-- The map on every original global section is the smooth Godement sheaf
map followed by the smooth-image inclusion. -/
@[simp]
theorem globalMap_apply (F : SmoothTopologicalSheaf R G X) (n : ℕ)
    (s : ((smoothGodementGlobalComplex R G Y).obj
      ((SmoothDirectImage.functor f hf).obj F)).X n) :
    ((globalMap f hf F).f n).hom s =
      ((((Godement.SmoothSpatial.complexMap f hf F).f n).hom.hom.app
        (Opposite.op ActionOpens.top)).hom s).val := rfl

/-- Degree zero retains the actual separate smooth Godement degree-zero map. -/
theorem globalMap_apply_zero (F : SmoothTopologicalSheaf R G X)
    (s : ((smoothGodementGlobalComplex R G Y).obj
      ((SmoothDirectImage.functor f hf).obj F)).X 0) :
    ((globalMap f hf F).f 0).hom s =
      (((Godement.SmoothSpatial.zeroMap f hf F).hom.hom.app
        (Opposite.op ActionOpens.top)).hom s).val := by
  rw [globalMap_apply, Godement.SmoothSpatial.complexMap_f_zero]
  rfl

/-- Naturality retains every original smooth sheaf morphism. -/
@[reassoc]
theorem globalMap_naturality
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementGlobalComplex R G Y).map ((SmoothDirectImage.functor f hf).map a) ≫
        globalMap f hf F' =
      globalMap f hf F ≫ (smoothGodementGlobalComplex R G X).map a :=
  (globalNatTrans f hf).naturality a

/-- Global spatial maps respect the actual smooth-direct-image identity. -/
@[reassoc]
theorem globalMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementGlobalComplex R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        globalMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F =
      𝟙 ((smoothGodementGlobalComplex R G X).obj F) := by
  rw [globalMap_eq]
  change (ProperSmoothCompactComplexes.globalComplex R G X (ComplexShape.up ℕ)).map
      ((Godement.smoothComplexFunctor R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F)) ≫
      ((ProperSmoothCompactComplexes.globalComplex R G X (ComplexShape.up ℕ)).map
        (Godement.SmoothSpatial.complexMap (ContinuousMap.id X)
          (fun (_ : G) (_ : X) => rfl) F) ≫ _) = _
  rw [← Functor.map_comp_assoc, Godement.SmoothSpatial.complexMap_id]
  exact ProperSmoothCompactComplexes.globalComplexMap_id
    (ComplexShape.up ℕ) (Godement.smoothComplex R G X F)

/-- Global spatial maps compose through the actual smooth-image lax map. -/
@[reassoc]
theorem globalMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementGlobalComplex R G Z).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        globalMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F =
      globalMap g hg ((SmoothDirectImage.functor f hf).obj F) ≫ globalMap f hf F := by
  let c := ComplexShape.up ℕ
  have hn := (ProperSmoothCompactComplexes.globalComplexMap c g hg).naturality
    (Godement.SmoothSpatial.complexMap f hf F)
  change (ProperSmoothCompactComplexes.globalComplex R G Z c).map
      (((SmoothDirectImage.functor g hg).mapHomologicalComplex c).map
        (Godement.SmoothSpatial.complexMap f hf F)) ≫
      (ProperSmoothCompactComplexes.globalComplexMap c g hg).app
        (((SmoothDirectImage.functor f hf).mapHomologicalComplex c).obj
          (Godement.smoothComplex R G X F)) =
    (ProperSmoothCompactComplexes.globalComplexMap c g hg).app
        (Godement.smoothComplex R G Y ((SmoothDirectImage.functor f hf).obj F)) ≫
      (ProperSmoothCompactComplexes.globalComplex R G Y c).map
        (Godement.SmoothSpatial.complexMap f hf F) at hn
  rw [globalMap_eq]
  change (ProperSmoothCompactComplexes.globalComplex R G Z c).map
      ((Godement.smoothComplexFunctor R G Z).map
        ((SmoothDirectImage.compMap f hf g hg).app F)) ≫
      ((ProperSmoothCompactComplexes.globalComplex R G Z c).map
        (Godement.SmoothSpatial.complexMap (g.comp f) _ F) ≫ _) = _
  rw [← Functor.map_comp_assoc, Godement.SmoothSpatial.complexMap_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [ProperSmoothCompactComplexes.globalComplexMap_comp c f hf g hg
    (Godement.smoothComplex R G X F)]
  erw [← Category.assoc
    ((ProperSmoothCompactComplexes.globalComplex R G Z c).map
      (((SmoothDirectImage.functor g hg).mapHomologicalComplex c).map
        (Godement.SmoothSpatial.complexMap f hf F))), hn]
  simp only [globalMap_eq, Category.assoc]
  rfl

/-- Proper compact pullback and global pullback commute with the actual
support-forgetting chain inclusions. -/
@[reassoc]
theorem compactMap_forgetSupport (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    (Langlands.SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ)).map
          (compactMap f hf hp F) ≫ (forgetSupportComplex R G X).app F =
      (forgetSupportComplex R G Y).app ((SmoothDirectImage.functor f hf).obj F) ≫
        globalMap f hf F := by
  let c := ComplexShape.up ℕ
  have hn := (ProperSmoothCompactComplexes.forgetSupportComplex R G Y c).naturality
    (Godement.SmoothSpatial.complexMap f hf F)
  dsimp only [Functor.comp_map] at hn
  simp only [compactMap_eq, Functor.map_comp, globalMap_eq, Category.assoc]
  erw [ProperSmoothCompactComplexes.properComplex_inclusion_triangle c f hf hp
    (Godement.smoothComplex R G X F)]
  erw [← Category.assoc, hn]

/-- Actual homology of the global spatial chain map. -/
def globalCohomologyNatTrans (q : ℕ) :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothGodementGlobalCohomology R G Y q ⟶
      smoothGodementGlobalCohomology R G X q :=
  Functor.whiskerRight (globalNatTrans f hf)
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q)

/-- The induced spatial map on global-section homology. -/
abbrev globalCohomologyMap (F : SmoothTopologicalSheaf R G X) (q : ℕ) :=
  (globalCohomologyNatTrans (R := R) f hf q).app F

/-- The cohomology map is homology of the constructed global chain map. -/
theorem globalCohomologyMap_eq (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    globalCohomologyMap f hf F q =
      (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map (globalMap f hf F) := rfl

@[reassoc]
theorem globalCohomologyMap_naturality (q : ℕ)
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementGlobalCohomology R G Y q).map ((SmoothDirectImage.functor f hf).map a) ≫
        globalCohomologyMap f hf F' q =
      globalCohomologyMap f hf F q ≫ (smoothGodementGlobalCohomology R G X q).map a :=
  (globalCohomologyNatTrans f hf q).naturality a

@[reassoc]
theorem globalCohomologyMap_id (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementGlobalCohomology R G X q).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        globalCohomologyMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) F q =
      𝟙 ((smoothGodementGlobalCohomology R G X q).obj F) := by
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, globalMap_id]
  exact (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map_id _

@[reassoc]
theorem globalCohomologyMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementGlobalCohomology R G Z q).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        globalCohomologyMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) F q =
      globalCohomologyMap g hg ((SmoothDirectImage.functor f hf).obj F) q ≫
        globalCohomologyMap f hf F q := by
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, globalMap_comp f hf g hg F, Functor.map_comp]
  rfl

/-- The support-forgetting triangle in cohomology uses exact-inclusion
naturality and homology of the proved chain triangle. -/
@[reassoc]
theorem cohomologyMap_forgetSupport (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    Langlands.SmoothRep.toRep.map (cohomologyMap f hf hp F q) ≫
        (forgetSupport R G X q).app F =
      (forgetSupport R G Y q).app ((SmoothDirectImage.functor f hf).obj F) ≫
        globalCohomologyMap f hf F q := by
  let H := homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q
  let e := DerivedPlus.mapHomologicalComplexHomologyIso
    (Langlands.SmoothRep.toRep (R := R) (G := G)) (ComplexShape.up ℕ) q
  have hn := e.inv.naturality (compactMap f hf hp F)
  dsimp only [Functor.comp_map] at hn
  have hc := congrArg H.map (compactMap_forgetSupport f hf hp F)
  simp only [Functor.map_comp] at hc
  simp only [forgetSupport_app, cohomologyMap_eq, globalCohomologyMap_eq]
  change _ ≫ (e.inv.app _ ≫ H.map _) = e.inv.app _ ≫ H.map _ ≫ H.map _
  rw [← Category.assoc, hn, Category.assoc, hc]
  rfl

end Spatial
end Langlands.Cohomology.SmoothGodementCohomology

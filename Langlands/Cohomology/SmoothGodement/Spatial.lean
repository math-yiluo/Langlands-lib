import Langlands.Sheaf.Equivariant.Godement.SmoothSpatialComplex
import Langlands.Cohomology.SmoothGodementCohomology
import Langlands.Cohomology.ProperSmoothCompactComplexes

/-! # Proper spatial maps on separate smooth Godement compact cohomology -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.SmoothGodementCohomology.Spatial

open CategoryTheory HomologicalComplex
open Langlands.Sheaf.Equivariant

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Apply compact sections to the constructed smooth Godement chain map,
then the actual proper compact-section pullback in every degree. -/
def compactNatTrans (hp : IsProperMap f) :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothGodementCompactComplex R G Y ⟶
      smoothGodementCompactComplex R G X :=
  Functor.whiskerRight (Godement.SmoothSpatial.complexNatTrans f hf)
      (ProperSmoothCompactComplexes.compactComplex R G Y (ComplexShape.up ℕ)) ≫
    Functor.whiskerLeft (Godement.smoothComplexFunctor R G X)
      (ProperSmoothCompactComplexes.properComplex (ComplexShape.up ℕ) f hf hp)

/-- The actual proper spatial map of compact-section complexes. -/
abbrev compactMap (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) :=
  (compactNatTrans (R := R) f hf hp).app F

/-- The component is a composite of two already constructed chain maps. -/
theorem compactMap_eq (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) :
    compactMap f hf hp F =
      (ProperSmoothCompactComplexes.compactComplex R G Y (ComplexShape.up ℕ)).map
          (Godement.SmoothSpatial.complexMap f hf F) ≫
        (ProperSmoothCompactComplexes.properComplex (ComplexShape.up ℕ) f hf hp).app
          (Godement.smoothComplex R G X F) := rfl

/-- Every degree uses the actual smooth sheaf map followed by proper pullback. -/
theorem compactMap_f (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) (n : ℕ) :
    (compactMap f hf hp F).f n =
      (smoothSheafCompactSections R G Y).map
          ((Godement.SmoothSpatial.complexMap f hf F).f n) ≫
        (ProperSmoothCompactSections.natTrans f hf hp).app
          ((Godement.smoothComplex R G X F).X n) := rfl

/-- On every original compact section, apply the constructed sheaf map and
forget only the smooth-image witness. -/
@[simp]
theorem compactMap_apply (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) (n : ℕ)
    (s : ((smoothGodementCompactComplex R G Y).obj
      ((SmoothDirectImage.functor f hf).obj F)).X n) :
    (Langlands.SmoothRep.hom ((compactMap f hf hp F).f n) s).val =
      ((((Godement.SmoothSpatial.complexMap f hf F).f n).hom.hom.app
        (Opposite.op ActionOpens.top)).hom s.val).val := rfl

/-- Degree zero uses precisely the constructed separate smooth Godement map. -/
@[simp]
theorem compactMap_f_zero (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) :
    (compactMap f hf hp F).f 0 =
      (smoothSheafCompactSections R G Y).map (Godement.SmoothSpatial.zeroMap f hf F) ≫
        (ProperSmoothCompactSections.natTrans f hf hp).app
          ((Godement.smoothZeroFunctor R G X).obj F) := by
  rw [compactMap_f, Godement.SmoothSpatial.complexMap_f_zero]
  rfl

/-- Naturality holds for every original smooth sheaf morphism. -/
@[reassoc]
theorem compactMap_naturality (hp : IsProperMap f)
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementCompactComplex R G Y).map ((SmoothDirectImage.functor f hf).map a) ≫
        compactMap f hf hp F' =
      compactMap f hf hp F ≫ (smoothGodementCompactComplex R G X).map a :=
  (compactNatTrans f hf hp).naturality a

/-- The actual smooth-direct-image unit gives the identity on the compact complex. -/
@[reassoc]
theorem compactMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementCompactComplex R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        compactMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl) isProperMap_id F =
      𝟙 ((smoothGodementCompactComplex R G X).obj F) := by
  rw [compactMap_eq]
  change (ProperSmoothCompactComplexes.compactComplex R G X (ComplexShape.up ℕ)).map
      ((Godement.smoothComplexFunctor R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F)) ≫
      ((ProperSmoothCompactComplexes.compactComplex R G X (ComplexShape.up ℕ)).map
        (Godement.SmoothSpatial.complexMap (ContinuousMap.id X)
          (fun (_ : G) (_ : X) => rfl) F) ≫ _) = _
  rw [← Functor.map_comp_assoc, Godement.SmoothSpatial.complexMap_id]
  exact ProperSmoothCompactComplexes.properComplex_id
    (ComplexShape.up ℕ) (Godement.smoothComplex R G X F)

/-- Proper spatial maps compose through the actual smooth-image lax comparison. -/
@[reassoc]
theorem compactMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementCompactComplex R G Z).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        compactMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) (hq.comp hp) F =
      compactMap g hg hq ((SmoothDirectImage.functor f hf).obj F) ≫
        compactMap f hf hp F := by
  let c := ComplexShape.up ℕ
  have hn := (ProperSmoothCompactComplexes.properComplex c g hg hq).naturality
    (Godement.SmoothSpatial.complexMap f hf F)
  change (ProperSmoothCompactComplexes.compactComplex R G Z c).map
      (((SmoothDirectImage.functor g hg).mapHomologicalComplex c).map
        (Godement.SmoothSpatial.complexMap f hf F)) ≫
      (ProperSmoothCompactComplexes.properComplex c g hg hq).app
        (((SmoothDirectImage.functor f hf).mapHomologicalComplex c).obj
          (Godement.smoothComplex R G X F)) =
    (ProperSmoothCompactComplexes.properComplex c g hg hq).app
        (Godement.smoothComplex R G Y ((SmoothDirectImage.functor f hf).obj F)) ≫
      (ProperSmoothCompactComplexes.compactComplex R G Y c).map
        (Godement.SmoothSpatial.complexMap f hf F) at hn
  rw [compactMap_eq]
  change (ProperSmoothCompactComplexes.compactComplex R G Z c).map
      ((Godement.smoothComplexFunctor R G Z).map
        ((SmoothDirectImage.compMap f hf g hg).app F)) ≫
      ((ProperSmoothCompactComplexes.compactComplex R G Z c).map
        (Godement.SmoothSpatial.complexMap (g.comp f) _ F) ≫ _) = _
  rw [← Functor.map_comp_assoc, Godement.SmoothSpatial.complexMap_comp]
  simp only [Functor.map_comp, Category.assoc]
  erw [ProperSmoothCompactComplexes.properComplex_comp c f hf g hg hp hq
    (Godement.smoothComplex R G X F)]
  erw [← Category.assoc
    ((ProperSmoothCompactComplexes.compactComplex R G Z c).map
      (((SmoothDirectImage.functor g hg).mapHomologicalComplex c).map
        (Godement.SmoothSpatial.complexMap f hf F))), hn]
  simp only [compactMap_eq, Category.assoc]
  rfl

/-- Apply actual homology in the existing smooth representation category. -/
def cohomologyNatTrans (hp : IsProperMap f) (q : ℕ) :
    SmoothDirectImage.functor (R := R) f hf ⋙ smoothGodementCompactCohomology R G Y q ⟶
      smoothGodementCompactCohomology R G X q :=
  Functor.whiskerRight (compactNatTrans f hf hp)
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q)

/-- The proper spatial map on the already defined smooth Godement cohomology. -/
abbrev cohomologyMap (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) (q : ℕ) :=
  (cohomologyNatTrans (R := R) f hf hp q).app F

/-- The cohomology map is the homology of the actual compact chain map. -/
theorem cohomologyMap_eq (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    cohomologyMap f hf hp F q =
      (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map
        (compactMap f hf hp F) := rfl

/-- Naturality retains all original coefficient morphisms. -/
@[reassoc]
theorem cohomologyMap_naturality (hp : IsProperMap f) (q : ℕ)
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementCompactCohomology R G Y q).map ((SmoothDirectImage.functor f hf).map a) ≫
        cohomologyMap f hf hp F' q =
      cohomologyMap f hf hp F q ≫ (smoothGodementCompactCohomology R G X q).map a :=
  (cohomologyNatTrans f hf hp q).naturality a

/-- The actual identity comparison induces the identity in every degree of cohomology. -/
@[reassoc]
theorem cohomologyMap_id (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementCompactCohomology R G X q).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        cohomologyMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id F q =
      𝟙 ((smoothGodementCompactCohomology R G X q).obj F) := by
  change (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, compactMap_id]
  exact (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map_id _

/-- Proper pullbacks on cohomology satisfy the actual lax spatial composition law. -/
@[reassoc]
theorem cohomologyMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementCompactCohomology R G Z q).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        cohomologyMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp) F q =
      cohomologyMap g hg hq ((SmoothDirectImage.functor f hf).obj F) q ≫
        cohomologyMap f hf hp F q := by
  change (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, compactMap_comp f hf g hg hp hq F, Functor.map_comp]
  rfl

end Langlands.Cohomology.SmoothGodementCohomology.Spatial

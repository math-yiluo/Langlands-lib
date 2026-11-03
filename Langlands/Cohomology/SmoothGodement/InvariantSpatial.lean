import Langlands.Cohomology.SmoothGodement.Spatial
import Langlands.Cohomology.SmoothGodementComparison.Invariants

/-! # Invariant compact spatial maps for the separate smooth Godement complex -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.SmoothGodementCohomology

open CategoryTheory HomologicalComplex
open Langlands.Sheaf.Equivariant
open SmoothGodementComparison

universe u

variable (R : Type u) [CommRing R] (G : Type u) [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  (X : Type u) [TopologicalSpace X] [MulAction G X]
  [ContinuousConstSMul G X] [HasStableNeighbourhoods G X]

/-- Degreewise invariants of the compact complex are the existing invariant
compact complex, through the actual composition isomorphism for functors on complexes. -/
def smoothGodementInvariantCompactComplexIso :
    smoothGodementCompactComplex R G X ⋙
        (smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ) ≅
      smoothGodementInvariantCompactComplex R G X :=
  Functor.isoWhiskerLeft (Godement.smoothComplexFunctor R G X)
    (Functor.mapHomologicalComplexCompIso
      (show smoothSheafCompactSections R G X ⋙ smoothInvariants R G ≅
        SmoothSheafCohomology.invariantCompactSections R G X from Iso.refl _)
      (ComplexShape.up ℕ))

/-- On original coefficient morphisms the two presentations give the same
chain map, degreewise the invariants of the compact-section morphism. -/
theorem smoothGodementInvariantCompactComplex_map
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementInvariantCompactComplex R G X).map a =
      ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((smoothGodementCompactComplex R G X).map a) := by
  ext n s
  rfl

namespace Spatial

variable {R G X}
  {Y Z : Type u} [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G Y] [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- Transport degreewise invariants of the actual compact chain map to the
already defined invariant compact complexes. -/
def invariantCompactNatTrans (hp : IsProperMap f) :
    SmoothDirectImage.functor (R := R) f hf ⋙
        smoothGodementInvariantCompactComplex R G Y ⟶
      smoothGodementInvariantCompactComplex R G X :=
  (Functor.isoWhiskerLeft (SmoothDirectImage.functor f hf)
      (smoothGodementInvariantCompactComplexIso R G Y)).inv ≫
    Functor.whiskerRight (compactNatTrans f hf hp)
      ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)) ≫
    (smoothGodementInvariantCompactComplexIso R G X).hom

/-- The proper spatial chain map on the original invariant compact complex. -/
abbrev invariantCompactMap (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) :=
  (invariantCompactNatTrans (R := R) f hf hp).app F

/-- The chain map is the explicit transport of degreewise invariants of the
constructed compact chain map. -/
theorem invariantCompactMap_eq (hp : IsProperMap f) (F : SmoothTopologicalSheaf R G X) :
    invariantCompactMap f hf hp F =
      (smoothGodementInvariantCompactComplexIso R G Y).inv.app
          ((SmoothDirectImage.functor f hf).obj F) ≫
        ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map
          (compactMap f hf hp F) ≫
        (smoothGodementInvariantCompactComplexIso R G X).hom.app F := rfl

/-- The composition comparison is the identity on original invariant sections,
so the transported map is precisely the restriction of the compact chain map. -/
theorem invariantCompactMap_eq_map (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    invariantCompactMap f hf hp F =
      ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map
        (compactMap f hf hp F) := by
  ext n s
  rfl

/-- In each degree the map is the actual invariants map of the compact pullback. -/
@[simp]
theorem invariantCompactMap_f (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) (n : ℕ) :
    (invariantCompactMap f hf hp F).f n =
      (smoothInvariants R G).map ((compactMap f hf hp F).f n) := by
  rw [invariantCompactMap_eq_map]
  rfl

/-- The original invariant compact section is mapped by the constructed
Godement sheaf map, with the same support-preserving underlying section. -/
@[simp]
theorem invariantCompactMap_apply (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) (n : ℕ)
    (s : ((smoothGodementInvariantCompactComplex R G Y).obj
      ((SmoothDirectImage.functor f hf).obj F)).X n) :
    (((invariantCompactMap f hf hp F).f n).hom s).val.val =
      ((((Godement.SmoothSpatial.complexMap f hf F).f n).hom.hom.app
        (Opposite.op ActionOpens.top)).hom s.val.val).val := by
  rw [invariantCompactMap_f]
  rfl

/-- In degree zero the map restricts the actual smooth Godement zero map. -/
@[simp]
theorem invariantCompactMap_f_zero (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) :
    (invariantCompactMap f hf hp F).f 0 =
      (smoothInvariants R G).map
        ((smoothSheafCompactSections R G Y).map (Godement.SmoothSpatial.zeroMap f hf F) ≫
          (ProperSmoothCompactSections.natTrans f hf hp).app
            ((Godement.smoothZeroFunctor R G X).obj F)) := by
  rw [invariantCompactMap_f, compactMap_f_zero]

/-- Naturality retains every morphism of the original smooth sheaves. -/
@[reassoc]
theorem invariantCompactMap_naturality (hp : IsProperMap f)
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementInvariantCompactComplex R G Y).map
        ((SmoothDirectImage.functor f hf).map a) ≫ invariantCompactMap f hf hp F' =
      invariantCompactMap f hf hp F ≫
        (smoothGodementInvariantCompactComplex R G X).map a :=
  (invariantCompactNatTrans f hf hp).naturality a

/-- The actual smooth-direct-image unit induces the identity on invariant complexes. -/
@[reassoc]
theorem invariantCompactMap_id (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementInvariantCompactComplex R G X).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        invariantCompactMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id F =
      𝟙 ((smoothGodementInvariantCompactComplex R G X).obj F) := by
  rw [invariantCompactMap_eq_map, smoothGodementInvariantCompactComplex_map]
  rw [← Functor.map_comp, compactMap_id]
  exact ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map_id _

/-- Invariant compact maps compose through the original lax direct-image comparison. -/
@[reassoc]
theorem invariantCompactMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (F : SmoothTopologicalSheaf R G X) :
    (smoothGodementInvariantCompactComplex R G Z).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        invariantCompactMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp) F =
      invariantCompactMap g hg hq ((SmoothDirectImage.functor f hf).obj F) ≫
        invariantCompactMap f hf hp F := by
  simp only [invariantCompactMap_eq_map, smoothGodementInvariantCompactComplex_map]
  rw [← Functor.map_comp, compactMap_comp f hf g hg hp hq F, Functor.map_comp]

/-- Take module homology after degreewise invariants of the actual compact chain map. -/
def invariantCohomologyNatTrans (hp : IsProperMap f) (q : ℕ) :
    SmoothDirectImage.functor (R := R) f hf ⋙
        smoothGodementInvariantCompactCohomology R G Y q ⟶
      smoothGodementInvariantCompactCohomology R G X q :=
  Functor.whiskerRight (invariantCompactNatTrans f hf hp)
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)

/-- The proper spatial map on existing invariant compact Godement cohomology. -/
abbrev invariantCohomologyMap (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) (q : ℕ) :=
  (invariantCohomologyNatTrans (R := R) f hf hp q).app F

/-- The map is module homology of the constructed invariant chain map. -/
theorem invariantCohomologyMap_eq (hp : IsProperMap f)
    (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    invariantCohomologyMap f hf hp F q =
      (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
        (invariantCompactMap f hf hp F) := rfl

/-- Naturality on invariant cohomology follows from the actual chain transformation. -/
@[reassoc]
theorem invariantCohomologyMap_naturality (hp : IsProperMap f) (q : ℕ)
    {F F' : SmoothTopologicalSheaf R G X} (a : F ⟶ F') :
    (smoothGodementInvariantCompactCohomology R G Y q).map
        ((SmoothDirectImage.functor f hf).map a) ≫ invariantCohomologyMap f hf hp F' q =
      invariantCohomologyMap f hf hp F q ≫
        (smoothGodementInvariantCompactCohomology R G X q).map a :=
  (invariantCohomologyNatTrans f hf hp q).naturality a

/-- Identity on invariant complexes induces identity in every degree of module homology. -/
@[reassoc]
theorem invariantCohomologyMap_id (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementInvariantCompactCohomology R G X q).map
        ((SmoothDirectImage.idIso (R := R) (G := G) (X := X)).hom.app F) ≫
        invariantCohomologyMap (ContinuousMap.id X) (fun (_ : G) (_ : X) => rfl)
          isProperMap_id F q =
      𝟙 ((smoothGodementInvariantCompactCohomology R G X q).obj F) := by
  change (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, invariantCompactMap_id]
  exact (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map_id _

/-- The original lax composition law descends to invariant compact cohomology. -/
@[reassoc]
theorem invariantCohomologyMap_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (F : SmoothTopologicalSheaf R G X) (q : ℕ) :
    (smoothGodementInvariantCompactCohomology R G Z q).map
        ((SmoothDirectImage.compMap f hf g hg).app F) ≫
        invariantCohomologyMap (g.comp f)
          (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
          (hq.comp hp) F q =
      invariantCohomologyMap g hg hq ((SmoothDirectImage.functor f hf).obj F) q ≫
        invariantCohomologyMap f hf hp F q := by
  change (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ ≫
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map _ = _
  rw [← Functor.map_comp, invariantCompactMap_comp f hf g hg hp hq F, Functor.map_comp]
  rfl

end Spatial
end Langlands.Cohomology.SmoothGodementCohomology

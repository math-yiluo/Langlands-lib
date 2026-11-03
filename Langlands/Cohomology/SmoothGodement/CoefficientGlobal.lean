import Langlands.Cohomology.SmoothGodement.SupportComparison
import Langlands.Cohomology.SmoothGodement.CoefficientSpatial

/-! # Global smooth Godement maps for full coefficients and support comparison -/

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

/-- Actual global chain pullback for the full locally constant smooth coefficients. -/
def coefficientGlobalNatTrans :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙ smoothGodementGlobalComplex R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙ smoothGodementGlobalComplex R G X :=
  Functor.whiskerRight (SmoothDirectImage.coefficientNatTrans f hf)
      (smoothGodementGlobalComplex R G Y) ≫
    Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
      (globalNatTrans f hf)

/-- Resolve the full coefficient map, then apply the constructed global spatial map. -/
theorem coefficientGlobalNatTrans_app (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientGlobalNatTrans f hf).app M =
      (smoothGodementGlobalComplex R G Y).map
          (SmoothDirectImage.coefficientMap f hf M) ≫
        globalMap f hf ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := rfl

/-- In every degree the original global section passes through the resolved
coefficient map and the spatial sheaf map, then its smooth-image witness is removed. -/
@[simp]
theorem coefficientGlobalNatTrans_apply (M : Langlands.SmoothRep.{u, u, u} R G)
    (n : ℕ)
    (s : ((smoothGodementGlobalComplex R G Y).obj
      ((LocallyConstantSheaf.smoothFunctor R G Y).obj M)).X n) :
    (((coefficientGlobalNatTrans f hf).app M).f n).hom s =
      ((((Godement.SmoothSpatial.complexMap f hf
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M)).f n).hom.hom.app
          (Opposite.op ActionOpens.top)).hom
        ((((smoothGodementGlobalComplex R G Y).map
          (SmoothDirectImage.coefficientMap f hf M)).f n).hom s)).val := rfl

/-- All original coefficient intertwiners commute with global chain pullback. -/
@[reassoc]
theorem coefficientGlobalNatTrans_naturality
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementGlobalComplex R G Y).map a ≫
        (coefficientGlobalNatTrans f hf).app N =
      (coefficientGlobalNatTrans f hf).app M ≫
        (LocallyConstantSheaf.smoothFunctor R G X ⋙
          smoothGodementGlobalComplex R G X).map a :=
  (coefficientGlobalNatTrans f hf).naturality a

@[simp]
theorem coefficientGlobalNatTrans_id :
    coefficientGlobalNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementGlobalComplex R G X) := by
  apply NatTrans.ext
  funext M
  rw [coefficientGlobalNatTrans_app, SmoothDirectImage.coefficientMap_id]
  exact globalMap_id _

/-- The matching coefficient and global lax laws give strict contravariant
composition without any properness or invertibility assumption. -/
theorem coefficientGlobalNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) :
    coefficientGlobalNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) =
      coefficientGlobalNatTrans g hg ≫ coefficientGlobalNatTrans f hf := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientGlobalNatTrans_app,
    SmoothDirectImage.coefficientMap_comp f hf g hg M, Functor.map_comp, Category.assoc]
  rw [globalMap_comp, globalMap_naturality_assoc]

/-- Equal actual continuous maps induce equal coefficient global transformations. -/
theorem coefficientGlobalNatTrans_congr {p q : C(X, Y)}
    (hp : ∀ (g : G) (x : X), p (g • x) = g • p x)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x) (h : p = q) :
    coefficientGlobalNatTrans (R := R) p hp =
      coefficientGlobalNatTrans q hq := by
  subst q
  rfl

/-- For a proper map, the coefficient compact and global chain maps commute
with the actual support inclusions. -/
@[reassoc]
theorem coefficientCompactNatTrans_forgetSupport (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (Langlands.SmoothRep.toRep.mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((coefficientCompactNatTrans f hf hp).app M) ≫
        (forgetSupportComplex R G X).app
          ((LocallyConstantSheaf.smoothFunctor R G X).obj M) =
      (forgetSupportComplex R G Y).app
          ((LocallyConstantSheaf.smoothFunctor R G Y).obj M) ≫
        (coefficientGlobalNatTrans f hf).app M := by
  have hn := (forgetSupportComplex R G Y).naturality
    (SmoothDirectImage.coefficientMap f hf M)
  dsimp only [Functor.comp_map] at hn
  simp only [coefficientCompactNatTrans_app, coefficientGlobalNatTrans_app,
    Functor.map_comp, Category.assoc]
  rw [compactMap_forgetSupport, ← Category.assoc, hn, Category.assoc]

/-- Apply algebraic-representation homology to the actual coefficient global chain map. -/
def coefficientGlobalCohomologyNatTrans (q : ℕ) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementGlobalCohomology R G Y q ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementGlobalCohomology R G X q :=
  Functor.whiskerRight (coefficientGlobalNatTrans f hf)
    (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q)

theorem coefficientGlobalCohomologyNatTrans_app (q : ℕ)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientGlobalCohomologyNatTrans f hf q).app M =
      (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map
        ((coefficientGlobalNatTrans f hf).app M) := rfl

/-- The cohomology component also factors through the actual coefficient sheaf map. -/
theorem coefficientGlobalCohomologyNatTrans_app_eq (q : ℕ)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientGlobalCohomologyNatTrans f hf q).app M =
      (smoothGodementGlobalCohomology R G Y q).map
          (SmoothDirectImage.coefficientMap f hf M) ≫
        globalCohomologyMap f hf
          ((LocallyConstantSheaf.smoothFunctor R G X).obj M) q := by
  rw [coefficientGlobalCohomologyNatTrans_app, coefficientGlobalNatTrans_app,
    Functor.map_comp]
  rfl

@[simp]
theorem coefficientGlobalCohomologyNatTrans_id (q : ℕ) :
    coefficientGlobalCohomologyNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) q =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementGlobalCohomology R G X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map _ = _
  rw [coefficientGlobalNatTrans_id]
  exact (homologyFunctor (Rep.{u} R G) (ComplexShape.up ℕ) q).map_id _

theorem coefficientGlobalCohomologyNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y) (q : ℕ) :
    coefficientGlobalCohomologyNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg]) q =
      coefficientGlobalCohomologyNatTrans g hg q ≫
        coefficientGlobalCohomologyNatTrans f hf q := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientGlobalCohomologyNatTrans_app,
    coefficientGlobalNatTrans_comp f hf g hg, Functor.map_comp]

/-- The existing coefficient compact cohomology map has the same factorization. -/
theorem coefficientCohomologyNatTrans_app_eq (hp : IsProperMap f) (q : ℕ)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientCohomologyNatTrans f hf hp q).app M =
      (smoothGodementCompactCohomology R G Y q).map
          (SmoothDirectImage.coefficientMap f hf M) ≫
        cohomologyMap f hf hp
          ((LocallyConstantSheaf.smoothFunctor R G X).obj M) q := by
  rw [coefficientCohomologyNatTrans_app, coefficientCompactNatTrans_app,
    Functor.map_comp]
  rfl

/-- Support forgetting commutes with proper full-coefficient cohomology pullback.
The compact side uses the already proved exact inclusion into algebraic representations. -/
@[reassoc]
theorem coefficientCohomologyNatTrans_forgetSupport (hp : IsProperMap f)
    (q : ℕ) (M : Langlands.SmoothRep.{u, u, u} R G) :
    Langlands.SmoothRep.toRep.map
        ((coefficientCohomologyNatTrans f hf hp q).app M) ≫
        (forgetSupport R G X q).app
          ((LocallyConstantSheaf.smoothFunctor R G X).obj M) =
      (forgetSupport R G Y q).app
          ((LocallyConstantSheaf.smoothFunctor R G Y).obj M) ≫
        (coefficientGlobalCohomologyNatTrans f hf q).app M := by
  have hn := (forgetSupport R G Y q).naturality
    (SmoothDirectImage.coefficientMap f hf M)
  dsimp only [Functor.comp_map] at hn
  simp only [coefficientCohomologyNatTrans_app_eq,
    coefficientGlobalCohomologyNatTrans_app_eq, Functor.map_comp, Category.assoc]
  rw [cohomologyMap_forgetSupport, ← Category.assoc, hn, Category.assoc]

end Langlands.Cohomology.SmoothGodementCohomology.Spatial

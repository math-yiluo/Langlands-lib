import Langlands.Cohomology.SmoothGodement.InvariantSpatial
import Langlands.Cohomology.SmoothGodement.CoefficientSpatial

/-! # Invariant compact spatial maps for full smooth coefficient Godement complexes -/

noncomputable section

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.Cohomology.SmoothGodementCohomology.Spatial

open CategoryTheory HomologicalComplex
open Langlands.Sheaf.Equivariant
open Langlands.Cohomology.SmoothGodementComparison

universe u

variable {R : Type u} [CommRing R] {G : Type u} [Group G]
  [TopologicalSpace G] [IsTopologicalGroup G]
  {X Y Z : Type u} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  [MulAction G X] [MulAction G Y] [MulAction G Z]
  [ContinuousConstSMul G X] [ContinuousConstSMul G Y] [ContinuousConstSMul G Z]
  [HasStableNeighbourhoods G X] [HasStableNeighbourhoods G Y]
  [HasStableNeighbourhoods G Z]
  (f : C(X, Y)) (hf : ∀ (g : G) (x : X), f (g • x) = g • f x)

/-- The actual invariant compact chain pullback on the full smooth coefficient sheaves. -/
def coefficientInvariantCompactNatTrans (hp : IsProperMap f) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙ smoothGodementInvariantCompactComplex R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙ smoothGodementInvariantCompactComplex R G X :=
  Functor.whiskerRight (SmoothDirectImage.coefficientNatTrans f hf)
      (smoothGodementInvariantCompactComplex R G Y) ≫
    Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
      (invariantCompactNatTrans f hf hp)

/-- Its component first resolves the full coefficient map and then applies the
actual proper invariant smooth Godement spatial chain map. -/
theorem coefficientInvariantCompactNatTrans_app (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientInvariantCompactNatTrans f hf hp).app M =
      (smoothGodementInvariantCompactComplex R G Y).map
          (SmoothDirectImage.coefficientMap f hf M) ≫
        invariantCompactMap f hf hp ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := rfl

/-- The coefficient invariant map is degreewise invariants of the constructed
full-coefficient compact chain pullback, without an exactness hypothesis. -/
theorem coefficientInvariantCompactNatTrans_app_eq_map (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientInvariantCompactNatTrans f hf hp).app M =
      ((smoothInvariants R G).mapHomologicalComplex (ComplexShape.up ℕ)).map
        ((coefficientCompactNatTrans f hf hp).app M) := by
  ext n s
  rfl

/-- In every degree this is the actual map of invariant submodules. -/
@[simp]
theorem coefficientInvariantCompactNatTrans_f (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (n : ℕ) :
    ((coefficientInvariantCompactNatTrans f hf hp).app M).f n =
      (smoothInvariants R G).map
        (((coefficientCompactNatTrans f hf hp).app M).f n) := by
  rw [coefficientInvariantCompactNatTrans_app_eq_map]
  rfl

/-- Removing only the invariant witness recovers the original compact chain map. -/
@[simp]
theorem coefficientInvariantCompactNatTrans_apply (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((smoothGodementInvariantCompactComplex R G Y).obj
      ((LocallyConstantSheaf.smoothFunctor R G Y).obj M)).X n) :
    ((((coefficientInvariantCompactNatTrans f hf hp).app M).f n).hom s).val =
      Langlands.SmoothRep.hom
        (((coefficientCompactNatTrans f hf hp).app M).f n) s.val := by
  rw [coefficientInvariantCompactNatTrans_f]
  rfl

/-- Every original coefficient intertwiner gives a commuting chain square. -/
@[reassoc]
theorem coefficientInvariantCompactNatTrans_naturality (hp : IsProperMap f)
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementInvariantCompactComplex R G Y).map a ≫
        (coefficientInvariantCompactNatTrans f hf hp).app N =
      (coefficientInvariantCompactNatTrans f hf hp).app M ≫
        (LocallyConstantSheaf.smoothFunctor R G X ⋙
          smoothGodementInvariantCompactComplex R G X).map a :=
  (coefficientInvariantCompactNatTrans f hf hp).naturality a

/-- The coefficient and direct-image units give identity on invariant complexes. -/
@[simp]
theorem coefficientInvariantCompactNatTrans_id :
    coefficientInvariantCompactNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isProperMap_id =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementInvariantCompactComplex R G X) := by
  apply NatTrans.ext
  funext M
  rw [coefficientInvariantCompactNatTrans_app, SmoothDirectImage.coefficientMap_id]
  exact invariantCompactMap_id _

/-- The actual coefficient pullbacks compose strictly, using the proved
coefficient and spatial equations for the same lax comparison. -/
theorem coefficientInvariantCompactNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) :
    coefficientInvariantCompactNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) =
      coefficientInvariantCompactNatTrans g hg hq ≫ coefficientInvariantCompactNatTrans f hf hp := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientInvariantCompactNatTrans_app,
    SmoothDirectImage.coefficientMap_comp f hf g hg M, Functor.map_comp, Category.assoc]
  rw [invariantCompactMap_comp, invariantCompactMap_naturality_assoc]

/-- Replacing the actual continuous map by an equal one changes no chain map. -/
theorem coefficientInvariantCompactNatTrans_congr {p q : C(X, Y)}
    (hp : ∀ (g : G) (x : X), p (g • x) = g • p x)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (hproper : IsProperMap p) (hproper' : IsProperMap q) (h : p = q) :
    coefficientInvariantCompactNatTrans (R := R) p hp hproper =
      coefficientInvariantCompactNatTrans q hq hproper' := by
  subst q
  rfl

/-- Module homology after invariants of the constructed coefficient compact chain map. -/
def coefficientInvariantCohomologyNatTrans (hp : IsProperMap f) (q : ℕ) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementInvariantCompactCohomology R G Y q ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementInvariantCompactCohomology R G X q :=
  Functor.whiskerRight (coefficientInvariantCompactNatTrans f hf hp)
    (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q)

/-- Each component is the homology of the actual compact chain pullback. -/
theorem coefficientInvariantCohomologyNatTrans_app (hp : IsProperMap f) (q : ℕ)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientInvariantCohomologyNatTrans f hf hp q).app M =
      (homologyFunctor (ModuleCat.{u} R) (ComplexShape.up ℕ) q).map
        ((coefficientInvariantCompactNatTrans f hf hp).app M) := rfl

@[simp]
theorem coefficientInvariantCohomologyNatTrans_id (q : ℕ) :
    coefficientInvariantCohomologyNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isProperMap_id q =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementInvariantCompactCohomology R G X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (ModuleCat.{u} R)
    (ComplexShape.up ℕ) q).map _ = _
  rw [coefficientInvariantCompactNatTrans_id]
  exact (homologyFunctor (ModuleCat.{u} R)
    (ComplexShape.up ℕ) q).map_id _

/-- Strict contravariant composition persists in every homology degree. -/
theorem coefficientInvariantCohomologyNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (q : ℕ) :
    coefficientInvariantCohomologyNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) q =
      coefficientInvariantCohomologyNatTrans g hg hq q ≫
        coefficientInvariantCohomologyNatTrans f hf hp q := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientInvariantCohomologyNatTrans_app,
    coefficientInvariantCompactNatTrans_comp f hf g hg hp hq, Functor.map_comp]

end Langlands.Cohomology.SmoothGodementCohomology.Spatial

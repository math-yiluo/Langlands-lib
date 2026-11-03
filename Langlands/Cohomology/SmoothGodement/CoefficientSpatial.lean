import Langlands.Cohomology.SmoothGodement.Spatial
import Langlands.Sheaf.Equivariant.SmoothDirectImage.Coefficients

/-! # Proper spatial maps on full smooth coefficient Godement complexes -/

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

/-- The actual compact chain pullback on the full smooth coefficient sheaves. -/
def coefficientCompactNatTrans (hp : IsProperMap f) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙ smoothGodementCompactComplex R G Y ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙ smoothGodementCompactComplex R G X :=
  Functor.whiskerRight (SmoothDirectImage.coefficientNatTrans f hf)
      (smoothGodementCompactComplex R G Y) ≫
    Functor.whiskerLeft (LocallyConstantSheaf.smoothFunctor R G X)
      (compactNatTrans f hf hp)

/-- Its component first resolves the full coefficient map and then applies the
actual proper smooth Godement spatial chain map. -/
theorem coefficientCompactNatTrans_app (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientCompactNatTrans f hf hp).app M =
      (smoothGodementCompactComplex R G Y).map
          (SmoothDirectImage.coefficientMap f hf M) ≫
        compactMap f hf hp ((LocallyConstantSheaf.smoothFunctor R G X).obj M) := rfl

/-- The degreewise map is the composite of the two constructed chain components. -/
theorem coefficientCompactNatTrans_f (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (n : ℕ) :
    ((coefficientCompactNatTrans f hf hp).app M).f n =
      ((smoothGodementCompactComplex R G Y).map
          (SmoothDirectImage.coefficientMap f hf M)).f n ≫
        (compactMap f hf hp ((LocallyConstantSheaf.smoothFunctor R G X).obj M)).f n :=
  rfl

/-- On each original compact section, resolve the coefficient pullback, apply
the spatial sheaf map and remove its smooth-image witness. -/
@[simp]
theorem coefficientCompactNatTrans_apply (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) (n : ℕ)
    (s : ((smoothGodementCompactComplex R G Y).obj
      ((LocallyConstantSheaf.smoothFunctor R G Y).obj M)).X n) :
    (Langlands.SmoothRep.hom (((coefficientCompactNatTrans f hf hp).app M).f n) s).val =
      ((((Godement.SmoothSpatial.complexMap f hf
        ((LocallyConstantSheaf.smoothFunctor R G X).obj M)).f n).hom.hom.app
          (Opposite.op ActionOpens.top)).hom
        (Langlands.SmoothRep.hom
          (((smoothGodementCompactComplex R G Y).map
            (SmoothDirectImage.coefficientMap f hf M)).f n) s).val).val := rfl

/-- Degree zero uses the actual smooth Godement zero functor and spatial map. -/
theorem coefficientCompactNatTrans_f_zero (hp : IsProperMap f)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    ((coefficientCompactNatTrans f hf hp).app M).f 0 =
      (smoothSheafCompactSections R G Y).map
          ((Godement.smoothZeroFunctor R G Y).map
            (SmoothDirectImage.coefficientMap f hf M)) ≫
        (smoothSheafCompactSections R G Y).map
          (Godement.SmoothSpatial.zeroMap f hf
            ((LocallyConstantSheaf.smoothFunctor R G X).obj M)) ≫
        (ProperSmoothCompactSections.natTrans f hf hp).app
          ((Godement.smoothZeroFunctor R G X).obj
            ((LocallyConstantSheaf.smoothFunctor R G X).obj M)) := by
  rw [coefficientCompactNatTrans_f, compactMap_f_zero]
  rfl

/-- Every original coefficient intertwiner gives a commuting chain square. -/
@[reassoc]
theorem coefficientCompactNatTrans_naturality (hp : IsProperMap f)
    {M N : Langlands.SmoothRep.{u, u, u} R G} (a : M ⟶ N) :
    (LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementCompactComplex R G Y).map a ≫
        (coefficientCompactNatTrans f hf hp).app N =
      (coefficientCompactNatTrans f hf hp).app M ≫
        (LocallyConstantSheaf.smoothFunctor R G X ⋙
          smoothGodementCompactComplex R G X).map a :=
  (coefficientCompactNatTrans f hf hp).naturality a

/-- The coefficient unit cancels the smooth-direct-image unit at the chain level. -/
@[simp]
theorem coefficientCompactNatTrans_id :
    coefficientCompactNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isProperMap_id =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementCompactComplex R G X) := by
  apply NatTrans.ext
  funext M
  rw [coefficientCompactNatTrans_app, SmoothDirectImage.coefficientMap_id]
  exact compactMap_id _

/-- The actual coefficient pullbacks compose strictly, using the proved
coefficient and spatial equations for the same lax comparison. -/
theorem coefficientCompactNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) :
    coefficientCompactNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) =
      coefficientCompactNatTrans g hg hq ≫ coefficientCompactNatTrans f hf hp := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientCompactNatTrans_app,
    SmoothDirectImage.coefficientMap_comp f hf g hg M, Functor.map_comp, Category.assoc]
  rw [compactMap_comp, compactMap_naturality_assoc]

/-- Replacing the actual continuous map by an equal one changes no chain map. -/
theorem coefficientCompactNatTrans_congr {p q : C(X, Y)}
    (hp : ∀ (g : G) (x : X), p (g • x) = g • p x)
    (hq : ∀ (g : G) (x : X), q (g • x) = g • q x)
    (hproper : IsProperMap p) (hproper' : IsProperMap q) (h : p = q) :
    coefficientCompactNatTrans (R := R) p hp hproper =
      coefficientCompactNatTrans q hq hproper' := by
  subst q
  rfl

/-- Actual smooth-representation homology of the constructed coefficient chain map. -/
def coefficientCohomologyNatTrans (hp : IsProperMap f) (q : ℕ) :
    LocallyConstantSheaf.smoothFunctor R G Y ⋙
        smoothGodementCompactCohomology R G Y q ⟶
      LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementCompactCohomology R G X q :=
  Functor.whiskerRight (coefficientCompactNatTrans f hf hp)
    (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q)

/-- Each component is the homology of the actual compact chain pullback. -/
theorem coefficientCohomologyNatTrans_app (hp : IsProperMap f) (q : ℕ)
    (M : Langlands.SmoothRep.{u, u, u} R G) :
    (coefficientCohomologyNatTrans f hf hp q).app M =
      (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G) (ComplexShape.up ℕ) q).map
        ((coefficientCompactNatTrans f hf hp).app M) := rfl

@[simp]
theorem coefficientCohomologyNatTrans_id (q : ℕ) :
    coefficientCohomologyNatTrans (R := R) (ContinuousMap.id X)
        (fun (_ : G) (_ : X) => rfl) isProperMap_id q =
      𝟙 (LocallyConstantSheaf.smoothFunctor R G X ⋙
        smoothGodementCompactCohomology R G X q) := by
  apply NatTrans.ext
  funext M
  change (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G)
    (ComplexShape.up ℕ) q).map _ = _
  rw [coefficientCompactNatTrans_id]
  exact (homologyFunctor (Langlands.SmoothRep.{u, u, u} R G)
    (ComplexShape.up ℕ) q).map_id _

/-- Strict contravariant composition persists in every homology degree. -/
theorem coefficientCohomologyNatTrans_comp (g : C(Y, Z))
    (hg : ∀ (k : G) (y : Y), g (k • y) = k • g y)
    (hp : IsProperMap f) (hq : IsProperMap g) (q : ℕ) :
    coefficientCohomologyNatTrans (R := R) (g.comp f)
        (fun k x => by change g (f (k • x)) = k • g (f x); rw [hf, hg])
        (hq.comp hp) q =
      coefficientCohomologyNatTrans g hg hq q ≫
        coefficientCohomologyNatTrans f hf hp q := by
  apply NatTrans.ext
  funext M
  simp only [NatTrans.comp_app, coefficientCohomologyNatTrans_app,
    coefficientCompactNatTrans_comp f hf g hg hp hq, Functor.map_comp]

end Langlands.Cohomology.SmoothGodementCohomology.Spatial

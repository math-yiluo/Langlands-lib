/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageOpenRestriction
import WeilConjectures.AlgebraicGeometry.DerivedDirectImageUniformTruncationBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import Mathlib.AlgebraicGeometry.Modules.Tilde
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # A uniform affine bound for canonical truncation projections

Source: Stacks Project, Tags 08D5(2) and 08DZ.
(blueprint: lem-pc-derived-direct-image-uniform-affine-truncation).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

-- Homology, restriction and truncation comparisons require substantial normalization.
-- Exact restriction additivity witnesses need a larger typeclass-search budget.
/-- A single lower truncation works on an affine open for every quasi-coherent
derived object. This is uniform in the object, with no coproduct hypothesis.
Source: Stacks Project, Tag 08D5(2), final truncation argument, and Tag 08DZ.
(blueprint: lem-pc-derived-direct-image-uniform-affine-truncation).

Proof. Restrict f to the inverse image of the affine open U. This is a qcqs morphism
with quasi-compact target. Exact restriction preserves quasi-coherent cohomology.
Use the uniform upper bound N of 08D5(2), not its objectwise truncation clause.
For n >= N-q the upper tail tau_<(-n) of any restricted object has direct image
with zero cohomology in degrees q and q+1: shift the tail by -n-1 and apply N.
The homology sequence of the truncation triangle makes its middle arrow invertible.
Exact restriction commutes with homology and canonical truncation, including the
projection. Derived direct image commutes naturally with open restriction, since
restriction of a K-injective representative remains K-injective (Tag 08BS).
Transport the middle-arrow isomorphism through these natural comparisons. Taking
n = N-q gives one a = -n, independent of the derived object. The assertion includes
zero objects and the empty open and places no compactness requirement on Y. -/
theorem exists_isIso_schemeHigherDirectImage_uniform_truncGE_over_affine
    {X Y : Scheme.{u}} (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (q : ℤ) (U : Y.Opens) (hU : IsAffineOpen U) :
    ∃ a : ℤ, ∀ E : schemeDerivedQCohCategory X,
      IsIso ((SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U).map
        ((schemeHigherDirectImage f q).map
          ((DerivedCategory.TStructure.t.truncGEπ a).app E.obj))) := by
  classical
  let V := f ⁻¹ᵁ U
  let : HasDerivedCategory
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let : HasDerivedCategory
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) :=
    HasDerivedCategory.standard _
  let rX := SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) V
  let eX := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over V))
    (D := SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv V)
  let rY := SheafOfModules.overFunctor.{u} (moduleRings Y.toRingedSpace) U
  let eY := Equivalence.functor
    (C := SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over U))
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let F := rX ⋙ eX
  let G := rY ⋙ eY
  have : rX.Additive := Functor.additive_of_preserves_binary_products _
  have : eX.Additive := Functor.additive_of_preserves_binary_products _
  have : rY.Additive := Functor.additive_of_preserves_binary_products _
  have : eY.Additive := Functor.additive_of_preserves_binary_products _
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have : G.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesFiniteLimits F := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits F := comp_preservesFiniteColimits _ _
  have : PreservesFiniteLimits G := comp_preservesFiniteLimits _ _
  have : PreservesFiniteColimits G := comp_preservesFiniteColimits _ _
  have hres : ∀ E : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty V.toScheme (F.mapDerivedCategory.obj E.obj) := by
    intro E m
    have : ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m).obj E.obj).IsQuasicoherent :=
      E.property m
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) m
    let e := ((Scheme.Modules.overFunctorEquiv V).app (H.obj E.obj)).symm ≪≫
      (F.mapDerivedCategoryHomologyFunctorIso m).app E.obj
    exact (SheafOfModules.isQuasicoherent
      (moduleRings V.toScheme.toRingedSpace)).prop_of_iso e (inferInstance)
  have : IsAffine U.toScheme := hU
  obtain ⟨⟨N, hpos, hN⟩, _⟩ :=
    exists_schemeDerivedDirectImage_uniform_truncation_bound (f ∣_ U)
  let n := N - q
  have hlocal : ∀ E : schemeDerivedQCohCategory X,
      IsIso ((schemeHigherDirectImage (f ∣_ U) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-n)).app
          (F.mapDerivedCategory.obj E.obj))) := by
    intro E
    let K := F.mapDerivedCategory.obj E.obj
    let TX := (DerivedCategory.TStructure.t.truncLT (-n)).obj K
    let RX := moduleRings V.toScheme.toRingedSpace
    let P := SheafOfModules.isQuasicoherent RX
    have hzero : IsZero (SheafOfModules.free (R := RX) PEmpty.{u + 1}) := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply (SheafOfModules.freeHomEquiv _).injective
      funext i
      exact PEmpty.elim i
    have : P.ContainsZero :=
      ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free (R := RX) PEmpty.{u + 1}⟩⟩
    have hTX : DerivedCategory.homologyProperty P TX := by
      have hle := DerivedCategory.homologyProperty_truncLE (hres E) (-n - 1)
      exact (DerivedCategory.homologyProperty P).prop_of_iso
        ((DerivedCategory.TStructure.t.truncLEIsoTruncLT (-n - 1) (-n) (by omega)).app K)
        hle
    have hshift : schemeDerivedQCohProperty V.toScheme (TX⟦-n - 1⟧) :=
      (DerivedCategory.homologyProperty P).le_shift (-n - 1) TX hTX
    have : (TX⟦-n - 1⟧).IsLE 0 :=
      DerivedCategory.TStructure.t.isLE_shift TX (-n - 1) (-n - 1) 0 (by omega)
    have htail (j : ℤ) (hj : N ≤ j + n + 1) :
        IsZero ((schemeHigherDirectImage (f ∣_ U) j).obj TX) := by
      have hz := hN ⟨TX⟦-n - 1⟧, hshift⟩
        (fun m hm ↦ DerivedCategory.isZero_of_isLE _ 0 m hm) (j + n + 1) hj
      let e := (DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) (j + n + 1)).mapIso
          (((schemeDerivedDirectImage (f ∣_ U)).commShiftIso (-n - 1)).app TX) ≪≫
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) 0).shiftIso
          (-n - 1) (j + n + 1) j (by omega)).app
            ((schemeDerivedDirectImage (f ∣_ U)).obj TX)
      exact hz.of_iso e.symm
    let T := (schemeDerivedDirectImage (f ∣_ U)).mapTriangle.obj
      ((DerivedCategory.TStructure.t.triangleLTGE (-n)).obj K)
    have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
      (schemeDerivedDirectImage (f ∣_ U)).map_distinguished _
        (DerivedCategory.TStructure.t.triangleLTGE_distinguished (-n) K)
    change IsIso ((DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) q).map T.mor₂)
    exact DerivedCategory.isIso_homologyMap_mor₂ T hT q (q + 1) rfl
      (htail q (by dsimp [n]; omega)) (htail (q + 1) (by dsimp [n]; omega))
  let c := (schemeDerivedDirectImage_openRestriction f U).some
  let H := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) q
  let HU := DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) q
  let d : schemeHigherDirectImage f q ⋙ G ≅
      F.mapDerivedCategory ⋙ schemeHigherDirectImage (f ∣_ U) q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.mapDerivedCategoryHomologyFunctorIso q) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight c HU ≪≫ Functor.associator _ _ _
  refine ⟨-n, ?_⟩
  intro E
  let p := (DerivedCategory.TStructure.t.truncGEπ (-n)).app E.obj
  have ht : IsIso ((schemeHigherDirectImage (f ∣_ U) q).map
      (F.mapDerivedCategory.map p)) := by
    have : IsIso ((schemeHigherDirectImage (f ∣_ U) q).map
        ((DerivedCategory.TStructure.t.truncGEπ (-n)).app
          (F.mapDerivedCategory.obj E.obj))) := hlocal E
    have : DerivedCategory.TStructure.t.IsGE
        ((DerivedCategory.TStructure.t.truncGE (-n) ⋙ F.mapDerivedCategory).obj E.obj)
        (-n) := F.isGE_mapDerivedCategory_obj
          ((DerivedCategory.TStructure.t.truncGE (-n)).obj E.obj) (-n)
    have hfac : (DerivedCategory.TStructure.t.truncGEπ (-n)).app
        (F.mapDerivedCategory.obj E.obj) ≫
        (F.mapDerivedCategoryTruncGEIso (-n)).inv.app E.obj =
        F.mapDerivedCategory.map p :=
      DerivedCategory.TStructure.t.π_descTruncGE _ _
    rw [← hfac, Functor.map_comp]
    infer_instance
  have hd : IsIso (G.map ((schemeHigherDirectImage f q).map p)) := by
    have heq := d.hom.naturality p
    have : IsIso (G.map ((schemeHigherDirectImage f q).map p) ≫
        d.hom.app ((DerivedCategory.TStructure.t.truncGE (-n)).obj E.obj)) := by
      change IsIso ((schemeHigherDirectImage f q ⋙ G).map p ≫ _)
      rw [heq]
      change IsIso (d.hom.app E.obj ≫
        (schemeHigherDirectImage (f ∣_ U) q).map (F.mapDerivedCategory.map p))
      infer_instance
    exact IsIso.of_isIso_comp_right _
      (d.hom.app ((DerivedCategory.TStructure.t.truncGE (-n)).obj E.obj))
  change IsIso (rY.map ((schemeHigherDirectImage f q).map p))
  exact (isIso_iff_of_reflects_iso _ eY).mp hd

end AlgebraicGeometry

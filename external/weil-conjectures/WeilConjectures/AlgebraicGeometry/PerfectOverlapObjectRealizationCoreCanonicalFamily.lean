/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.PerfectOverlapHomContinuityData
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreBase
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreComparisons
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapObjectRealizationCoreTransport
public import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
public import WeilConjectures.AlgebraicGeometry.PerfectOverlapStageEquivalence
public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionLocalization
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenRestrictionData
import WeilConjectures.AlgebraicGeometry.DerivedPullbackComposition
import WeilConjectures.AlgebraicGeometry.TwoOpenComparisonDiagram
import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionIsoDescent

/-! # Core object comparison data (without the final Hom pin).

Source: Stacks Project, Tags 09RE, 08DW and 0D5S.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data).
-/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u w v h v' h'
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

attribute [local instance] Functor.additive_of_preserves_binary_products
attribute [local instance 2000] openComparisonModuleAbelian openComparisonOverModuleAbelian

/-- The fixed restriction and pullback comparison at each later stage. -/
@[no_expose] noncomputable def perfectOverlapCanonicalComparisonFamily
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E) :
    (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij (fun _ _ ↦ ⟨j, le_rfl⟩)
        U V hcover hU hV A B hA hB E φU φV k hjk := by
  intro k hjk
  let aj : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (c.ι.app j))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])
  let ak : Over.mk (Spec.map (c.ι.app i)) ⟶
      Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) :=
    Over.homMk (Spec.map (c.ι.app k))
      (by dsimp; rw [← Spec.map_comp, c.w (homOfLE (hij.trans hjk))])
  let jk : Over.mk (Spec.map (R.map (homOfLE (hij.trans hjk)))) ⟶
      Over.mk (Spec.map (R.map (homOfLE hij))) :=
    Over.homMk (Spec.map (R.map (homOfLE hjk)))
      (by dsimp; rw [← Spec.map_comp, ← R.map_comp]; rfl)
  have hcomp : ak ≫ jk = aj := by
    ext
    change Spec.map (c.ι.app k) ≫ Spec.map (R.map (homOfLE hjk)) = Spec.map (c.ι.app j)
    rw [← Spec.map_comp, c.w (homOfLE hjk)]
  have hgf : baseChangeMap t ak ≫ baseChangeMap t jk = baseChangeMap t aj := by
    rw [← baseChangeMap_comp, hcomp]
  exact transportDataOfComposite (baseChangeMap t jk) (baseChangeMap t ak)
    (baseChangeMap t aj) hgf U V A B E φU φV

/-- Comparison data for one fixed later stage of the overlap construction.
The construction is the single-stage restriction and pullback comparison from
Tags 09RE and 08DW; the family theorem only packages these independent choices.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data-at).
-/
theorem perfect_overlap_object_realization_core_data_at
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (k : I) (hjk : j ≤ k) :
    Nonempty (perfectOverlapComparisonDataType R c hc i Z t j hij (fun _ _ ↦ ⟨j, le_rfl⟩)
      U V hcover hU hV A B hA hB E φU φV k hjk) := by
  exact ⟨perfectOverlapCanonicalComparisonFamily R c hc i Z t j hij
    U V hcover hU hV A B hA hB E φU φV k hjk⟩

/-- The prescribed overlap comparison data exists simultaneously at every stage.
For each later index, identify the inverse-image intersection with the cartesian
base change of `U ⊓ V`, pull back along this identification, and apply the inverse
open-site equivalence. Restriction and derived-pullback composition comparisons
provide the transport data and theta equations.
(blueprint: lem-pc-perfect-overlap-object-realization-core-data-family).
-/
theorem perfect_overlap_object_realization_core_data_family
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (hc : IsColimit c)
    (i : I) (Z : Scheme.{u}) (t : Z ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation t] [QuasiCompact t] [QuasiSeparated t]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    [∀ (Z : Scheme.{u}) (U : Z.Opens),
      HasDerivedCategory.{w} ((SheafOfModules.{u})
        ((moduleRings Z.toRingedSpace).over U))]
    (j : I) (hij : i ≤ j)
    (U V : (pullback t (Spec.map (R.map (homOfLE hij)))).Opens)
    (hcover : U ⊔ V = ⊤)
    (hU : IsCompact (U : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (hV : IsCompact (V : Set (↥(pullback t (Spec.map (R.map (homOfLE hij)))))))
    (A : schemeDerivedCategory U.toScheme) (B : schemeDerivedCategory V.toScheme)
    (hA : U.toScheme.IsPerfect A) (hB : V.toScheme.IsPerfect B)
    (E : schemeDerivedCategory (pullback t (Spec.map (c.ι.app i))))
    (φU : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ U)).obj A ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E)
    (φV : (derivedPullback (baseChangeMap t
      (T := Over.mk (Spec.map (R.map (homOfLE hij))))
      (T' := Over.mk (Spec.map (c.ι.app i)))
      (Over.homMk (Spec.map (c.ι.app j))
        (by dsimp; rw [← Spec.map_comp, c.w (homOfLE hij)])) ∣_ V)).obj B ≅
      (schemeOpenRestriction _ _).mapDerivedCategory.obj E) :
    Nonempty (Σ _ : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij (fun _ _ ↦ ⟨j, le_rfl⟩)
        U V hcover hU hV A B hA hB E φU φV k hjk, Unit) := by
  classical
  let data : (k : I) → (hjk : j ≤ k) →
      perfectOverlapComparisonDataType R c hc i Z t j hij (fun _ _ ↦ ⟨j, le_rfl⟩)
        U V hcover hU hV A B hA hB E φU φV k hjk := fun k hjk ↦
    Classical.choice (perfect_overlap_object_realization_core_data_at R c hc i Z t j hij
      U V hcover hU hV A B hA hB E φU φV k hjk)
  exact ⟨data, ()⟩

end AlgebraicGeometry


/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedOpenRestrictionMaps
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.OpenRestrictionSupportTriangle
import WeilConjectures.AlgebraicGeometry.SupportedQCohTriangulated
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Topology.Sheaves.Abelian

/-! # A pointwise supported-cone test for the right-adjoint open unit

Source: Stacks Project, Duality for Schemes, Tag 0E4G.
-/

@[expose] public section

set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits
open CategoryTheory.Pretriangulated
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
namespace AlgebraicGeometry

/-- Derived restriction to an open is zero exactly when every cohomology stalk there
is a subsingleton. Exact restriction commutes with homology. The open stalk
isomorphisms give the forward direction, and sheaf section extensionality makes
each restricted homology object zero in the converse. The homology isomorphism
criterion then makes the restricted derived object zero.
Source: Stacks Project, Tag 0E4G, proof of Lemma 48.4.3. -/
theorem restriction_zero_iff_stalks
    (X : Scheme.{u}) (U : X.Opens)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    (K : schemeDerivedCategory X) :
    IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj K) ↔
      ∀ (n : ℤ) (x : X), x ∈ U →
        Subsingleton (↑(TopCat.Presheaf.stalk ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K).val.presheaf x)) :=
  set_option synthInstance.maxSize 2048 in by
  let : Zero (schemeDerivedCategory U.toScheme) := HasZeroObject.zero' _
  let L := schemeOpenRestriction X U
  constructor
  · intro hK n x hx
    let H := (DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
    have hLH : IsZero (L.obj H) :=
      ((DerivedCategory.homologyFunctor _ n).map_isZero hK).of_iso
        ((L.mapDerivedCategoryHomologyFunctorIso n).app K)
    let e : L.obj H ≅ (Scheme.Modules.restrictFunctor U.ι).obj H :=
      (Scheme.Modules.overFunctorEquiv U).app H
    have hRH := hLH.of_iso e.symm
    let F := Scheme.Modules.toPresheaf U.toScheme ⋙
      TopCat.Presheaf.stalkFunctor AddCommGrpCat.{u} (⟨x, hx⟩ : U)
    have : (Scheme.Modules.toPresheaf U.toScheme).Additive := ⟨by intros; rfl⟩
    have : F.Additive := by dsimp [F]; infer_instance
    have hz := F.map_isZero hRH
    let eStalk := (Scheme.Modules.restrictStalkNatIso U.ι (⟨x, hx⟩ : U)).app H
    exact AddCommGrpCat.subsingleton_of_isZero (hz.of_iso eStalk.symm)
  · intro hK
    have hz (n : ℤ) : IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace)) n).obj
          (L.mapDerivedCategory.obj K)) := by
      let H := (DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) n).obj K
      have hR : IsZero ((SheafOfModules.overFunctor.{u}
          (moduleRings X.toRingedSpace) U).obj H) := by
        apply (IsZero.iff_id_eq_zero _).mpr
        ext V z
        change z = 0
        apply TopCat.Presheaf.section_ext
          ((SheafOfModules.toSheaf (moduleRings X.toRingedSpace)).obj H)
        intro x hx
        change TopCat.Presheaf.germ H.val.presheaf _ x hx _ =
          TopCat.Presheaf.germ H.val.presheaf _ x hx _
        exact (hK n x (leOfHom V.unop.hom hx)).elim _ _
      have hLH : IsZero (L.obj H) :=
        (Scheme.Modules.overEquiv U).functor.map_isZero hR
      exact hLH.of_iso ((L.mapDerivedCategoryHomologyFunctorIso n).app K).symm
    have hi : IsIso (0 : L.mapDerivedCategory.obj K ⟶ 0) :=
      (DerivedCategory.isIso_iff _ _).mpr (fun n ↦
        IsZero.isIso (hz n) ((DerivedCategory.homologyFunctor _ n).map_isZero
          (isZero_zero _)) _)
    exact (isZero_zero _).of_iso (asIso (0 : L.mapDerivedCategory.obj K ⟶ 0))

private instance qcoh_tri (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    (schemeDerivedQCohProperty Z).IsTriangulated := by
  simpa [supportedProperty] using supported_qcoh_isTriangulated Z Set.univ

private instance qcoh_iso (Z : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))] :
    (schemeDerivedQCohProperty Z).IsClosedUnderIsomorphisms where
  of_iso e hK n := (SheafOfModules.isQuasicoherent (moduleRings Z.toRingedSpace)).prop_of_iso
    ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK n)

/-- The unit at one object is tested by the restricted image of its supported cone.
Source: Stacks Project, Tag 0E4G, proof of Lemma 48.4.3(1)--(2).
(blueprint: lem-sc-right-adjoint-open-unit-cone-test).

Proof. Complete the specified unit K → Rj_*j^*K to a distinguished triangle
in the quasi-coherent derived category. The open-restriction support triangle
shows that its cone Q restricts to zero, and is bounded below when K is. This
applies to the supplied adjunction: uniqueness of adjoints identifies its unit
with the unit constructed from restriction/direct image, up to an invertible
map of the second vertex; transport the triangle across this isomorphism.
Quasi-coherent derived categories are triangulated. The lift of Rf_* is exact,
so its right adjoint a has the adjoint shift structure and is exact. Apply a,
the ambient inclusion, and restriction to U to this triangle. In a distinguished
triangle the first arrow is invertible exactly when the third vertex is zero.
This is the asserted pointwise test. The same cone handles the bounded and
unbounded cases; for V empty or all of Y the construction and the triangle
criterion are unchanged. -/
theorem rightAdjoint_open_unit_cone_test
    {X Y : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) (V : Y.Opens) (hV : IsCompact (V : Set Y))
    (U : X.Opens) (_hU : U = f ⁻¹ᵁ V)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings V.toScheme.toRingedSpace))]
    (hpush : ∀ K : schemeDerivedQCohCategory X,
      schemeDerivedQCohProperty Y ((schemeDerivedDirectImage f).obj K.obj))
    (a : schemeDerivedQCohCategory Y ⥤ schemeDerivedQCohCategory X)
    (adj : (schemeDerivedQCohProperty Y).lift
      ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush ⊣ a)
    (adjOpen : (schemeOpenRestriction Y V).mapDerivedCategory ⊣ schemeDerivedDirectImage
          V.ι)
    (hopen : ∀ K : schemeDerivedQCohCategory Y,
      schemeDerivedQCohProperty Y
        ((schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj)))
    (K : schemeDerivedQCohCategory Y) :
    ∃ Q : schemeDerivedQCohCategory Y,
      IsZero ((schemeOpenRestriction Y V).mapDerivedCategory.obj Q.obj) ∧
      ((∃ n : ℤ, K.obj.IsGE n) → ∃ n : ℤ, Q.obj.IsGE n) ∧
      (IsIso ((schemeOpenRestriction X U).mapDerivedCategory.map
      ((schemeDerivedQCohProperty X).ι.map (a.map (ObjectProperty.homMk (X := K)
        (Y := ⟨(schemeDerivedDirectImage V.ι).obj
          ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj), hopen K⟩)
        (adjOpen.unit.app K.obj))))) ↔
        IsZero ((schemeOpenRestriction X U).mapDerivedCategory.obj (a.obj Q).obj)) := by
  classical
  obtain ⟨ra, Q, β, δ, hT, hM, hQ, hsupp, hbound⟩ :=
    openRestriction_support_triangle Y V hV K.obj K.property
  let e := (schemeDerivedDirectImage V.ι).mapIso ((ra.leftAdjointUniq adjOpen).app K.obj)
  let M : schemeDerivedQCohCategory Y :=
    ⟨(schemeDerivedDirectImage V.ι).obj
      ((schemeOpenRestriction Y V).mapDerivedCategory.obj K.obj), hopen K⟩
  let q : schemeDerivedQCohCategory Y := ⟨Q, hQ⟩
  let t : Triangle (schemeDerivedQCohCategory Y) :=
    Triangle.mk (ObjectProperty.homMk (X := K) (Y := M) (adjOpen.unit.app K.obj))
      (ObjectProperty.homMk (X := M) (Y := q) (e.inv ≫ β))
      (ObjectProperty.homMk (X := q) (Y := K⟦(1 : ℤ)⟧)
        (δ ≫ ((schemeDerivedQCohProperty Y).ι.commShiftIso (1 : ℤ)).inv.app K))
  have ht : t ∈ distTriang (schemeDerivedQCohCategory Y) := by
    change (schemeDerivedQCohProperty Y).ι.mapTriangle.obj t ∈ distTriang _
    apply (distinguished_iff_of_iso
      (Triangle.isoMk (Triangle.mk (ra.unit.app K.obj) β δ)
        ((schemeDerivedQCohProperty Y).ι.mapTriangle.obj t)
        (Iso.refl _) e (Iso.refl _) ?_ ?_ ?_)).mp hT
    · simp [Functor.mapTriangle, Triangle.mk, t, e]
    · simp [Functor.mapTriangle, Triangle.mk, t]
    · simp [Functor.mapTriangle, Triangle.mk, t]
  let F := (schemeDerivedQCohProperty Y).lift
    ((schemeDerivedQCohProperty X).ι ⋙ schemeDerivedDirectImage f) hpush
  let : F.CommShift ℤ := inferInstance
  have : F.IsTriangulated := inferInstance
  let : a.CommShift ℤ := adj.rightAdjointCommShift ℤ
  have : adj.CommShift ℤ := adj.commShift_of_leftAdjoint ℤ
  have : a.IsTriangulated := adj.isTriangulated_rightAdjoint
  let G := a ⋙ (schemeDerivedQCohProperty X).ι ⋙
    (schemeOpenRestriction X U).mapDerivedCategory
  have : G.IsTriangulated := inferInstance
  refine ⟨q, (restriction_zero_iff_stalks Y V Q).mpr hsupp, hbound, ?_⟩
  exact (Triangle.isZero₃_iff_isIso₁ (G.mapTriangle.obj t) (G.map_distinguished t ht)).symm

end AlgebraicGeometry

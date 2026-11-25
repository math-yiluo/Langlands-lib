/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import WeilConjectures.Topology.RingedSpaceModuleCohomology
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound

/-! # Affine sections and the canonical lower truncation

Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5, and Tag 08D4.
(blueprint: new-affine-derived-sections-truncation-iso).
-/

@[expose] public section

universe u wA wY
open CategoryTheory
namespace AlgebraicGeometry

/-- The lower-truncation projection is invertible on derived affine sections
in its cutoff degree.
Source: Stacks Project, Tag 06Z0, proof of Lemma 36.3.5; Tag 08D4 (3).
(blueprint: new-affine-derived-sections-truncation-iso).

Proof: Let S be global sections followed by scalar transport through ΓSpecIso.
Sections is right adjoint to tilde and preserves products. Scalar transport along
this ring isomorphism is exact and preserves products. Affine vanishing gives
R^p S(M) = 0 for quasi-coherent M and p >= 1; after the exact conservative
forgetful functor to abelian groups, apply the unbounded cohomological bound
with N = 1 to the strictly lower truncation of K at n. Truncation preserves
quasi-coherent cohomology. This truncation is supported in degrees <= n - 1,
so its derived sections have zero cohomology in degrees n and n + 1.
Apply derived sections to the canonical truncation triangle. The homology
exact sequence now makes H^n of its projection K -> truncGE n K invertible.
Conservativity of forgetting modules detects invertibility before forgetting.
These are the canonical maps, so the conclusion concerns the stated projection.
The zero ring and zero complex require no exception, and K is unbounded. -/
theorem affineDerivedSections_truncGE_isIso (A : Type u) [CommRing A]
    [HasDerivedCategory.{wA} (ModuleCat.{u} A)]
    [HasDerivedCategory.{wY}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (K : schemeDerivedQCohCategory (Spec (.of A))) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
      ((RingedSpace.globalSectionsFunctor (Spec (.of A)).toRingedSpace ⋙
          ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom).rightDerivedFunctor.map
        ((DerivedCategory.TStructure.t.truncGEπ n).app K.obj))) := by
  let X := Spec (.of A)
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let S := RingedSpace.globalSectionsFunctor X.toRingedSpace ⋙
    ModuleCat.restrictScalars (Scheme.ΓSpecIso (.of A)).inv.hom
  let V := forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}
  let F := S ⋙ V
  let : HasDerivedCategory AddCommGrpCat.{u} := HasDerivedCategory.standard _
  have : Limits.PreservesLimitsOfShape (Discrete ℕ)
      (ModuleCat.restrictScalars.{u} (Scheme.ΓSpecIso (.of A)).inv.hom) :=
    ⟨fun {_} ↦ inferInstance⟩
  have : Limits.PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp [F, S, RingedSpace.globalSectionsFunctor]
    infer_instance
  have hN (M : C) (hM : M.IsQuasicoherent) (p : ℕ) (hp : 1 ≤ p) :
      Limits.IsZero ((F.rightDerived p).obj M) := by
    have := hM
    have : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).obj M) :=
      subsingleton_openModuleCohomology_of_isAffineOpen X M ⊤ (isAffineOpen_top X) p
        (by omega)
    change Limits.IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p ⊤).obj M)
    exact AddCommGrpCat.isZero_of_subsingleton _
  let t := DerivedCategory.TStructure.t (C := C)
  let E := (t.truncLT n).obj K.obj
  let P := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hzero : Limits.IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{u + 1}) := by
    apply (Limits.IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : P.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  have hE : schemeDerivedQCohProperty X E := by
    have hle := DerivedCategory.homologyProperty_truncLE K.property (n - 1)
    exact (DerivedCategory.homologyProperty P).prop_of_iso
      ((t.truncLEIsoTruncLT (n - 1) n (by omega)).app K.obj) hle
  have hz (i : ℤ) (hi : n ≤ i) : Limits.IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).obj
        (F.rightDerivedFunctor.obj E)) := by
    apply isZero_homology_rightDerivedFunctor_of_cohomological_bound
      X F 1 hN (n - 1) E hE
      (fun j hj ↦ DerivedCategory.isZero_of_isLE E (n - 1) j hj) i
    omega
  let T := F.rightDerivedFunctor.mapTriangle.obj ((t.triangleLTGE n).obj K.obj)
  have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    F.rightDerivedFunctor.map_distinguished _ (t.triangleLTGE_distinguished n K.obj)
  have hi : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} n).map T.mor₂) :=
    DerivedCategory.isIso_homologyMap_mor₂ T hT n (n + 1) rfl
      (hz n le_rfl) (hz (n + 1) (by omega))
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} n
  let e : F.rightDerivedFunctor ⋙ H ≅
      S.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} A) n ⋙ V :=
    Functor.isoWhiskerRight
      (S.rightDerivedFunctorCompMapDerivedCategoryIso V) H ≪≫
    Functor.isoWhiskerLeft S.rightDerivedFunctor (V.mapDerivedCategoryHomologyFunctorIso n).symm
  have hj := (NatIso.isIso_map_iff e ((t.truncGEπ n).app K.obj)).1 hi
  change IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).map
    (S.rightDerivedFunctor.map ((t.truncGEπ n).app K.obj)))
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ V hj _

end AlgebraicGeometry

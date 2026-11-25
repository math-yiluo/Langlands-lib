/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedSectionPresheaf
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure


import WeilConjectures.AlgebraicGeometry.QCohInverseAffineOpenVanishing
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated
import Mathlib.Algebra.Category.Grp.Zero
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits

/-! # Affine-open invertibility of the derived sections truncation projection

Source: Stacks Project, Tags 08D4 (3), 08D5 and 01F4 (2).
(blueprint: new-qcoh-sections-truncation-projection).
-/

@[expose] public section

universe u wX wY

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- On affine opens, the canonical projection to the lower truncation at i
induces an isomorphism on degree-i derived sections for quasi-coherent objects.
This only compares E with its lower truncation, not with its cohomology sheaf.
Source: Stacks Project, Tags 08D4 (3), 08D5 and 01F4 (2).
(blueprint: new-qcoh-sections-truncation-projection).

Proof:
1. For an affine V in Y, put U = f inverse-image V. Restriction of injective
resolutions computes cohomology on U. Open restriction commutes with derived
pushforward, so hacyc kills positive direct images for the restricted morphism.
Its higher direct images of quasi-coherent sheaves are quasi-coherent, by the
quasi-coherence clause of finite-support-hi. Affine vanishing on V and the
Leray edge identify H^p(U,F|U) with sections of R^p(f|V)_*(F|U), hence zero
for p > 0. Sections preserve countable products by their universal property.
2. The strictly lower truncation T = truncLT i E has quasi-coherent cohomology
and is supported in degrees at most i-1. Apply the unbounded cohomological
bound with N = 1 to the sections functor on U, followed by forgetting modules.
Its derived cohomology vanishes in degrees i and i+1.
3. Apply derived sections to the distinguished truncation triangle
T -> E -> truncGE i E -> T[1]. The homology exact sequence and the two zero
endpoints make the stated canonical projection invertible after evaluation
at V. Exact evaluation identifies this homology with evaluated derived-section
presheaf homology; forgetting modules reflects isomorphisms. Evaluation at all
affine opens jointly reflects isomorphisms of module presheaves, giving the claim.
The argument applies to every integer and includes the zero object and empty
open; it never assumes that U is affine or that E is bounded below. -/
theorem qcoh_acyclic_derived_sections_truncation_isIso {X Y : Scheme.{u}}
    [HasDerivedCategory.{wX} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wY} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (f : X ⟶ Y) [QuasiCompact f] [QuasiSeparated f]
    (hacyc : ∀ (F : SheafOfModules.{u} (moduleRings X.toRingedSpace)),
      F.IsQuasicoherent → ∀ (p : ℤ), 0 < p →
        IsZero ((schemeModuleHigherDirectImage f p).obj F))
    (i : ℤ) (E : schemeDerivedQCohCategory X) :
    IsIso ((PresheafOfModules.pushforward₀
      (ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V))
      (moduleRings Y.toRingedSpace).obj).map
        ((schemeDerivedSectionPresheaf f i).map
          ((DerivedCategory.TStructure.t.truncGEπ i).app E.obj))) := by
  let C := SheafOfModules.{u} (moduleRings X.toRingedSpace)
  let D := PresheafOfModules.{u} (moduleRings Y.toRingedSpace).obj
  let S := RingedSpace.moduleDirectImage f.toLRSHom.toShHom ⋙
    SheafOfModules.forget (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard D
  let := HasDerivedCategory.standard AddCommGrpCat.{u}
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  let t := DerivedCategory.TStructure.t (C := C)
  let K := (t.truncLT i).obj E.obj
  let Q := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hzero : IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{u + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext j
    exact PEmpty.elim j
  have : Q.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{u + 1}⟩⟩
  have hK : schemeDerivedQCohProperty X K := by
    have hle := DerivedCategory.homologyProperty_truncLE E.property (i - 1)
    exact (DerivedCategory.homologyProperty Q).prop_of_iso
      ((t.truncLEIsoTruncLT (i - 1) i (by omega)).app E.obj) hle
  let T := PresheafOfModules.toPresheaf.{u}
    ((ObjectProperty.ι (fun V : Y.Opens ↦ IsAffineOpen V)).op ⋙
      (moduleRings Y.toRingedSpace).obj)
  apply (isIso_iff_of_reflects_iso _ T).mp
  rw [NatTrans.isIso_iff_isIso_app]
  intro V
  let v := V.unop.obj
  let A := PresheafOfModules.evaluation (moduleRings Y.toRingedSpace).obj
      (Opposite.op v) ⋙ forget₂ _ AddCommGrpCat.{u}
  let F := S ⋙ A
  have : F.Additive := by dsimp [F, S, A]; infer_instance
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    change PreservesLimitsOfShape (Discrete ℕ)
      (RingedSpace.openModuleSections X.toRingedSpace (f ⁻¹ᵁ v))
    dsimp [RingedSpace.openModuleSections]
    infer_instance
  have hN (M : C) (hM : M.IsQuasicoherent) (p : ℕ) (hp : 1 ≤ p) :
      IsZero ((F.rightDerived p).obj M) := by
    change IsZero
      ((RingedSpace.openModuleCohomology X.toRingedSpace p (f ⁻¹ᵁ v)).obj M)
    exact qcoh_acyclic_inverse_affine_open_vanishing f hacyc v V.unop.property M hM p
      (by omega)
  have hz (j : ℤ) (hj : i ≤ j) : IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} j).obj
        (F.rightDerivedFunctor.obj K)) := by
    apply isZero_homology_rightDerivedFunctor_of_cohomological_bound
      X F 1 hN (i - 1) K hK
      (fun n hn ↦ DerivedCategory.isZero_of_isLE K (i - 1) n hn) j
    omega
  let Δ := F.rightDerivedFunctor.mapTriangle.obj ((t.triangleLTGE i).obj E.obj)
  have hΔ : Δ ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    F.rightDerivedFunctor.map_distinguished _ (t.triangleLTGE_distinguished i E.obj)
  have hi : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{u} i).map Δ.mor₂) :=
    DerivedCategory.isIso_homologyMap_mor₂ Δ hΔ i (i + 1) rfl
      (hz i le_rfl) (hz (i + 1) (by omega))
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} i
  have : S.Additive := by dsimp [S]; infer_instance
  let c : F.rightDerivedFunctor ≅ S.rightDerivedFunctor ⋙ A.mapDerivedCategory :=
    F.rightDerivedFunctorIsoKInjectives ≪≫
    Functor.isoWhiskerLeft
      ((HomotopyCategory.KInjectives.equivalence C).inverse ⋙ ObjectProperty.ι _)
      (Functor.isoWhiskerRight
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (S ⋙ A)) (ComplexShape.up ℤ)).symm
        DerivedCategory.Qh ≪≫
        Functor.isoWhiskerLeft (S.mapHomotopyCategory (ComplexShape.up ℤ))
          A.mapDerivedCategoryFactorsh.symm) ≪≫
    Functor.isoWhiskerRight S.rightDerivedFunctorIsoKInjectives.symm A.mapDerivedCategory
  let e : F.rightDerivedFunctor ⋙ H ≅
      S.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor D i ⋙ A :=
    Functor.isoWhiskerRight c H ≪≫
    Functor.isoWhiskerLeft S.rightDerivedFunctor (A.mapDerivedCategoryHomologyFunctorIso i).symm
  exact (NatIso.isIso_map_iff e ((t.truncGEπ i).app E.obj)).1 hi

end AlgebraicGeometry

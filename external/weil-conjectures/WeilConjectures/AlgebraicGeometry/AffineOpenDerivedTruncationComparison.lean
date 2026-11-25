/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
import WeilConjectures.AlgebraicGeometry.AffineOpenModuleCohomologyVanishing
import WeilConjectures.AlgebraicGeometry.UnboundedDerivedFunctorCohomologicalBound
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.Grp.Zero
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.AB
import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
import WeilConjectures.Mathlib.Algebra.Homology.DerivedCategory.HomologyProperty
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Triangulated

/-! # The derived truncation comparison on an affine open

Source: Stacks Project, Tag 08D4, parts (1)--(3), and Tag 0AVW.
(blueprint: lem-sc-affine-open-derived-truncation-comparison).
-/

@[expose] public section
universe v w w'
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace AlgebraicGeometry

/-- Derived sections on an affine open send the canonical lower-truncation
projection to an isomorphism on cohomology in its cutoff degree.
Source: Stacks Project, Tag 08D4 with N = 1; Tag 0AVW, cohomology calculation.
(blueprint: lem-sc-affine-open-derived-truncation-comparison).

Proof: Let F be evaluation at U followed by forgetting the scalar action.
Sections commute with countable products, since limits of module sheaves are
computed sectionwise. Affine-open module cohomology vanishing gives R^pF(M) = 0
for quasi-coherent M and p >= 1. Put K = Q(I). Quasi-coherence of its homology
follows from the homology factorization through Q. The strictly lower truncation
E = truncLT n K still has quasi-coherent homology and is supported in degrees at
most n-1. Apply the unbounded cohomological bound with N = 1 to E. This gives
H^n(RF(E)) = 0 and H^(n+1)(RF(E)) = 0. Apply RF to the distinguished triangle
E to K to truncGE n K. Its long exact sequence makes the displayed projection
invertible after forgetting scalars. Exact forgetting commutes with right derived
functors and homology, and reflects isomorphisms, giving invertibility over
O_X(U). All comparisons are natural and preserve the specified projection.
No K-injectivity or boundedness of I is required. Zero complexes, empty affine
opens, and all integer degrees satisfy the same argument. -/
theorem affine_open_derived_truncation_comparison
    (X : Scheme.{v})
    [HasDerivedCategory.{w} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    (U : X.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{w'}
      (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op U)))]
    (I : CochainComplex (SheafOfModules.{v} (moduleRings X.toRingedSpace)) ℤ)
    (hI : ∀ n : ℤ, (I.homology n).IsQuasicoherent) (n : ℤ) :
    IsIso ((DerivedCategory.homologyFunctor
      (ModuleCat.{v} ((moduleRings X.toRingedSpace).obj.obj (op U))) n).map
        ((SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
          PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj
            (op U)).rightDerivedFunctor.map
          ((DerivedCategory.TStructure.t.truncGEπ n).app (DerivedCategory.Q.obj I)))) := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let S := SheafOfModules.forget (moduleRings X.toRingedSpace) ⋙
    PresheafOfModules.evaluation (moduleRings X.toRingedSpace).obj (op U)
  let V := forget₂ (ModuleCat.{v}
    ((moduleRings X.toRingedSpace).obj.obj (op U))) AddCommGrpCat.{v}
  let F := S ⋙ V
  let : HasDerivedCategory AddCommGrpCat.{v} := HasDerivedCategory.standard _
  have : EnoughInjectives C :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  have : PreservesLimitsOfShape (Discrete ℕ) F := by
    dsimp [F, S, V]
    infer_instance
  have hN (M : C) (hM : M.IsQuasicoherent) (p : ℕ) (hp : 1 ≤ p) :
      IsZero ((F.rightDerived p).obj M) := by
    have := hM
    have : Subsingleton ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj M) :=
      subsingleton_openModuleCohomology_of_isAffineOpen X M U hU p (by omega)
    change IsZero ((RingedSpace.openModuleCohomology X.toRingedSpace p U).obj M)
    exact AddCommGrpCat.isZero_of_subsingleton _
  let K := DerivedCategory.Q.obj I
  let t := DerivedCategory.TStructure.t (C := C)
  let E := (t.truncLT n).obj K
  let P := SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)
  have hK : schemeDerivedQCohProperty X K := by
    intro i
    exact P.prop_of_iso ((DerivedCategory.homologyFunctorFactors C i).app I).symm (hI i)
  have hzero : IsZero (SheafOfModules.free (R := moduleRings X.toRingedSpace)
      PEmpty.{v + 1}) := by
    apply (IsZero.iff_id_eq_zero _).mpr
    apply (SheafOfModules.freeHomEquiv _).injective
    funext i
    exact PEmpty.elim i
  have : P.ContainsZero :=
    ⟨⟨_, hzero, SheafOfModules.isQuasicoherent_free PEmpty.{v + 1}⟩⟩
  have hE : schemeDerivedQCohProperty X E := by
    have hle := DerivedCategory.homologyProperty_truncLE hK (n - 1)
    exact (DerivedCategory.homologyProperty P).prop_of_iso
      ((t.truncLEIsoTruncLT (n - 1) n (by omega)).app K) hle
  have hz (i : ℤ) (hi : n ≤ i) : IsZero
      ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} i).obj
        (F.rightDerivedFunctor.obj E)) := by
    apply isZero_homology_rightDerivedFunctor_of_cohomological_bound
      X F 1 hN (n - 1) E hE
      (fun j hj ↦ DerivedCategory.isZero_of_isLE E (n - 1) j hj) i
    omega
  let T := F.rightDerivedFunctor.mapTriangle.obj ((t.triangleLTGE n).obj K)
  have hT : T ∈ CategoryTheory.Pretriangulated.distinguishedTriangles :=
    F.rightDerivedFunctor.map_distinguished _ (t.triangleLTGE_distinguished n K)
  have hi : IsIso ((DerivedCategory.homologyFunctor AddCommGrpCat.{v} n).map T.mor₂) :=
    DerivedCategory.isIso_homologyMap_mor₂ T hT n (n + 1) rfl
      (hz n le_rfl) (hz (n + 1) (by omega))
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{v} n
  let e : F.rightDerivedFunctor ⋙ H ≅
      S.rightDerivedFunctor ⋙ DerivedCategory.homologyFunctor _ n ⋙ V :=
    Functor.isoWhiskerRight
      (S.rightDerivedFunctorCompMapDerivedCategoryIso V) H ≪≫
    Functor.isoWhiskerLeft S.rightDerivedFunctor (V.mapDerivedCategoryHomologyFunctorIso n).symm
  have hj := (NatIso.isIso_map_iff e ((t.truncGEπ n).app K)).1 hi
  exact @isIso_of_reflects_iso _ _ _ _ _ _ _ V hj _

end AlgebraicGeometry

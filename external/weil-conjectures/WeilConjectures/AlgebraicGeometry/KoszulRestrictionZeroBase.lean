/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.KoszulBasicOpenExact
import WeilConjectures.AlgebraicGeometry.OpenCoverRestrictionExact
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits TopologicalSpace
namespace AlgebraicGeometry
/-- Unshifted restriction of the sheafified Koszul complex is zero on the union of
basic opens. This is the contraction and sheaf gluing argument of Stacks Tags 09IR
and 0663, before applying the derived-category shift.
(blueprint: lem-pc-koszul-restriction-zero-base). -/
theorem isZero_restrict_koszul_base
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat))))) := by
  let := HasZeroObject.zero' (C := CochainComplex
    (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ)
  let K := (@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
    (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
    _ _ _ _ (tilde.functor (.of A))
    ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
    ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat)
  let F := SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U
  let L := (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K
  have hL : L.Acyclic := by
    intro n
    exact exactAt_over_of_open_cover (Spec (.of A)) K (Fin r)
      (fun i ↦ PrimeSpectrum.basicOpen (f i)) U hU n
      (fun i ↦ koszul_basicOpen_exact A r f i n)
  let z : (0 : CochainComplex
    (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ) ⟶ L := 0
  have : QuasiIso z := by
    rw [quasiIso_iff]
    intro n
    exact (quasiIsoAt_iff_exactAt z n
      (HomologicalComplex.acyclic_of_isZero _ (isZero_zero _) n)).2 (hL n)
  have hz := DerivedCategory.Q.map_isZero (isZero_zero
    (CochainComplex
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U)) ℤ))
  have hQ : IsZero (DerivedCategory.Q.obj L) := hz.of_iso (asIso (DerivedCategory.Q.map z)).symm
  exact hQ.of_iso (F.mapDerivedCategoryFactors.app K)
end AlgebraicGeometry

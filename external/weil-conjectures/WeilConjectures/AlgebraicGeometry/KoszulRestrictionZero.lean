/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DerivedCategory
public import WeilConjectures.AlgebraicGeometry.KoszulComplex
import WeilConjectures.AlgebraicGeometry.KoszulRestrictionZeroBase
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.Embedding.CochainComplex

/-! # Koszul complexes vanish on the basic-open complement
Source: Stacks Project, Tag 09IR.
(blueprint: lem-pc-koszul-restriction-zero).
-/

@[expose] public section

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry

/-- All shifts of the sheafified Koszul complex vanish on the union of the basic opens.
Source: Stacks Project, Tag 09IR, proof of lemma-orthogonal-koszul-complex;
Tag 0663, null-homotopy of multiplication by a Koszul generator.
(blueprint: lem-pc-koszul-restriction-zero).

Proof: On D(f_i), multiplication by f_i is invertible. Exterior multiplication by
f_i⁻¹ times the i-th basis vector contracts the Koszul complex: contraction with f
composed with this homotopy, plus the reverse composition, is the identity.
The basic opens cover U, so the restricted complex has zero cohomology sheaves.
Exact open restriction commutes with sheafification, localization and shifts.
Consequently its image in the derived category is zero in every shift.
For r = 0 the union is empty and the restricted category is zero; the zero ring
also has empty spectrum. No regularity or nonzeroness of the f_i is required. -/
theorem isZero_restrict_shift_koszul
    (A : Type u) [CommRing A] (r : ℕ) (f : Fin r → A)
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))]
    (U : (Spec (.of A)).Opens)
    (hU : U = ⨆ i : Fin r, PrimeSpectrum.basicOpen (f i))
    [HasDerivedCategory.{w}
      (SheafOfModules.{u} ((moduleRings (Spec (.of A)).toRingedSpace).over U))]
    (n : ℤ) :
    IsZero ((SheafOfModules.overFunctor.{u}
      (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory.obj
      ((DerivedCategory.Q.obj
          ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
            (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
            _ _ _ _ (tilde.functor (.of A))
            ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
            ((ExteriorAlgebra.koszulComplex A r f).extend
              ComplexShape.embeddingDownNat)))⟦n⟧)) := by
  let L := (SheafOfModules.overFunctor.{u}
    (moduleRings (Spec (.of A)).toRingedSpace) U).mapDerivedCategory
  let K : DerivedCategory (SheafOfModules.{u}
      (moduleRings (Spec (.of A)).toRingedSpace)) :=
    (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec (.of A)).toRingedSpace))
        _ _ _ _ (tilde.functor (.of A)) ⟨fun _ _ ↦ tilde.map_zero⟩
        (ComplexShape.up ℤ)).obj
        ((ExteriorAlgebra.koszulComplex A r f).extend ComplexShape.embeddingDownNat)))
  have hz : IsZero (L.obj K) := isZero_restrict_koszul_base A r f U hU
  exact (Functor.map_isZero (shiftFunctor _ n) hz).of_iso ((L.commShiftIso n).app K)

end AlgebraicGeometry

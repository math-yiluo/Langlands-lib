/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import WeilConjectures.AlgebraicGeometry.ShiftedKoszulAugmentation
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnitPerfect
import WeilConjectures.AlgebraicGeometry.AffinePerfectKoszulPrincipalUnitIso

/-! # Powers Koszul complexes are perfect on a principal-open cover

Source: Stacks Project, Tag 08CX, Section 36.9
(blueprint: lem-sc-affine-perfect-koszul-principal-unit).
-/

@[expose] public section

universe a b

open CategoryTheory

namespace AlgebraicGeometry

/-- The object associated to the shifted Koszul complex on powers of a finite
sequence is perfect; its canonical augmentation restricts to an isomorphism on
the union of the principal opens. Source: Stacks, Tag 08CX
(blueprint: lem-sc-affine-perfect-koszul-principal-unit).

Proof:
1. The Koszul terms are finite free exterior powers and vanish above degree `r`
   (`def-weil-pbc-koszul-complex`). Deleting degree zero and negating the
   differential leaves a bounded finite free complex. Its associated sheaf is
   strictly perfect, hence its derived object is perfect
   (`lemma-coherent-base-change-invertible-sheaves--1`).
2. On `D(f i)`, the element `(f i)^e` is invertible. Exterior multiplication by
   `(f i)^(-e) e_i` contracts the localized Koszul complex: the differential's
   formula gives `dh + hd = id` (Stacks, Tags 0626 and 0663). The Koszul triangle
   therefore makes the augmentation a quasi-isomorphism on this open.
3. These opens cover their union. Being an isomorphism in the derived category
   is local, so the restricted augmentation is an isomorphism on the union.
   The empty family gives the empty open; the one-element family gives the usual
   two-term contracting homotopy. -/
theorem affine_perfect_koszul_principal_unit
    (A : Type a) [CommRing A] (r : ℕ) (f : Fin r → A) (e : ℕ) (he : 1 ≤ e)
    [HasDerivedCategory.{b}
      (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))]
    [∀ U : (Spec (.of A)).Opens,
      HasDerivedCategory.{b}
        (SheafOfModules.{a} ((moduleRings (Spec (.of A)).toRingedSpace).over U))] :
    Scheme.IsPerfect (Spec (.of A))
      (DerivedCategory.Q.obj
        ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{a} A)
          (SheafOfModules.{a} (moduleRings (Spec (.of A)).toRingedSpace))
          _ _ _ _ (tilde.functor (.of A))
          ⟨fun _ _ ↦ tilde.map_zero⟩ (ComplexShape.up ℤ)).obj
          (shiftedKoszulComplex A r (fun i ↦ f i ^ e)))) ∧
      IsIso (((SheafOfModules.overFunctor (moduleRings (Spec (.of A)).toRingedSpace)
        (⨆ i : Fin r, (Spec (.of A)).basicOpen
          ((Scheme.ΓSpecIso (.of A)).inv (f i)))).mapDerivedCategory).map
            (affineKoszulAugmentation A r (fun i ↦ f i ^ e))) := by
  exact ⟨affine_perfect_koszul_principal_unit_perfect A r f e,
    affine_perfect_koszul_principal_unit_iso A r f e he⟩

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CoherentFormalModule
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientIso
import WeilConjectures.AlgebraicGeometry.CompletionInternalHomQuotientAnnihilation

/-! # Internal Hom factorization through ideal-power quotients

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, construction of the map.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- Postcomposition with the level-n quotient kills the level-n ideal product of
internal Hom. Maps into that quotient factor uniquely through the level-m source
quotient whenever n ≤ m.

Source: Stacks Project, Cohomology of Schemes, Lemma 0882, construction of its map;
Section 0EHN, equation 0880.
(blueprint: lem-weil-pbc-completion-internal-hom-quotient).

Proof:
1. By the image definition of the ideal-module product, its sections are locally
   finite sums of products of ideal sections and module sections. The quotient by
   that image is annihilated by the ideal power, since each multiplication factors
   through the image and then has zero composite with the cokernel projection.
2. A local linear map G → F/I^n F sends a product ax with a in I^m to a times
   the image of x. This is zero, because I^m is contained in I^n for n ≤ m.
   Consequently the map kills I^m G and factors uniquely through G/I^m G.
   Restriction preserves the quotient universal property (restriction is exact),
   so these local factorizations commute with restriction and are linear. They
   invert precomposition on every open, giving the internal-Hom isomorphism.
3. For a local map h : G → F and a in I^n, postcomposition sends ah to the
   map x ↦ a times the class of h(x), which is zero by step 1. Thus it kills
   each local finite sum of such products, hence the entire ideal product sheaf.
No coherence or Noetherian hypothesis is needed for these finite-level assertions. -/
theorem completion_internal_hom_quotient {X : Scheme.{u}}
    (I : X.IdealSheafData) (F G : X.Modules) (m n : ℕ) (h : n ≤ m) :
    (Scheme.idealModuleProductι (Scheme.idealSheafPower I.toModulesι n).2
        (SheafOfModules.homObj (R := X.toRingedSpace.sheaf) G F) ≫
      SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
        (𝟙 G) (formalModuleQuotientπ I n F) = 0) ∧
    IsIso (SheafOfModules.homObjMap (R := X.toRingedSpace.sheaf)
      (formalModuleQuotientπ I m G) (𝟙 (formalModuleQuotient I n F))) := by
  constructor
  · exact completion_internal_hom_quotient_annihilation I F G n
  · exact completion_internal_hom_quotient_isIso I F G m n h

end AlgebraicGeometry

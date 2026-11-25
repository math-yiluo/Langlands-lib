/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import Mathlib.CategoryTheory.Limits.Constructions.Over.Products
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech
public import WeilConjectures.CategoryTheory.SiteCechComplex
import WeilConjectures.CategoryTheory.SiteCechMathlibComparison

/-!
# Comparison of the two étale Čech complex constructions

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM.
(blueprint: lem-weil-pbc-etale-site-cech-complex-comparison).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

attribute [local instance] Over.ConstructProducts.over_finiteProducts_of_finiteWidePullbacks

/-- Chosen fibre products and the categorical products in the slice give isomorphic
Čech complexes, with their alternating restriction differentials.

Source: Stacks Project, Cohomology on Sites, Tags 03AK and 03AM, independence of the
choice of fibre products.
(blueprint: lem-weil-pbc-etale-site-cech-complex-comparison).

Proof: For every tuple of indices, both constructions use its fibre product over U.
The universal properties give a unique projection-compatible isomorphism from the
categorical product in Over U to the product chosen by S. Restriction along this
isomorphism identifies their groups of sections. Taking products over all tuples gives
an isomorphism in each degree; the canonical limit product of abelian groups is identified
with the group of tuples by its projections. The product isomorphisms commute with each
omitted-factor map, since their composites with every projection agree. Therefore the
degree maps commute with each restriction summand and with its sign, hence with the
alternating differential. The reverse product isomorphisms give inverse complex maps.
This includes the empty index set and degree zero; no covering assumption is needed. -/
theorem nonempty_etale_siteCech_complex_iso
    (X : Scheme.{u}) (U : X.Etale) {J : Type (u + 1)}
    (V : J → X.Etale) (f : ∀ j : J, V j ⟶ U) (S : SiteCechComplex V f)
    (F : X.Etaleᵒᵖ ⥤ AddCommGrpCat.{u + 1}) :
    Nonempty (S.complex F ≅
      (cechComplexFunctor fun j : J ↦ Over.mk (f j)).obj ((Over.forget U).op ⋙ F)) := by
  exact CategoryTheory.SiteCechComplex.mathlib_complex_iso_exists (V := V) f S F

end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleLowerShriekBaseChangeMap
import WeilConjectures.SixFunctors.BaseChange.Etale

/-!
# Etale extension by zero commutes with base change for module sheaves

Source: Stacks Project, Etale Cohomology, Lemma 59.70.5, Tag 03S6
(blueprint: lem-weil-pbc-etale-shriek-base-change-modules).
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry.Etale

/-- The canonical base-change transformation for etale extension by zero is an isomorphism
on sheaves of constant-ring modules. Thus every component is an isomorphism, and the
inverse components form a natural transformation in the opposite direction.
Source: Stacks Project, Etale Cohomology, Lemma 59.70.5, Tag 03S6
(blueprint: lem-weil-pbc-etale-shriek-base-change-modules).

Proof:
1. The base change of `j` is etale (situation-conventions).
Compose the adjunctions for extension by zero (lemma-acyclicity-pulled-back-injectives)
and inverse image (situation-conventions), using
 def-weil-pbc-composite-adjunction. The two left adjoints are `f⁻¹ j_!` and `j'_! f'⁻¹`.
By def-weil-pbc-etale-shriek-base-change-map, the conjugate of the displayed transformation
is the underived exchange between their right adjoints.
2. By lem-weil-pbc-etale-underived-exchange-restriction, this exchange is an isomorphism
on abelian sheaves: sections identify the two iterated fibre products.
3. By lem-weil-pbc-underived-exchange-module-linear, exchange is module-linear. The inverse
of each bijective linear section map is linear, and these inverses commute with restriction.
Thus the exchange is a natural isomorphism on module sheaves
(situation-conventions).
4. Conjugation preserves and reflects isomorphisms (def-weil-pbc-adjunction-conjugate),
so the base-change transformation is an isomorphism. Its inverse is natural in the sheaf. -/
theorem isIso_etaleLowerShriekBaseChangeMap (Λ : Type (u + 1)) [CommRing Λ]
    {Y V X : Scheme.{u}} (f : Y ⟶ X) (j : V ⟶ X) [Etale j] :
    IsIso (etaleLowerShriekBaseChangeMap Λ f j) := by
  unfold etaleLowerShriekBaseChangeMap
  have := Etale.isIso_baseChangeMap_flip_of_isPullback (ModuleCat.{u + 1} Λ)
    (IsPullback.of_hasPullback f j).flip
  infer_instance

end AlgebraicGeometry.Etale

# Abstract reciprocity: unit cohomology and the two exact rows

Module `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Core`, copied unchanged from the Lean library NYLL. The origin of the file is given at the end of this page.

This file belongs to the library's abstract class field theory: a group `G` with a topology, fields given by closed subgroups, a coefficient representation `A` written additively, a degree datum `D` and a valuation datum `v`. It has two parts. The first shows that the class field axiom implies the unit-cohomology axiom. The second builds the two rows used to prove abstract reciprocity for a finite Galois tower `K ⊆ M ⊆ L`, and counts orders in the cyclic case.

## Unit cohomology from the class field axiom

- `classFieldAxiom_implies_unramifiedUnitCohomology`: if `hcf : SatisfiesClassFieldAxiom A`, then `v` satisfies `SatisfiesUnramifiedUnitCohomology`. That is, `Ĥ⁰` and `Ĥ⁻¹` of the units `U_L` vanish for every finite unramified cyclic `L/K` with `K` finite over the base field.

Proof for `Ĥ⁻¹`: the axiom writes a unit of norm zero as `g·a − a` with `a ∈ A_L`. Correcting `a` by an element of `A_K` of the same valuation turns it into a unit; this uses that `L/K` is unramified.

Proof for `Ĥ⁰`: the valuation modulo `n = [L:K]` maps `Ĥ⁰(A_L)` onto `ℤ/nℤ`. The axiom gives this group order `n`, so the map is bijective. Hence a unit of `K` is a norm `N(y)`, and `y` is a unit.

## The two rows

- `abstractReciprocityInclusion : G(L/M) → G(L/K)` and `abstractReciprocityRestriction : G(L/K) → G(M/K)`. Restriction is surjective, and `abstractReciprocity_galois_exact` gives exactness at `G(L/K)`.
- `abstractReciprocityNormMap : A_M/N A_L → A_K/N A_L` is induced by the norm from `M` to `K`, and `abstractReciprocityNormProjection : A_K/N A_L → A_K/N A_M` is the projection. The projection is surjective, and the row is exact in the middle (`abstractReciprocity_normQuotient_exact`).
- `abstractReciprocity_normMap_comp_normQuotientInclusion`: `abstractReciprocityNormMap` composed with the inclusion `i` of norm quotients is multiplication by `[M:K]`.
- `abstractReciprocityAbelianizationFactor` factors an additive map through the abelianization.
- Comparison lemmas identify these maps with those of norm–conjugation naturality when the base fields agree.

## Cyclic order counts (under `hcf`)

- `abstractReciprocity_cyclic_surjective_iff_bijective`: let `L/K` be cyclic and `K` of finite index in the base field. An additive homomorphism `G(L/K) → A_K/N A_L` is then surjective if and only if it is bijective.
- `abstractReciprocity_cyclicTower_normMap_injective`: under the same condition on `K`, if `L/K`, `L/M` and `M/K` are all cyclic, `abstractReciprocityNormMap` is injective.

The file ends with valuation lemmas for totally ramified extensions, among them `v_L(x) = [L:K]·v_K(x)` for `x` from `K`.

## Watch for

- `SatisfiesClassFieldAxiom A` is a hypothesis wherever it appears.
- The cyclic statements require a generator of each cyclic quotient as an argument.
- The header comment displays the upper row as short exact. The file proves exactness in the middle and surjectivity on the right, but states no injectivity of `abstractReciprocityInclusion`.

## Origin of the file

Copied unchanged from the Lean library NYLL (https://github.com/n-yamaguchi-0729/NYLL), commit `fe40c03df1b2b195053fdd63305571d97c73ce48`, file `Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/Core.lean`: the Lean file is the source byte for byte (SHA-256 `b357dd72b634cb26a98b77944e5678aadc7d5f339ded72364cf3c61648c7dd34`). That library is distributed under the Apache License, Version 2.0; its licence and notice are kept with the Library's licences.

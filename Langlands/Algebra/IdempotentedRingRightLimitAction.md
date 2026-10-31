# The actual right-limit action on original nondegenerate modules

Authors: Worker 6 and Worker 702.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The original conventions and I.1.1–I.1.3, printed pp.5–9/PDF11–15,
specify original additive associative actions without a unit law,
finite local units, compatible right-image families and the actual
source product. Printed p.9/PDF15 gives the action formula using a
fixing idempotent and asserts choice independence and unitality.

The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The cited PDF11–15 were read directly, and PDF15 was also inspected
visually. No dedicated source errata note was present in the project or
current Library. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF1–3. The early Chapter I corrections on PDF1 change the
old pseudometric inequality and fixed-point formula; the governing
2026 text already has these corrected formulas. These entries do not
change the action formula used here.

The scalar ring `A : Type uA` and vector carrier `M : Type uM` are
independent. The given `AddCommGroup M` and original
`NonUnitalModule A M` remain the original operations.
`IsNondegenerate A M` is precisely the property that each vector is
fixed by some actual idempotent of `A`. The completed scalar carrier
is the actual `IdempotentedRingRightLimit A` with the local actual
`IdempotentedRingRightLimit.ring hA`. No replacement carrier or
assumed extension occurs.

`coordinate_smul_independent` compares any two idempotents fixing
the same original vector. Choose a common upper idempotent `g`.
Family coherence rewrites `x(e)` as `x(g)*e`; associativity of the
original action and the fixing equation give `x(e) • m = x(g) • m`.
The same argument with the other fixer proves equality.
`act hM x m` chooses one fixing idempotent, and `act_eq` proves the
exact source formula for every permitted fixer.

For additivity in vectors, choose fixers for both vectors and a
common upper bound. The original idempotent absorption lemma shows
that this upper bound fixes both vectors, so it fixes their sum.
The exact formula reduces the claim to original distributivity.
Additivity in the family and both zero laws similarly use one
fixer and the original action laws. The unit family's value at
that fixer is the fixer itself, proving the unit law.

For `product_act`, first choose `e` fixing `m`, then a local unit
`f` fixing `y(e)` on the left. The original action law gives
`f • (y(e) • m) = y(e) • m`. The exact source product formula
`(x*y)(e) = x(f)*y(e)`, the action formula at these two fixers,
and original associativity give
`(x*y) • m = x • (y • m)`. Thus `module hA hM` packages all
proved laws into an ordinary unital `Module` on the same original
additive group. Users install it and the actual ring locally.
`smul_eq` is the exact installed-action formula.

The canonical family's value at `e` is `a*e`. Original
associativity and `e • m = m` therefore prove
`canonical_act` and `canonical_smul`: its new action is exactly the
original action of `a`.

An original intertwiner sends every fixing equation to a fixing
equation. Using the same fixer on source and target reduces
`map_act` to its original intertwining law.
`linearMap hA hM hN f` is the same actual additive map, now linear
over the constructed right-limit ring and modules. Its evaluation
formula is reflexivity, and `linearMap_toAddMonoidHom` identifies its
entire underlying additive homomorphism with that of the original
intertwiner by definitional equality. Extensionality proves identity and
composition laws on those same underlying maps, retaining a fourth
independent carrier universe for composition.

Complete unapplied checks retain arbitrary scalar and carrier
universes, including both unequal scalar/vector assignments.
The hypotheses include zero rings and trivial carriers, arbitrary
noncommutative nonunital original rings and the original action
conventions. No global identity or original unit-action law,
nontriviality, field, dimension or finiteness assumption is added.
The extended unit law is proved from nondegeneracy. `module` uses the
original `AddCommGroup M` parameter directly, and a definitional check
identifies its installed action with `act`.

The detailed module laws and extension of intertwiners are intrinsic
internal consequences implementing the source's action construction,
not additional numbered source theorems. Uniform continuity of
orbit maps, continuous extension uniqueness, universal completion
comparisons, topological-ring laws and the distinct module
completion of I.1.4 remain separate units.

This module imports the independently published actual ring and original
nonunital-module interfaces by Lean name. It introduces the extended
action and linear maps on those original carriers.

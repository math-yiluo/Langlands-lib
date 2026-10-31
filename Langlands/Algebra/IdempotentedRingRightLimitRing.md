# The actual ring on right-compatible families

Authors: Worker 6 and Worker 702.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
I.1.1–I.1.2, printed pp.6–7/PDF12–13, supplies the nonunital conventions,
actual corner order and finite local units. I.1.3, printed pp.8–9/PDF14–15,
supplies the actual compatible families and canonical map. The product
formula, its independence of choices, the extension of multiplication
and the unit family are on printed p.9/PDF15.

The retained original is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
The cited PDF12–15 were read, and PDF15 was also inspected visually.
No dedicated source errata note was present in the project or current
Library. The supplementary registered
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF1–3. Its early Chapter I corrections concern the
pseudometric inequality and a fixed-point formula in the 2010 edition;
they do not change the product or unit used here. The governing source
remains the 2026 original.

Every construction uses the original `A : Type uA` with its original
`NonUnitalRing A` and `hA : IsIdempotented A`. The carrier is precisely
the additive subgroup `IdempotentedRingRightLimit A` from the prerequisite.
No original identity, nontriviality, multiplicative commutativity, size
restriction, topology or extra ring-law certificate is assumed.

`coordinate_mul_independent` proves that `x(e) * a` is independent of
the actual idempotent `e` fixing `a` on the left. Choose a common upper
bound `g` of two permitted choices. Family coherence rewrites their
values as `x(g) * e` and `x(g) * f`; associativity and the two left-unit
equations give equality after multiplication by `a`.
`applyOriginal` chooses one such idempotent; `applyOriginal_eq` makes
its value independent of that choice. A common finite local unit proves
additivity in the original element. A left unit for `a` also fixes `a*b`,
which proves right-linearity. Pointwise addition of families proves
additivity in the family. The original idempotent coordinate and the
canonical family have the stated exact evaluation laws.

`product hA x y` has coordinate `applyOriginal hA x (y(e))`.
Right-linearity and the right-fixed and coherence equations of `y` prove
that this is again an actual compatible family. `product_val` proves
the exact source formula `x(f) * y(e)` for every idempotent `f` fixing
`y(e)` on the left. Thus the product does not depend on the chosen
idempotents. `product_applyOriginal` proves that evaluation of a product
is composition of the two evaluations, using any left unit for the
original argument and right-linearity.

`unit` is the family with value `e` at `e`. The corner order gives its
coherence. Its evaluation is the identity on the original ring.
Coordinate extensionality, the composition law and the two additivity
laws prove associativity and both distributive laws. Zero and unit
laws follow from the corresponding evaluation equations.
`ring hA` packages these proved laws as a `Ring` on the same carrier
with exactly its inherited pointwise additive commutative group.
Users install this definition locally; the module adds no global ring
instance.

`canonical_product` uses the canonical-family evaluation formula and
original associativity to prove multiplication preservation.
`canonicalRingHom` packages the already constructed canonical additive
map with that law as an actual nonunital ring homomorphism into the local
`ring hA`. Its underlying map is definitionally the original canonical
map; injectivity is the already proved finite-local-unit theorem.
`canonicalRingHom_toAddMonoidHom` also identifies its entire underlying
additive map with `canonical` by definitional equality. Complete
unapplied interface checks retain the arbitrary ring universe, and
additional checks use multiplication and `1` after installing `ring hA`
locally. The projection of `ring hA` to `AddCommGroup` is definitionally
the published instance, preserving all its operations.

The helper evaluation laws and detailed ring axioms are internal
intrinsic obligations implementing Renard's ring assertion; they are
not extra numbered theorems or class formulations attributed to the
book. This unit supplies no topology or continuity on the limit,
density, completeness, completion comparison, annihilator quotient
comparison, or extension to an arbitrary nondegenerate module.

This module imports the independently published additive right-image
limit by Lean name and introduces only the ring construction on that
carrier.

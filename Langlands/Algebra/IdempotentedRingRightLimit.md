# The actual additive right-image inverse limit

Authors: Worker 6 and Worker 702.

For the actual given nonunital ring `A`, `Idempotent.rightImage e` is the
additive subgroup of elements satisfying `a * e = a`. Its membership
equivalence with `∃ b, b * e = a` identifies it with the source's `Ae`.
Idempotence proves the image-to-fixed-point implication. The actual
additive map `rightProjection e` sends `a` to `a * e`. It is the identity
on the subgroup, so is surjective.

For the published corner order `e ≤ f`, `rightTransition` sends an element
of `Af` to its product on the right with `e`. The identity law uses its
fixed-point condition, while composition and compatibility with the
projections use associativity and `f * e = e`. These are actual additive
maps between the actual subgroup carriers.

`rightCompatibleFamilies A` is an actual additive subgroup of the function
group `Idempotent A → A`, imposing both the right-fixed equation at each
coordinate and the source coherence equations for all comparable
idempotents. Its subtype `IdempotentedRingRightLimit A` inherits its
additive commutative group. `evaluation e` takes its value in `Ae`.
The coherence equations give transition compatibility. Equality of all
evaluations gives equality of families by function and subtype extensionality.

`lift` constructs an additive map into this group from any compatible
family of actual additive maps `q e : B →+ Ae`. Its values are precisely
the coordinate values of `q`; compatibility proves membership in the
family subgroup. `evaluation_lift` proves the coordinate equations.
`lift_unique` uses extensionality, and `existsUnique_lift` gives the exact
additive inverse-limit universal property. The test group `B` has a
universe independent of `A`, with complete unapplied checks at arbitrary
universes and both unequal assignments `(0,1)` and `(1,0)`. The construction
and universal property work even without idempotentedness.

`canonical` is the actual additive map `a ↦ (e ↦ a * e)`, with exact
coordinate formula and projection compatibility. For `IsIdempotented A`,
a common two-sided local unit for two elements makes equality of their
canonical families imply equality of the original elements. This proves
injectivity without a global unit or a nontriviality assumption.

The governing original is David Renard, *Représentations des groupes
réductifs p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The retained source is
`/home/taskhub/central-library/Renard--Representations des groupes reductifs p-adiques (2026 version)--2026.pdf`.
I.1.1–I.1.2, printed pp.6–7/PDF12–13, provide the nonunital conventions,
corner order and finite local units. I.1.3, printed p.8/PDF14, defines
`Ae`, its right multiplication transitions and the inverse limit.
The explicit family conditions run from printed p.8/PDF14 to p.9/PDF15;
the canonical embedding is on printed p.9/PDF15.

These original pages were read, and PDF15 was also inspected visually.
No source-specific project or current Library errata note was present.
The supplementary registered `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF1–3. Its early Chapter I entries correct a pseudometric
inequality and a local-unit formula in the 2010 edition. They do not alter
the right images, transitions, or family equations used here. The governing
2026 original already states `d_e ≤ d_f` and the fixed-point equation
`a * e = a`; the pseudometric assertion itself is outside this unit.

The additive subgroup presentation and its explicit universal-property
proof are an internal realization of the source's inverse limit (whose
categorical reference is A.IV.1). No categorical limit certificate is
assumed or installed. This module does not assert a topology, a ring
product, a unit, a quotient/decomposition comparison, density, completeness,
or an extension of module actions on the family group. Those remain
separate obligations. The distinct left-action module completion of
I.1.4 is also outside this unit.

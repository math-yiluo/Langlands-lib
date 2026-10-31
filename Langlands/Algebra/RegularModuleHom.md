# Actual regular-module Hom and its source action

Authors: Worker 6 (construction and intrinsic proofs) and Worker 185
(source/interface audit and submission). This is the focused definition
unit for task `4c53eccd-a24b-4027-b6bd-bcdfea0e3031`.

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Chapter I conventions and I.1.1–I.1.5, printed pp.5–11/PDF11–17, govern
the original nonunital actions. I.1.4, printed p.10/PDF16, describes the
evaluation of `Hom_A(A,M)` on actual idempotents and the left action
`(a • φ)(b) = φ(b*a)`. Formula I.1.5.1 on the same page describes the
canonical vector map `m ↦ (a ↦ a • m)`. Worker 185 read all of these
original pages and visually checked PDF16. The registered supplementary
2010 errata `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
were consulted at PDF pages 1–3. The correction from `ae=e` to `ae=a`
in the older Hom argument is already present in the governing 2026
edition; it concerns the separate inverse construction. No dedicated
project errata entry was found.

`regularModuleHomGroup A M` is the actual additive subgroup of `A →+ M`
cut out by `φ(a*b) = a • φ(b)`. `RegularModuleHom A M` is its subtype,
with the inherited pointwise abelian group, function coercion,
extensionality, additive inclusion, and exact additive and left-linear
formulas. `NonUnitalModule.regular A` specifies the regular source action
by multiplication without installing a global action instance on `A`.
The additive equivalence `RegularModuleHom.equivNonUnitalModuleHom`
identifies these actual maps with the published `NonUnitalModuleHom`
using that explicit regular source action and the unchanged original
target action. Its maps preserve the entire additive map. This also
retains distinct actions when source and target carriers coincide;
an explicit equal-carrier zero-target example checks this case.

`rightPrecomposition a` precomposes an additive map with `b ↦ b*a`.
Associativity of ring multiplication proves that the result still
satisfies the left-linear equation. Pointwise addition proves that this
operation is additive in the Hom argument. The installed
`instNonUnitalModule` uses precisely this formula: associativity gives
the action composition law, right distributivity and additivity of
`φ` give addition in the scalar, and the original additive-map zero law
gives the zero-scalar law. No pointwise scalar multiplication on values
is substituted for the source formula.

`RegularModuleHom.canonical` is an actual `NonUnitalModuleHom` from the
original module to this Hom module. Distributivity of the original action
gives additivity in the source scalar and the vector; associativity gives
both regular left-linearity and equivariance of the vector map.
`toLeftLimit` is the actual additive map
`φ ↦ (e ↦ φ(e))` to `NonUnitalModuleLeftLimit A M`. Idempotence gives
the fixed-coordinate law, and `e*f=e` for `e ≤ f` gives left coherence.
Its coordinate and evaluation formulas are literal. The proved
`toLeftLimit_comp_canonical` equality identifies its composite with the
original-vector map with the published canonical left-compatible family.

The subtype presentation, explicit regular-action adapter equivalence,
and structural laws are internal implementations of the displayed source
constructions. They are proved here for every original nonunital action
over every nonunital ring, which extends the source's idempotented-ring,
nondegenerate-module setting for these definitions and intrinsic laws.
No idempotented-ring hypothesis, nondegeneracy, original unit-action law,
nontriviality or finiteness is used. Zero rings, zero actions and trivial
carriers remain included. Complete unapplied interfaces are checked at
independent ring and vector universes and at both unequal assignments.

The evaluation isomorphism proposition is a separate statement and proof
unit requiring `IsIdempotented A`. This file constructs its actual map
but does not assert bijectivity. It installs no scalar action on the
family carrier and makes no topological claim. The family action,
completion functor, nondegenerate-part comparison and
smoothing/completion adjunction remain separate successors.

# Categorical universality of the actual ring localization

Worker 1301 implements this proof, with Worker 709's source correspondence,
statement design and suggested factorization route. The module imports the
published `Langlands.Algebra.RenardLocalRingUniversalStatement` without changing
its statements or the actual ring-denominator construction it imports.

## Source and formal packaging

The governing source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, Appendix A.III.1, printed
pp.251–252 / one-based PDF257–258. These pages were read directly for this
proof. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
The supplementary `renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was checked on PDF18–19. Those pages do not change example 3; this is a
bounded check of older-edition errata.

On PDF257, a right universal solution for an inclusion is a chosen map
through which every map to an object of the subcategory factors uniquely.
Example 3 on PDF258 applies this definition to commutative unital rings
with designated multiplicative subsets, maps preserving those subsets,
and the full subcategory where the designated elements are units. It
identifies the actual localization and canonical ring map as the solution,
including the case where zero is designated.

The imported `RingPair`, `LocalRingCat`, full inclusion, chosen factor and
structured-arrow presentation are derived internal packaging of that
example. The localized pair designates precisely the image of the original
submonoid under the algebra map. The source does not specify that designated
submonoid or a carrier-universe convention. The proof retains these published
choices, so a local target may designate a proper submonoid of its units.

## Implemented proof

All four theorems lie in `Langlands.Renard.RingLocalization`.

`categoricalFactorizationStatement` proves the published
`CategoricalFactorizationStatement.{u}`. Extensionality for the actual
denominator-preserving morphisms reduces the canonical triangle equation
to equality of ring homomorphisms, and then to evaluation on each original
ring element. The published `canonicalFactor_algebraMap` law gives exactly
that equality. Thus the constructed factor, including its already proved
denominator-preservation property, satisfies the triangle equation.

`categoricalFactorUniquenessStatement` proves the published
`CategoricalFactorUniquenessStatement.{u}`. Its competitor is every actual
map `g : canonicalLocalObject A ⟶ N` satisfying the triangle equation.
Extensionality first removes the full-subcategory and denominator-preservation
wrappers. `IsLocalization.ringHom_ext A.denominators` reduces equality of
the remaining ring maps to equality after precomposition with the algebra
map. Evaluation of the assumed triangle equation, together with
`canonicalFactor_algebraMap`, supplies this equality. There is no restriction
to maps already presented as localization lifts.

`categoricalInitialityStatement` proves the published
`CategoricalInitialityStatement.{u}`. For each actual structured arrow `B`
out of `A`, `StructuredArrow.homMk` packages the chosen factor
`canonicalFactor A B.right B.hom`, with the proved triangle equation.
`Limits.IsInitial.ofUniqueHom` constructs initiality from these morphisms.
For every competing structured-arrow morphism, `StructuredArrow.w` gives
its triangle equation, the preceding uniqueness theorem identifies its
right component, and `StructuredArrow.hom_ext` identifies the whole morphism.
The resulting initiality data are wrapped in `Nonempty`, exactly as required
by `StructuredArrow.IsUniversal`.

Finally, `categoricalUniversalStatements` has type exactly the closed
published `CategoricalUniversalStatements.{u}` and combines these three
proofs. It takes no extra mathematical arguments or universal-property
certificate.

## Universes and scope

The common ring-carrier universe `u` is arbitrary. Every actual `RingPair.{u}`,
local target `LocalRingCat.{u}`, denominator-preserving unital map and
commuting competitor is quantified over. The proof uses the actual
`Localization A.denominators`, its designated image, the existing
`canonicalFactor` and `canonicalStructuredArrow`, and all maps in the full
subcategory. The localization extensionality theorem applies also to zero
rings and submonoids containing zero. No nontriviality, domain, finiteness,
smallness or shrinking assumption is added.

This proof covers the three published categorical assertions for example 3.
Compatible isomorphisms between different chosen solutions, localization
functors, reflection and adjunctions, independent-target-universe transport,
the other examples and the rest of Appendix A remain separate obligations.

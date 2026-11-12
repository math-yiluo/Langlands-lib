# No primitive classes in structure-sheaf cohomology of degree two

`Langlands.AbelianScheme.FieldH2PrimitiveInjectivityStatement.{u}` is a
`Prop`-valued definition, with all parameters quantified inside the proposition.
It states that, for an abelian scheme `A` over any field `K` in `Type u`,

```text
μ* − p₁* − p₂* : H²(A, O_A) → H²(A ×_K A, O_(A ×_K A))
```

is injective. This file states a proof obligation and proves no injectivity
result. There is no characteristic restriction, positive-dimensionality
assumption, or chosen basis.

## Objects, maps and coefficients

The underlying object `A.X : Over (Spec (CommRingCat.of K))` is the Library's
actual smooth, proper, geometrically connected commutative group scheme.
`P := A.X ⨯ A.X` is its product over `Spec K`. The arrows `p1`, `p2` are
the categorical projections, and `m := p1 * p2` is the actual multiplication
map supplied by the group-object instance.

For each of these arrows `f`, the linear map called `pull f` is the composite

```text
H²(A, O_A)
  → H²(P, f*O_A)
  → H²(P, O_P).
```

The first arrow is
`Langlands.AlgebraicGeometry.Modules.DerivedSections.relativeCohomologyPullback`.
The second is the cohomology map of
`Langlands.Scheme.Modules.pullbackUnitIso f.left`. Thus all three arrows
have exactly the same target module. Subtraction takes place in the module
of linear maps over the actual field `K`. `Function.Injective` asserts
injectivity of this particular difference map; no replacement isomorphism
or unspecified Künneth identification occurs in the proposition.

The functor `relativeCohomology A.X.hom 2` is the Library's right-derived
relative global-sections functor, valued in `ModuleCat K`. Applied to the
structure module, it is the actual structure-sheaf cohomology used by the
obstruction calculation.

## Source and provenance

Derived from D. Mumford, J. Fogarty and F. Kirwan, *Geometric Invariant
Theory*, 3rd enlarged edition (1994), Chapter 6, proof of Proposition 6.7,
printed pp.117–118, especially the last displayed homomorphism and the
following injectivity assertion on p.118 (PDF pp.130–131). The registered
original is
`provided-ec58cb66687d0d54d9e39b6ec21281b651fe3a6d039f9b5d099c79791671233f`,
file `Mumford, Fogarty, Kirwan - Geometric Invariant Theory, 3rd edition
(1994), Chapter 6.pdf`, SHA-256
`3eed7c31fd64936e20a41d85c85ebaeebc3f2631b01f561417b85bdf33b1af16`.
Worker 2057 read both pages and visually checked the displayed map on
p.118. No source-specific errata note was found in the project or current
Library `notes/errata` directories.

The source uses this map after tensoring with the kernel of an elementary
Artinian thickening. The present statement isolates its field coefficient
map before tensoring. The source invokes the structure of the cohomology
of abelian varieties and the Künneth formula. In the usual exterior-algebra
description, the mixed component of multiplication on degree two sends
`v ∧ w` to `v ⊗ w − w ⊗ v`, which is injective also in characteristic two.
This is an explanation of the proposed proof route, not a construction or
an assumed comparison in Lean.

The source's projectivity hypothesis belongs to its relative Picard
representability setup. The isolated field cohomology assertion holds for
abelian varieties; the Library encodes these over a field as smooth proper
geometrically connected commutative group schemes. The later proof must
justify every field-cohomology comparison needed for this full scope.

## Role and remaining obligations

This is a substantial prerequisite of Task 5704,
`60cd926c-5964-46c0-ad0e-111a8faf6631`, for
`ArtinianPrimitiveLineBundleLiftingStatement`. A proof must establish the
injectivity for the specific canonical maps above. Existence of an
abstract Künneth isomorphism alone does not identify these maps.

Naturality of square-zero Picard obstructions under morphisms of
thickenings, compatibility with the identification of elementary ideal
cohomology with residue-fibre cohomology, and the lifting argument are
separate obligations. This statement neither assumes nor proves any
relative dual representability, Picard-zero lifting or Picard smoothness
result.

## Authorship

Worker 2057 authored this pair.

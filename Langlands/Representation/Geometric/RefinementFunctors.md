# Normalized functors for refinements inside a product Levi

Author: Worker 14.

This module constructs normalized induction and Jacquet functors for the actual
standard subgroups inside a product Levi of `GL_n`. Let `B : BlockShape n` be
an ordered outer block shape and `S : BlockRefinement B` an ordered block shape
inside every outer block. The ambient group is `B.Levi F`; the parabolic,
diagonal Levi and radical are the existing subgroups `refinedParabolic F B S`,
`refinedLevi F B S`, and `refinedUnipotent F B S`.

## Jacquet construction

`RefinedJacquetModule B S ρ` is literally
`Jacquet.Coinvariants ρ (refinedUnipotent F B S)`. It is the ambient quotient by
the span of the vectors `ρ(u)v - v`, and `refinedJacquetMk` is its canonical
linear quotient map. This agrees definitionally with the carrier tested by
`CuspidalSupport.IsLeviQuasicuspidal`. No alternate parabolic quotient or
coordinate equivalence is required.

`refinedLevi_le_normalizer` follows from the actual inclusion section and the
proved fact that the refined parabolic normalizes the ambient radical. For a
full positive character `δ` on the refined Levi,
`normalizedRefinedJacquetOf B S δ ρ` uses the published normalized normalizer
action on that quotient. Its action on a quotient class is

`m [v] = δ(m)^(-1/2) [ρ(m.val)v]`.

The square root is the canonical positive square root, embedded in the complex
numbers. An ambient intertwiner `f` induces `[v] ↦ [f(v)]`. Its well-definedness
and equivariance come from the existing normalized Jacquet map, rather than
being assumptions. An open kernel for `δ` gives smoothness of the normalized
quotient of a smooth representation. The bundled
`normalizedRefinedJacquetFunctorOf` has intrinsic identity and composition laws;
their proofs use the coinvariant extensionality lemma and reduce to the action
on quotient representatives.

## Induction construction

`refinedInducingRepresentation B S χ σ` inflates `σ` through the actual
`refinedLeviProjection F B S` and twists by the inflated unit-valued complex
character `χ`. `normalizedRefinedInducedOf` is the existing smooth induction
from the actual refined parabolic to the ambient product Levi. Its vectors are
actual functions with the covariance

`f(q g) = χ(projection(q)) • σ(projection(q))(f(g))`

and an open subgroup fixing the entire function by right translation. The
action is `(g f)(x) = f(x g)`. The displayed covariance and translation laws are
proved directly from the function construction. An intertwiner acts by
postcomposition. The induction functor's identity and composition laws reduce
to pointwise equality of functions.

This low-level constructor accepts any character `χ`; smoothness of the
result follows from taking smooth vectors. It makes no claim that arbitrary inducing data are smooth and asserts no
exactness theorem. The p-adic specialization uses
the specific positive half modulus, whose open kernel was proved in
`RefinementDefinitions`.

## P-adic specialization and universes

For a prime `p`, `F : PadicField p` and compatible `T : F.TopologicalData`, the
public specializations in `Langlands.PadicField.TopologicalData` are:

- `T.normalizedRefinedJacquet B S ρ` and
  `T.normalizedRefinedJacquetFunctor B S`, using
  `T.refinedLeviModulus B S`. The action formula is stated using exactly
  `T.refinedLeviInverseHalfModulus B S`.
- `T.normalizedRefinedInduced B S σ` and
  `T.normalizedRefinedInductionFunctor B S`, using
  `T.refinedLeviHalfModulus B S`. The function carrier exposes the inflated
  `T.refinedParabolicHalfModulus B S` and actual projection.
- The corresponding `normalizedRefinedJacquetMap` and
  `normalizedRefinedInducedMap`, and the two smoothness theorems.

The full character is the product of the explicit residue-normalized block
moduli over the inner parabolics, and the two functors therefore use inverse
and positive halves of the same character. The chosen field topology induces
the product and subgroup topologies in the source and target categories.
There is no assumption of irreducibility, admissibility, finite length, or
finite dimensionality. Empty outer block shapes are allowed. Field and carrier
universes are independent: Jacquet preserves carrier universe `uV`, while
induction has carrier universe `max uF uV`, as required by its function space.
The auxiliary algebraic and topological constructions work over a commutative
ring, respectively a topological commutative ring.

## Provenance and scope

The registered original is Bernstein and Zelevinsky, *Induced representations
of reductive p-adic groups I* (1977), source ID
`bernstein-zelevinsky-1977-induced-i`, SHA-256
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Section 1.8(a-b), printed page 444 / PDF page 5, defines normalized smooth
induction by covariance and a uniform open stabilizer, with positive half
modulus, and the normalized quotient action with inverse half modulus.
Sections 2.1-2.3, printed page 446 / PDF page 7, identify the standard subgroups
inside product Levis with ordered block refinements and apply these functors
to parabolic triples. Those original pages were read directly.

The implementation is an internal specialization of the existing actual
induction, normalized Jacquet, and refinement geometry modules. It constructs
the maps and their intrinsic laws, without assuming any representation-theoretic
theorem as data. It uses smooth induction, which is the source's capital `I`
in section 1.8. Section 2.3 identifies this with compact induction for parabolic
triples; this module does not prove that identification, nor the underlying
compactness of the parabolic quotient. The geometric lemma, exactness,
admissibility preservation, transitivity, and identification of the explicit
character with Haar scaling remain separate results. The functor definitions
alone assert none of those conclusions.

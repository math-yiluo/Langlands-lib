# Actual archimedean adjoint automorphisms

Author: Worker 16. Namespace: `Langlands.Global.ArchimedeanGL`.

The module constructs the actual adjoint automorphisms on the published real
matrix Lie algebra, its complexification, its universal enveloping algebra,
and the center of that enveloping algebra. The parameters are `K : Type u`,
`[Field K]`, and `n : ℕ`. Thus the construction applies, in particular, to every
number field in arbitrary universe and every natural rank, including zero.
The purely algebraic construction does not need a `NumberField K` instance.
No adjoint action or compatibility certificate is supplied as an input.

## Real and complex Lie automorphisms

Write `C(g) = (archimedeanGLCoordinates K n g).val` and
`M = realLieAlgebraToMatrix K n`. For `g : InfiniteAdelicGL K n`, the real Lie
equivalence `realLieConjugation K n g` satisfies

`realLieConjugation K n g X = M.symm (C(g) * M X * C(g⁻¹))`.

This is `realLieConjugation_apply`. The companion simplification lemma
`realLieAlgebraToMatrix_realLieConjugation` gives its matrix coordinates
without `M.symm`. The implementation first constructs an algebra equivalence
on the actual archimedean matrix algebra, using the inverse matrix of the
unit `archimedeanGLCoordinates K n g`. Associativity and the two unit identities
prove invertibility and multiplicativity; centrality of real scalars proves
scalar compatibility. Transport through `M` preserves the commutator bracket
because an algebra equivalence preserves products and subtraction. This
transport retains the published real Lie structure.

`complexLieConjugation K n g` is a complex Lie equivalence on the existing
`ComplexLieAlgebra K n = ℂ ⊗[ℝ] RealLieAlgebra K n`. Its underlying complex
linear equivalence is `LinearEquiv.baseChange` of the real map. Bracket
preservation uses Mathlib's proved `LieAlgebra.ExtendScalars.map`. Its action
on coefficients is the identity, as recorded by

`complexLieConjugation_tmul : Adℂ(g) (z ⊗ X) = z ⊗ Adℝ(g) X`.

The lemma `complexLieConjugation_complexify` gives the corresponding formula
on `complexify K n X = 1 ⊗ X`. The construction complexifies the whole real
matrix Lie algebra, including both real directions at complex places.

## Enveloping and center automorphisms

`envelopingConjugation K n g` is a complex algebra equivalence on the actual
`EnvelopingAlgebra K n`. Its forward map is
`UniversalEnvelopingAlgebra.lift ℂ` applied to the composition of
`complexLieConjugation K n g` with `envelopingGenerator K n`.
The universal property's generator formula yields

`envelopingConjugation_generator : AdU(g) (ι X) = ι (Adℂ(g) X)`.

Equality of algebra homomorphisms is checked on generators using
`UniversalEnvelopingAlgebra.hom_ext`. This proves the identity and composition
laws for the lifts, and hence that the lift for `g⁻¹` is their actual inverse.
The equivalence does not assume an action on the enveloping algebra.

`centerConjugation K n g` restricts this equivalence to the existing
`EnvelopingCenter K n`, the carrier of `Subalgebra.center ℂ (EnvelopingAlgebra K n)`.
Surjectivity of an algebra equivalence ensures that it maps central elements
to central elements; the same argument applies to its inverse. The inclusion
formula is

`centerInclusion_centerConjugation : incl (AdZ(g) z) = AdU(g) (incl z)`.

This asserts preservation of the center as an algebra, without asserting
pointwise fixation of its elements by disconnected group elements.

## Elementary action laws and scope

For each prefix `realLieConjugation`, `complexLieConjugation`,
`envelopingConjugation`, and `centerConjugation`, the module proves:

- `_one`: the map at the identity is the identity equivalence.
- `_mul`: the map at `g * h` is `(map h).trans (map g)`, so it sends `x` to
  `map g (map h x)`.
- `_inv`: the map at `g⁻¹` is `(map g).symm`.

The complex laws follow from the real laws by tensor induction. The enveloping
laws follow by uniqueness on generators, and the center laws follow after
inclusion. In particular, the center equivalence and its inverse permit
reindexing arbitrary central elements. No positive-rank hypothesis occurs.

Differential covariance, central covariance on function spaces, and preservation
of automorphic forms remain separate statement and proof tasks. This unit
constructs only the automorphisms and their elementary algebraic laws.

## Original source and derived provenance

A. Borel and H. Jacquet, *Automorphic forms and automorphic representations*,
Corvallis Part I (1979), section 1.5(1), printed p.190 (one-based PDF185), states
preservation of the automorphic conditions under compact right translates.
Sections 4.2(c) and 4.3, printed p.195 (PDF190), use a finite-codimension ideal
of the enveloping center in the adelic definition and its archimedean slices.
Worker 16 read both original pages. No source-specific errata note was found
in the current Library's public notes.

Registered original: `borel-jacquet-1979-automorphic`, SHA256
`3b9fe0145da81d870ef8967be83635cd440a2581fe043e64e63324e22dec4db5`.
The explicit conjugation maps and their implementation laws are internal derived
prerequisites for those statements, not verbatim numbered assertions from the
source. The actual groups and algebraic objects are imported from
`Langlands.Global.AdelicGL` and `Langlands.Global.ArchimedeanLieAlgebra`.
Mathlib's matrix-unit identities, scalar extension, universal enveloping
property, and algebra-center API supply the implementation ingredients.

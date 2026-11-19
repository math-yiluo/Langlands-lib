# Semisimple representations and the identity component in characteristic zero (proof)

The theorem
`Langlands.GroupScheme.charZeroSemisimpleRepresentationIdentityComponent.{u}` proves
the unchanged
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement.{u}`
(Milne, *Algebraic Groups* (2017), Corollaries 22.43 and 22.44) for every universe `u`,
with no additional hypotheses. Its axioms are the standard `propext`,
`Classical.choice` and `Quot.sound`.

For every field `k : Type u` of characteristic zero and every group scheme `G` over
`Spec k` whose structure morphism is locally of finite type and affine:

- if `G` is smooth, every finite matrix representation `MatrixRepresentation G (Fin n)`
  is semisimple (the sum of its simple stable subspaces is everything) exactly when
  `IsConnectedReductive (identityComponent G)` holds;
- the tensor product `ρ.tensor σ` of two semisimple finite matrix representations is
  semisimple.

The statement and its Markdown explain why the smoothness premise loses nothing
(Cartier's theorem, `affineCartierSmooth`).

## Proof

The proof is a single term that combines published Library results:

- `SemisimpleIdentityComponent.charZeroSemisimpleRepresentationIdentityComponent_of`
  (module `Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent.Reduction`)
  proves the target statement from two hypotheses: Milne's Theorem 22.42,
  `CharZeroReductiveSemisimpleRepresentationStatement.{u}`, and Milne's
  Proposition 4.19, `SemisimpleRepresentationFieldExtensionStatement.{u}`. The modules
  of `Langlands.GroupScheme.Reductive.SemisimpleIdentityComponent` and their Markdown
  carry out the argument: base change to `AlgebraicClosure k`, where semisimplicity is
  read on the representation of the group of rational points (`RationalBridge`); over
  the algebraically closed field, the published Clifford theorem for the finite-index
  normal subgroup of rational points of the identity component and the published
  finite-index ascent in characteristic zero (`AlgClosedCore`); the image of `G` under
  the direct sum representation for tensor products (`SumRepresentation`,
  `TensorCore`); and descent and ascent along `k → AlgebraicClosure k` through
  Proposition 4.19 (`FieldReduction`, `Reduction`).
- Theorem 22.42 is supplied by `charZeroReductiveSemisimpleRepresentation`
  (module `Langlands.GroupScheme.Reductive.SemisimpleRepresentationCharZeroProof`).
- Proposition 4.19 is supplied by
  `semisimpleRepresentationFieldExtension_of_algebra` (module
  `Langlands.GroupScheme.Reductive.SemisimpleFieldExtensionReduction`), which derives
  `SemisimpleRepresentationFieldExtensionStatement.{u}` from the generic algebra
  proposition `Langlands.Algebra.SemisimpleScalarExtensionStatement.{u,u,u}`, applied to
  its proof `Langlands.Algebra.semisimpleScalarExtension` (module
  `Langlands.Algebra.SemisimpleScalarExtensionProof`): a finite-dimensional semisimple
  algebra stays semisimple after scalar extension along a separable algebraic extension,
  or when its centre is étale.

The Lean proof does not follow Milne's printed route through the averaged projection
`q = (1/n) Σ g ∘ π ∘ g⁻¹` and Galois descent. Instead the reduction module works with
rational points over the algebraic closure, abstract-group semisimplicity results and
Proposition 4.19 for descent and ascent along `k → AlgebraicClosure k`, as its Markdown
records.

## Provenance

Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`. Corollaries 22.43 and 22.44 are on printed p. 478; the
provenance of the statement and its derived features are recorded in
`SemisimpleRepresentationIdentityComponentStatement.md`. Theorem 22.42 (printed p. 477)
and Proposition 4.19 (printed pp. 90–91) are the inputs used in the reduction.

# Milne 22.43 and 22.44 from Theorem 22.42 and Proposition 4.19

This module assembles the target statement
`Langlands.GroupScheme.CharZeroSemisimpleRepresentationIdentityComponentStatement` from two
published statements whose proofs are separate tasks:

- `CharZeroReductiveSemisimpleRepresentationStatement` (Milne, Theorem 22.42), hypothesis `h22`;
- `SemisimpleRepresentationFieldExtensionStatement` (Milne, Proposition 4.19), hypothesis `h419`.

## Base change and tensor products

- `tensor_baseChange_pointMatrix`: for any `b : Spec R' ⟶ Spec k`, the point matrices of
  `(ρ.tensor σ).baseChange b` and `(ρ.baseChange b).tensor (σ.baseChange b)` agree. Both are the
  Kronecker product of the matrices of `ρ` and `σ` at the corresponding point of `G`
  (published `pointMatrix_baseChange` and `tensor_pointMatrix`).
- `tensor_baseChange_rationalRepresentation`: hence, for a field extension `K` of `k`, the two
  representations have the same rational-point representation.

## Corollary 22.44

`tensor_isSemisimpleStable h22 h419 ρ σ hρ hσ`: let `k` have characteristic zero and `G` be a
group scheme over `Spec k` with `[LocallyOfFiniteType G.X.hom]` and `[IsAffineHom G.X.hom]`. If
`ρ : MatrixRepresentation G (Fin n)` and `σ : MatrixRepresentation G (Fin m)` satisfy
`IsSemisimpleStable`, so does `ρ.tensor σ`. `G` is smooth by the published
`affineCartierSmooth` (Cartier). The base changes of `ρ` and `σ` to `AlgebraicClosure k` have
semisimple rational-point representations (`geometric_rational_of_isSemisimpleStable`, module
`FieldReduction`), so does the tensor product (`tensor_rationalRepresentation_isSemisimple`,
module `TensorCore`), which is the base change of `ρ.tensor σ`; descent
(`isSemisimpleStable_of_geometric_rational`) concludes.

## The target statement

`charZeroSemisimpleRepresentationIdentityComponent_of h22 h419 :
CharZeroSemisimpleRepresentationIdentityComponentStatement.{u}`. After introducing `k`, `G` and
the local abbreviation `IsSemisimpleRep` (definitionally `IsSemisimpleStable`):

- under `[Smooth G.X.hom]`, "all `Fin n` representations semisimple ⇒ identity component connected
  reductive" is `identityComponent_isConnectedReductive h22 h419`, and the converse is
  `isSemisimpleStable_of_identityComponent h419` (module `FieldReduction`);
- the tensor conjunct is `tensor_isSemisimpleStable h22 h419`.

The theorem is conditional: it is not a proof of the target statement until `h22` and `h419` are
supplied by published proofs. It uses only the axioms `propext`, `Classical.choice` and
`Quot.sound`.

## Provenance

Internal and derived. Source: J. S. Milne, *Algebraic Groups* (2017), registered as
`milne-2017-algebraic-groups`: Corollaries 22.43 and 22.44 (printed p. 478, PDF p. 494),
Theorem 22.42 (printed p. 477), Proposition 4.19 (printed pp. 90–91) and Theorem 3.23 (printed
p. 71).

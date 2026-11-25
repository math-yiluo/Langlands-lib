# The identity-component necessity in Nagata's theorem

`Langlands.GroupScheme.nagataIdentityComponentNecessity` proves
`NagataIdentityComponentNecessityStatement.{u}` in every universe `u`. Let `k`
be a field of characteristic `p ≠ 0`, and let `G` be an affine group scheme of
finite type over `Spec k`. Suppose every finite-coordinate matrix
representation of `G` is the sum of its simple stable subspaces. Then the
canonical open identity component `finiteTypeIdentityComponent G` is of
multiplicative type. The canonical open and closed immersion
`finiteTypeIdentityComponentι G` has range `IdentityComponent.identitySet G`.
The theorem needs no smoothness, reducedness, perfectness or connectedness of
`G`.

## The implemented proof

The proof composes Library results.

1. Base change to the algebraic closure `K` of `k`. The field
   extension theorem `LinearReductivity.linearlyReductiveFieldExtension` shows
   that the base change `G_K` is again linearly reductive in the same all-test
   sense. That theorem uses normalized local right integrals and does not use
   Nagata's theorem.
2. Over `K`, apply `nagataConnectedFrobeniusReduction`. It reduces
   multiplicative type of the identity component of a linearly reductive group
   to two premises.
   - The case of a reduced ambient group is
     `linearlyReductiveReducedIdentity`. The reduction of the identity
     component is a smooth connected group without nontrivial connected
     closed unipotent subgroups, hence a torus. For a reduced ambient group
     the identity component is isomorphic to its reduction.
   - The first Frobenius kernel step uses `affineLinearEmbeddingStatement`. It
     supplies a closed finite-coordinate representation of the ambient group.
     `MatrixRepresentation.linearlyReductiveFrobeniusKernel` then shows that
     the kernel of its first matrix Frobenius is of multiplicative type.

   The reduction proves the general case by induction on a nilpotence exponent
   `p ^ r` of the coordinate algebra. It passes to Frobenius images and uses
   the extension theorem for groups of multiplicative type.
3. `IdentityComponent.FiniteType.baseChangeIso` identifies the identity
   component of `G_K` with the base change of `finiteTypeIdentityComponent G`.
   So that base change is of multiplicative type over `K`.
4. `K` is separably closed. By
   `MultiplicativeTypeSplitting.isFGDiagonalizable_of_isSepClosed`, this base
   change is isomorphic to an actual diagonalizable group with a finitely
   generated character group. This isomorphism, with the extension `K` of
   `k`, is the splitting datum in `IsMultiplicativeType` for
   `finiteTypeIdentityComponent G`.

The witness of the existential is `H = finiteTypeIdentityComponent G` with
`i = finiteTypeIdentityComponentι G`. Its open-immersion instance and its range
equation `IdentityComponent.FiniteType.range_finiteTypeIdentityComponentι` are
Library results.

## Independence from the full Nagata theorem

The proof uses neither `nagataLinearlyReductive` nor any assumed instance of
`NagataLinearlyReductiveStatement`. The module does not import
`Torus.NagataLinearlyReductiveProof`, `Torus.NagataSufficiencyProof` or
`Torus.NagataComponentOrderProof`, and no imported module imports them.

A development check computed the transitive closure of the constants in the
type and value of `nagataIdentityComponentNecessity`. It has 112058 constants,
of which 19851 are Langlands constants from 1587 modules. The only Langlands
constants whose names contain `agata` are this theorem and its auxiliary
proofs, `NagataIdentityComponentNecessityStatement`, and
`nagataConnectedFrobeniusReduction` with its statement and auxiliary proof.
`NagataLinearlyReductiveStatement` is not in the closure. The Nagata modules
that declare constants in the closure are `Torus.NagataReductionStatements`,
`Torus.NagataConnectedReduction` and `Torus.NagataFrobeniusImage`, besides
this module.

## Relation to the full theorem

The module `Torus.NagataLinearlyReductiveProof` contains a `private` theorem
with the same proof, used there to assemble `nagataLinearlyReductive`. This
module reuses that proof text. A private name cannot be
cited from other modules. This module states the same proof as
a public theorem of the exact statement. The identity-component
part of Nagata's theorem can therefore be imported without the sufficiency
and component-order parts.

## Provenance

The statement is the identity-component part of Milne, *Algebraic Groups*,
corrected reprint (2022), Remark 12.56, printed p. 249, with linear reductivity
as in Definition 12.52, printed p. 248. The proof follows the route of
Demazure–Gabriel, *Groupes algébriques I* (1970), IV §3, Theorem 3.6 and
Lemma 3.7, printed pp. 509–511. That route consists of the unipotent
obstruction, the first Frobenius kernel and an induction on Frobenius kernels.
The Library proofs of the individual steps are derived routes. Their own
Markdown records the details and sources.

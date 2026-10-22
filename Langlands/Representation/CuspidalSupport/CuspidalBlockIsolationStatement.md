# Finite-type isolation of a cuspidal constituent

`Langlands.CuspidalSupport.LeviCuspidalBlockIsolationTheorem` is a
proposition definition, not a proof. It records a reduced consequence of
Bernstein–Zelevinsky (1976), Lemma 3.26 and the proof of Proposition 3.28.

## Mathematical statement and Lean correspondence

For every prime `p`, actual `PadicField F`, compatible topological data `T`,
natural rank `n`, and block shape `B`, put
`G = B.Levi F.Carrier` and `H = determinantUnitSubgroup T B`.
The declaration explicitly installs `T.topology`. The field universe `uF`
and representation-carrier universe `uV` are independent; the two smooth
representations `A` and `D` belong to the same category
`SmoothRep.{0, uF, uV} ℂ G`, as required by its actual subquotient relation.

Assume that `D` is irreducible and `IsLeviCuspidal B D.representation`.
The latter is the published admissible-quasicuspidal predicate, so
admissibility of `D` is already included. The only condition on `A` is
smoothness: it need not be admissible, finite dimensional, finitely
generated, of finite length, or semisimple.

The conclusion says:

1. The actual restricted action
   `ρD = determinantUnitRestriction T B D.representation` is semisimple.
2. There exist a natural number `m` and actual invariant subrepresentations
   `V i : Subrepresentation ρD`, indexed by `Fin m`, such that every
   `(V i).toRepresentation` is irreducible and
   `(⨆ i, (V i).toSubmodule) = ⊤`. Thus their underlying submodules span
   the whole carrier of `D`.
3. There exist actual `G`-subrepresentations `S` and `Q` of `A`, with
   `IsCompl S.toSubmodule Q.toSubmodule`. Their underlying submodules have
   zero intersection and sum to the whole carrier.
4. The actual restriction of `S.toRepresentation` to `H` is semisimple.
   For every irreducible subrepresentation `W` of this restriction, there
   is an index `i : Fin m` and an actual representation equivalence
   `W.toRepresentation.Equiv (V i).toRepresentation`.
5. `D` is not a `SmoothRep.IsSubquotient` of
   `SmoothRep.subrepresentation A Q`.

Irreducibility and semisimplicity use Mathlib's
`Representation.IsIrreducible` and
`Representation.IsSemisimpleRepresentation`. The equivalence in item 4
is an equivariant complex-linear equivalence, packaged under `Nonempty`;
no auxiliary predicate hides the finite family or its coverage.
The subquotient relation in item 5 uses actual invariant submodules,
their actual quotients, and an isomorphism in the smooth category.

The family need not be pairwise nonisomorphic or linearly independent:
only its irreducibility and spanning property are asserted. Its length
is finite; the individual representations need not be finite dimensional.
No positivity hypothesis on `m` is needed, since irreducibility of `D`
and the spanning equation rule out an empty family.

## Original source and reduced conclusion

The source is I. N. Bernshtein and A. V. Zelevinskii,
*Representations of the group GL(n,F) where F is a non-Archimedean local
field*, Russian Mathematical Surveys 31:3 (1976), 1–68, English translation.
Registered source:
`bernstein-zelevinsky-1976-representations-gln`.
The retained PDF has SHA256
`72dc22eb9991112936a88327f00d0f02a16a2bf8747518ca0ecfeeadd188e50c`.
Printed and PDF page numbers coincide.

Section 3.20, p.34, defines `G°` by requiring each block determinant to be
a unit. This is the published `determinantUnitSubgroup T B`, whose actual
restriction construction is imported here. Lemma 3.26, p.36, decomposes
the restriction of any irreducible `G`-representation as a finite direct
sum of irreducible `G°`-representations. It supplies both item 1 and the
finite spanning family in item 2; the present statement retains only the
spanning consequence of the direct-sum assertion.

For cuspidal `D`, Theorem 3.21, pp.34–35, says that its restriction is
finite in the sense of section 2.40, p.26. Here “finite” means compact
matrix coefficients against the smooth dual, not finite dimension.
In the proof of Proposition 3.28, p.36, the irreducible summands `V_i`
are therefore finite. Sections 2.43–2.44, p.28, construct the isotypic
projections and split off each such type from an arbitrary smooth
representation. Section 2.44(a) provides a semisimple sum of copies of
the selected type and a complementary summand having no subquotient
of that type. Repeating this for the finitely many types gives `S`
as the sum of the selected isotypic pieces and the complementary `Q`.
Conjugation by `G` permutes the types occurring in the restriction of
`D`; as in the proof of 3.28, these pieces are consequently
`G`-subrepresentations, not just `H`-subrepresentations.

This construction gives the semisimplicity and explicit type coverage of
`S` required above. The source's exclusion of all selected
`H`-subquotients in `Q` implies the stated exclusion of `D` as a
`G`-subquotient: restriction is exact on the underlying vector spaces,
so a `G`-subquotient isomorphic to `D` would restrict to an
`H`-subquotient containing one of the irreducible `V_i`. Taking the
preimage of that subrepresentation under the quotient map would realize
that `V_i` as an `H`-subquotient of `Q`, contradicting the construction.

Only this reduced interface is stated. The classification of other
irreducible constituents of `S` by character twists, and Lemma 3.29,
are not part of the declaration. The source's stronger conclusions are
used here only to explain the provenance of the weaker explicit clauses.
The analytic and isotypic arguments remain proof obligations, not
additional hypotheses in the Lean proposition.

## Rank zero

The quantifier over `n` includes zero. This is an elementary
empty-product extension of the cited positive-rank discussion.
The positive block sizes force the length of a rank-zero block shape
to be zero. Thus `G` and `H` are trivial groups. An irreducible complex
representation `D` then has one-dimensional carrier. Its restriction
is irreducible and semisimple; take `m = 1` and `V 0 = ⊤`.
Every complex vector space is semisimple as a representation of the
trivial group, and all its irreducible subrepresentations are isomorphic
to `D`. Hence `S = ⊤` and `Q = ⊥` satisfy the claimed clauses:
the zero representation has no subquotient isomorphic to nonzero `D`.
This paragraph explains the extension; it does not assert a Lean proof.

## Scope

The module defines only this proposition. It imports the published
cuspidality, determinant-unit restriction, and actual smooth subquotient
constructions without changing their Lean or Markdown files. It neither
defines generic isotypic projectors nor proves their properties.
A proof of the displayed target is separate work.

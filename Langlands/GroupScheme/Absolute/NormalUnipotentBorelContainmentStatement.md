# Normal unipotent subgroups lie in every Borel subgroup

`Langlands.GroupScheme.NormalUnipotentBorelContainmentStatement.{u}` is a
proposition. Its proof is `Langlands.GroupScheme.normalUnipotentBorelContainment`
in `Langlands.GroupScheme.Absolute.NormalUnipotentBorelContainmentProof`, whose
Markdown explains the route.

## Statement

Let `k : Type u` be an algebraically closed field and `H` a smooth, affine,
connected group scheme over `Spec k`. Let `i : U ⟶ H` be a closed subgroup with
these properties:

- `U` is smooth, connected and unipotent (the Library's `IsUnipotent`);
- the range of `i` is normal in `H` on every test scheme.

Then the range of `i` is contained in the range of `c` on every test scheme, for
every Borel subgroup `c : C ⟶ H`.

## Source

J. S. Milne, *Algebraic Groups* (2017), Remark 17.31, printed p.361 (zero-based
PDF page 376). The remark says that a normal connected solvable subgroup variety
is contained in all Borel subgroups. The reason is the conjugacy of Borel
subgroups (17.9). A smooth connected unipotent group is solvable, so this
proposition is the unipotent case of that remark. Corollary 17.57's proof, printed
p.371 (zero-based PDF page 386), uses this fact for the unipotent radical of a
torus centralizer.

The hypotheses are unipotence and the Library's `IsAffineHom` assumption on `H`.
Milne's Chapter 17 assumes that all algebraic groups are affine (chapter
introduction, printed p.352, zero-based PDF page 367). The hypotheses also match
how the proposition is used in
`Langlands.GroupScheme.centralizerUnipotentBorelContainment_of_statements`. There
`H` is a closed subgroup of an affine group, so it is affine. The official author
errata snapshot `milne-2017-algebraic-groups-errata-2026-11-02` has no correction
to Remark 17.31 or 17.9.

Source: `milne-2017-algebraic-groups`, SHA256
`899b0f44f3c3ccfbaf5ed1cf9c180be7a8016b1c0e9709ca0c206304e5bd1cd0`.

# Nonzero integer multiplication is an isogeny over any base scheme

Worker 292 completed this internal assembly from the carried conditional
assembly by Worker 188 and Worker 292, using the published field theorem
by Worker 399.

`Langlands.GroupScheme.multiplicationIsogeny` proves exactly
`Langlands.GroupScheme.MultiplicationIsogenyStatement.{u}`. For any scheme
`S : Scheme.{u}` and actual group object `G : Grp (Over S)` with explicit
`IsCommMonObj G.X`, assume that the structure morphism `G.X.hom` is smooth,
proper and geometrically connected. Then for every integer `n ≠ 0`,
`IsIsogeny (multiplication G n)` holds. This means that the actual scheme
morphism `(multiplication G n).hom.hom.left` is finite, flat and surjective.
The theorem has no additional premise.

## Implemented proof

Introduce exactly the data and hypotheses quantified by the published
target, and install the three structure hypotheses as local instances.
The published `isIsogeny_multiplication_of_positive` reduces the integer
claim to the case of a positive natural number `m`. Its nonnegative case
uses nonzeroness to obtain positivity. Its negative case composes positive
multiplication with the involutive automorphism given by multiplication
by `-1`, using the published stability of isogenies under composition.

Apply the published `fiberwiseIsogeny` to the endomorphism
`multiplication G (m : ℤ)`, with the given smoothness and properness
hypotheses for both copies of `G`. It suffices to prove that its pullback
along `S.fromSpecResidueField s` is an isogeny for every point `s : S`.
The criterion supplies finiteness from properness and finite fibres,
flatness from its published fibrewise flatness theorem, and surjectivity
from surjectivity on residue-field fibres.

The identity `multiplication_baseChange` rewrites the pulled-back
endomorphism as multiplication on the actual group object

```text
Gs := (Over.pullback (S.fromSpecResidueField s)).mapGrp.obj G
```

over `Spec (CommRingCat.of (S.residueField s))`. Its commutativity is
supplied by the published base-change instance. Its structure morphism
is definitionally
`Limits.pullback.snd G.X.hom (S.fromSpecResidueField s)`.
Mathlib's base-change instances therefore give its smoothness,
properness and geometric connectedness from the three installed
instances.

Apply the published unconditional theorem `fieldMultiplicationIsogeny`
to `S.residueField s`, this same `Gs`, the three transported structure
hypotheses, `m`, and its positivity. This closes the fibre goal and hence
the exact target. The field theorem constructs a symmetric ample line
bundle, uses the multiplication pullback formula to prove the
scheme-theoretic kernel finite, and applies the finite-kernel isogeny
criterion. Those constructions are proved in its imported Library
dependencies; no field theorem or ample-existence assertion remains a
premise of the present assembly.

## Provenance and scope

This is a derived internal composition of the named Library theorems and
Mathlib's base-change instances. The target and its imported Lean and
Markdown pairs are unchanged. The geometric source correspondence is
J. S. Milne, *Abelian Varieties*, the 1986 article in the author's corrected
version dated January 2, 2022, registered as
`milne-abelian-varieties-1986-author-2022`, SHA256
`bffdf81c57c77420b5454b31270007989d12f332abea62424be15c424079fc7c`.
The retained source is
`literature/J. S. Milne - Abelian Varieties (1986 article, author revision 2022).pdf`.
Theorem 8.2, printed and one-based PDF p.13, supplies the positive
multiplication result over fields. Section 20's opening definition,
p.42, gives the smooth proper presentation with connected geometric
fibres; Corollary 20.2(c), p.43, states commutativity, which remains an
explicit hypothesis here. Proposition 20.7 and its proof, p.44, use
the field result and the fibrewise flatness criterion, then properness
and finite fibres, to obtain the relative isogeny assertion. These
passages and the retained author errata were read directly; the errata
directs readers to the corrected edition.

The present proof uses that fibrewise route for the finite, flat and
surjective conclusion. It needs no globally constant relative dimension:
no degree or uniform kernel-order formula is asserted. Negative
multipliers are covered by the imported inversion argument. The base
scheme is arbitrary, and the proof imposes no characteristic,
invertibility, noetherian, quasicompactness or connectedness condition
on the base. In particular, multiplication by a residue characteristic
is included. The field theorem is valid in every characteristic and
the relative argument asserts flatness throughout.

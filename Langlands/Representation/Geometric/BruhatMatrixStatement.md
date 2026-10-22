# Matrix prerequisites for p-adic parabolic Bruhat

Author: Worker 197.

This pair defines two propositions in `Langlands.Geometric`; it proves neither
proposition and assumes neither as data. It imports the published
`Langlands.Representation.Geometric.WeylDefinitions` without modification and
uses its actual permutation groups, block Weyl subgroups, upper block parabolic
subgroups, invertible matrices, and Mathlib double-coset quotients.

Both declarations are closed `Prop`-valued definitions, with arbitrary
field-carrier universe `uF`. Inside each proposition, the quantifiers range over
every natural number `p` with `[Fact p.Prime]`, every `F : PadicField.{uF} p`,
every natural rank `n` with `0 < n`, and every pair `B C : BlockShape n`.
The existing `BlockShape` carries ordered positive block sizes whose sum is `n`.
The existing `PadicField` carries a field with a finite-dimensional algebra
structure over the p-adic numbers. There is no additional topology parameter or
representation-space universe.

`PadicBruhatMatrixExistenceTheorem` says that for every
`g : GeneralLinear n F.Carrier` there exists an actual permutation
`w : Equiv.Perm (Fin n)` such that

```text
[permutation(w)⁻¹] = [g] in P_B \ GL_n(F) / P_C.
```

The permutation is not required to satisfy either minimality inequality. This
is the representative-level existence assertion needed for surjectivity onto
the parabolic double-coset quotient.

`PadicBruhatWeylReflectionTheorem` says that for any actual permutations `v,w`,
equality of their inverse permutation-matrix classes in
`P_B \ GL_n(F) / P_C` implies

```text
[v] = [w] in W_C \ S_n / W_B.
```

This expresses the injectivity obligation for the induced map on Weyl double
cosets. It does not assert that `v = w`, and it assumes no minimality of either
permutation. Well-defined descent of that map and uniqueness of minimal Weyl
representatives are separate obligations; they are not extra fields or
hypotheses of these definitions.

## Inverse convention and provenance

The published `GeneralLinear.permutation n F.Carrier w` sends the standard
basis vector `e_j` to `e_(w j)`. Both new propositions use the inverse of this
matrix. Consequently the Weyl quotient has left subgroup `blockWeyl C` and
right subgroup `blockWeyl B`, whereas the matrix quotient has left subgroup
`B.parabolic F.Carrier` and right subgroup `C.parabolic F.Carrier`. This is
the convention already used by the published `parabolicDoubleCoset` and
`PadicParabolicBruhatTheorem`.

Bernstein and Zelevinsky, *Induced representations of reductive p-adic groups I*,
Annales scientifiques de l'ENS (4) 10 (1977), 441–472, section 6.4, printed
page 468 (PDF page 29), states that the inverse-representative map induces a
bijection

```text
W_N \ W / W_M  ≃  P \ G / Q.
```

The original section 6.4 was read on PDF pages 29–30. Its first paragraph
supplies the quotient bijection and then specializes to unique minimal
representatives. Our two propositions are a derived separation of the
existence and injectivity content of that quotient bijection for actual
`GL_n`, with `P = P_B`, `Q = P_C`, `W_M = W_B`, and `W_N = W_C`. They are
not separately named theorems in the source. BZ77 cites Borel–Tits for the
Bruhat decomposition; this pair does not claim to verify that proof or to
prove the matrix prerequisites.

Registered literature ID: `bernstein-zelevinsky-1977-induced-i`.
Original PDF SHA-256:
`8424600228ab72c5937e45edceefcae410a2a0b8f5ebf282185691542aa89092`.
Retained original:
`/home/taskhub/central-library/Bernstein-Zelevinsky--Induced representations of reductive p-adic groups I--1977.pdf`.

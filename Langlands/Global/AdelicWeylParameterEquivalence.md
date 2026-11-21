# Linear equivalence of Weyl parameters

The theorem `exists_weylParameter_linearEquiv` identifies the published
`weylParameter l c π'` with the forward map of a complex linear
equivalence. It uses rational Levi inclusions `l : M → P` and
`l' : M' → Q`, an isomorphism `c : M' → M` and the supplied retraction
`π' : Q → M'` of `l'`.

A rational Levi inclusion yields an isomorphism on rational characters
by restriction. To prove injectivity, factor each test point of the
parabolic into a Levi component and a point of the geometric unipotent
radical. A character sends the radical component to the identity,
since the target is the split torus `𝔾ₘ`. Thus its restriction to the
Levi determines it on every test scheme. Pullback along a retraction
gives the inverse to restriction. In the source parabolic the Lean
proof uses a retraction supplied by the rational Levi hypothesis.

The proof composes the character restriction for `l`, the pullback
along `c`, and the inverse of the character restriction for `l'`.
Extending that additive equivalence by tensoring over `ℤ` with `ℂ`
gives the parameter equivalence. On each pure tensor its character
factor is the pullback along `π' ≫ c ≫ l`, which is the defining
formula of `weylParameter`.

This is the algebraic character-space identification used in
Bernstein–Lapid, *On the meromorphic continuation of Eisenstein series*,
§2.1, for the action of a rational Weyl representative on parameter
spaces. Its application to the functional equation uses the two
Levi inclusions from the parabolic root presentations and the
isomorphism field of `IsWeylConjugation`.

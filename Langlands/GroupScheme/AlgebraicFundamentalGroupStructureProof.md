# Structure of the algebraic fundamental group

The theorem `Langlands.GroupScheme.AlgebraicFundamentalGroup.algebraicFundamentalGroupStructure`
proves the published `AlgebraicFundamentalGroupStructureStatement` without additional
hypotheses. Its source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Construction 11.3.1, printed p. 427 (PDF p. 458). The quotient is the
actual cocharacter quotient of the actual scheme-theoretic preimage defined in
`AlgebraicFundamentalGroup.lean`.

The registered source is `kaletha-prasad-2023-bruhat-tits-new-approach`,
SHA-256 `05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`.
The Chapter 11 entries of the authors' November 1, 2024 corrections
(`kaletha-prasad-2024-corrections`, PDF pp. 43–46,
SHA-256 `23293f51e58d5ceecb91f834743f68058b98431797d2531142415d013fdf61ed`)
concern Section 11.7 and do not amend Construction 11.3.1.

The implemented proof first extends to an algebraic closure. The published
derived maximal split torus and maximal torus centralizer results supply a closed
self-centralizing source torus in the simply connected cover, mapping into the
chosen ambient torus. Its map to the full preimage comes from the pullback
universal property and the canonical comparison of pullback with base change.
The full preimage is already known to be a torus. Maximality of the source torus
therefore makes this comparison an isomorphism. Transport of maximality and
reflection under field extension prove that the actual preimage inclusion is
maximal over the original field.

The actual projection from the preimage to the chosen torus is a base change of
the composite of the finite simply connected covering and the closed derived
inclusion. It is finite, and remains finite after every field extension.
The published finite-homomorphism cancellation theorem then gives injectivity
on actual cocharacters, including inseparable coverings.

The chosen torus splits over the separable closure. Its actual cocharacter
lattice is consequently finitely generated over the integers, and the
surjective quotient map gives finite generation of the quotient.

The four `Choice` lemmas are internal consequences of the published constructions
and structural results used in this proof. They retain the actual preimage and
maps; no replacement torus or lattice is used in the conclusions. The theorem
does not assert the further identification of the image with the coroot lattice,
or the canonical comparisons between different choices.

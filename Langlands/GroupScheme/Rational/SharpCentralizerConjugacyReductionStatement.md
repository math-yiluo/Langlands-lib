# Actual-image centralizer conjugacy reduction statement

`SharpCentralizerConjugacyReductionStatement.{u}` is an internal proposition
over every field `k : Type u`. It concerns arbitrary commutative group-scheme
maps `a : A → G` and `a' : A' → G`, supplied representatives `j : Z → G` and
`j' : Z' → G` of their entire centralizer subgroup functors, and an arbitrary
actual group-scheme map `p : C → G`.

The premises are ordinary rational subgroup conjugacy of `a` and `a'`, the two
all-test centralizer representations, and a factorization of every `g ∈ G(k)`
as `p(c) j(z)` with actual rational points `c ∈ C(k)` and `z ∈ Z(k)`.
The conclusion gives a conjugating point in the literal range of `p` on rational
points, an actual isomorphism `e : Z ≅ Z'`, and the commuting square
`j ≫ Int(g) = e.hom ≫ j'`. The proposition neither assumes nor concludes
surjectivity of `p` on rational points.

The provenance is an internal consequence of the Library's subgroup conjugacy,
all-test centralizer and inner-isomorphism definitions. A centralizer point fixes
`a`; removing that factor from an ordinary conjugator transports its centralizer
representation to the centralizer of `a'`. Uniqueness of representatives then
gives the indicated isomorphism. This paragraph explains the intended reduction;
the present file only defines its proposition and supplies no proof.

For its motivating application, Kaletha–Prasad, *Bruhat–Tits Theory: A New
Approach* (2023), Fact 2.6.22 and Lemma 2.6.24, printed pp.104–105
(PDF pp.135–136), use the image-times-centralizer product and minimal-Levi
conjugacy. That source is registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`. The registered 2024 corrections,
`kaletha-prasad-2024-corrections`, Section 2.6, PDF pp.24–25, concern the
subsequent valued-field conventions. This proposition is the internal
arbitrary-field implication and contains no valuation assumption or unconditional
product, torus-conjugacy, or unramified quasi-splitness claim.

# Coefficient-model inclusion for actual smooth subquotients

Author: Worker 1747.

`Langlands.Whittaker.subquotientCoefficientModelInclusion` proves
`SubquotientCoefficientModelInclusionStatement` for independent group and
carrier universes. This is an internal consequence of the published smooth
character-localization exactness theorem, motivated by the component arguments
in JPSS 1983, Section 8.2, printed pages 445–448. It proves no local-factor
identity.

Let `q : U → σ` be the surjective intertwiner in the statement. The proof first
pulls the specified functional `ℓ` back along `q`, using `functionalsComap`.
The actual subtype inclusion `i : U → ρ` is an injective intertwiner.
`functionalsComap_surjective_of_smooth` extends the pulled-back functional to
an equivariant functional `L` on `ρ`. Its hypotheses are precisely the smoothness,
compact-subgroup limit and locally constant character assumptions retained in
the statement.

The extension equation gives `L(v) = ℓ(q(v))` for every `v` in `U`.
If `L` were zero, surjectivity of `q` would make `ℓ` zero. For each vector
`w` of `σ`, choose a lift `v` in `U`. Equivariance of `q` and the extension
equation give
`L(ρ(g)v) = ℓ(q(U(g)v)) = ℓ(σ(g)w)` for every `g`. Thus the corresponding
coefficient functions are equal in the unchanged equivariant function space.
This proves the required inclusion of the actual coefficient images.

The proof uses no irreducibility, admissibility, finite-length or genericity
assumption. Its source provenance is the internal adapter described in the
statement's Markdown, rather than a claim that JPSS states this general
topological-group theorem.

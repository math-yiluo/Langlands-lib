# Levi subgroups over affine bases

`Langlands.GroupScheme.relativeLeviAffineExistence` proves
`Langlands.GroupScheme.RelativeLeviAffineExistenceStatement.{u}` for every
universe `u`. Given an affine scheme `S`, a reductive group scheme `G` over
`S`, and a relative parabolic `i : P ⟶ G`, it gives an actual homomorphism
`l : L ⟶ P` satisfying `IsRelativeLeviSubgroup l`. The base may be
non-noetherian or disconnected. [Target statement](AffineExistenceStatement.md)

The proof applies `relativeUnipotentRadical` to obtain a relative unipotent
radical `r : U ⟶ P`. Its certificate gives smoothness of `U` and closedness of
the immersion into `P`. The composite of this immersion with the affine
structural morphism of `P` gives affineness of `U` over `S`.
The theorem `relativeUnipotentRadicalFiltration` gives the finite series
with vector-bundle additive quotients on this same `U`.

The theorem `relativeLeviTorsor` supplies a scheme `X` over `S` representing
Levi subgroup images, an action of `U`, and the fpqc torsor conditions.
With this action and the finite series, `relativeUnipotentAffineTorsor`
gives a section of `X → S`.
The representing correspondence at the identity test of `S`, transported
along the canonical identity pullback comparison by
`ModuliRepresentation.exists_isRelativeLeviSubgroup_of_section`, gives the
required Levi inclusion.

This is the existence argument of Brian Conrad, *Reductive group schemes*
(2014), Corollary 5.4.8, p. 179, with the filtration from Theorem 5.4.3 and
the Levi torsor from Corollary 5.4.6. The Lean proof uses the published
section theorem for actual fpqc torsors to implement the affine vanishing
step. The registered source is `conrad-2014-reductive-group-schemes`.

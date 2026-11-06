# Scalar endomorphisms on actual rational points

Worker 1581 supplies an internal scalar-space construction for the endomorphism
argument in Renard VI.5.3 and VII.1.3. This module does not prove the geometric
lemma, Frobenius reciprocity, or the maximal-Levi endomorphism dichotomy.
Its field universe `u`, group universe `uG`, and carrier universe `uV` remain
independent where the corresponding data occur.

The construction is derived from published proofs. It is motivated by
David Renard, *Représentations des groupes réductifs p-adiques*, version of
9 July 2026, VI.5.3 (printed p.173 / one-based PDF179) and VII.1.3.1
(printed p.225 / PDF231), where irreducibility makes an endomorphism space
one-dimensional. The registered source is
`renard-2026-representations-groupes-reductifs-padiques`, SHA-256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
These passages and the normalized-adjunction passage VI.1.2 (PDF141–142)
were read. No project errata note for this source was found.

`separableSmooth_scalarEndomorphism` combines
`Langlands.Whittaker.MirabolicRigidity.rank_le_aleph0` with
`Langlands.countableDimensionalSchur`. The first theorem gives a countable
algebraic dimension for an irreducible smooth representation of a separable
topological group. The second theorem makes every equivariant endomorphism a
unique complex scalar times the identity. Admissibility is not a hypothesis.

`separableSmoothEndomorphismEquiv` is the complex linear equivalence from `ℂ`
to the actual endomorphism space whose forward map sends `c` to `c • id`.
Existence of the Schur scalar proves surjectivity and its uniqueness proves
injectivity. The application equation identifies this forward map.

For a connected reductive group over a nonarchimedean local field,
`rationalPoint_rank_le_aleph0` installs exactly
`rationalPointTopology F G.X`. The published
`rationalPoint_secondCountableTopology` supplies second countability:
the local field has a countable base, finite-type affine points admit finite
coordinates, and the rational-point comparison is a homeomorphism. Affineness
and local finite type come from connected reductivity. The published
`rationalPoint_isTopologicalGroup` supplies the group topology. The preceding
smooth orbit rank bound then applies.

`rationalPoint_scalarEndomorphism` applies countable-dimensional Schur to this
rank bound. `rationalPointEndomorphismEquiv` specializes the scalar
parametrization to the same topology. Finally,
`leviPoint_scalarEndomorphism` specializes the scalar theorem to a rational
Levi, using its connected reductivity. The published `leviPointTopology` is
definitionally this canonical rational-point topology, so the theorem applies
to the exact topology used by the represented parabolic functors.

# Rational geometric terms in the literal standard family

This internal specialization of `GeometricTermReduction` retains the actual
rational-point family, canonical `pointTopology`, every minimum point Weyl
representative and every normalizer lift. The point normalizer and full
centralizer comparisons, the supplied scheme Coxeter system, the standard
Levi intersection statement and both all-test twisted-intersection properties
remain explicit structural inputs.

`pointStandardIntersectionTermK0` constructs a full integer-linear map from
exact finite-length K0 of the coarse source Levi `L_J` to that of the coarse
target Levi `L_I`. Its source fine index is `intersectionLeviIndex pointCs I J w`
inside `J`; its target fine index is
`intersectionLeviIndex pointCs J I w⁻¹` inside `I`. It composes literal restricted
normalized Jacquet restriction, the canonical subgroupOf identification,
actual inverse conjugation by the supplied lift, the target subgroupOf
identification, and literal restricted normalized induction. Both fine-Levi
inclusions and actual conjugation membership are derived from the rational
intersection adapters.

Private helpers derive restricted Jacquet short-exactness from the compact
subgroup limit premise and restricted induction short-exactness from closedness,
continuous standard Levi projection and compact-open cofinality in the closed
coarse Levi. Finite-length preservation is exactly the supplied literal source
Jacquet and target induction preservation. No preservation property of an
actual geometric factor is an additional assumption.

`pointGeometricTermK0_eq_standard` identifies the complete actual rational
geometric-term map with that standard term. It rewrites the exact source
radical and target parabolic/radical labels through
`leviIndex_intersectionLeviIndex`, uses the already derived source/target Levi
identities and decompositions, and specializes
`geometricTermK0_eq_standardOfEq`. Equality-identification maps commute with
actual conjugation in that generic result, so this is equality on every virtual
finite-length class, with all exact-sequence relations retained. The carrier
universe remains `max (u + 1) v` for independent `u` and `v`, and the normalized
functors retain their existing Haar characters.

The provenance is internal specialization of the named generic factorization
and the rational intersection constructions. The geometric expansion,
normalized induction stages, induced Weyl-conjugacy comparison, structural
input proofs and final Aubert induction equation remain separate obligations.
The published final target is unchanged.

# Admissible complementary Jacquet parts on the actual Levi points

Author: Worker 17.

This is a derived supporting construction for Renard,
*Représentations des groupes réductifs p-adiques*, French edition dated
9 July 2026, VII.2.3, printed p.229 / PDF p.235 (registered source
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`).
That lemma decomposes the normalized Jacquet module into its unitary and
nonunitary characteristic parts and asserts temperedness of the unitary part.
Here the actual Levi representations are proved admissible, and the
complementary decomposition is given its coproduct universal property.

The field and representation carrier have independent universes `u` and `v`.
The ambient topology is the canonical rational-point topology, with the
published local compactness and nonarchimedean hypotheses. Every parabolic,
rational Levi, matching radical, multiplication isomorphism and split
component is supplied as actual data. The Levi uses `leviPointTopology l hl`.
The source hypothesis is precisely `IsNormalizedExponentTempered hG π`;
there is no separate Jacquet-admissibility or presentation hypothesis.

`IsNormalizedExponentTempered.isAdmissible_leviJacquetFunctor_obj` transports
the published pointwise admissibility theorem through `leviPointsEquiv`.
The pointwise theorem obtains a compatible presentation and source
admissibility from temperedness, then applies the published dynamic
contraction and normalized Jacquet admissibility results. Admissibility
is preserved under this topological group equivalence.

`IsNormalizedExponentTempered.isAdmissible_leviUnitaryJacquetModule` and
`IsNormalizedExponentTempered.isAdmissible_leviNonunitaryJacquetModule`
apply the published injective-intertwiner theorem to the literal
inclusions of the two submodules into the transported Jacquet module.
The scalars are complex numbers, so the required Noetherian scalar-ring
hypothesis is available.

`leviJacquetPartsCofan` has the normalized Jacquet module as its vertex.
Its `true` leg is `leviUnitaryJacquetModuleι`, and its `false` leg is
`leviNonunitaryJacquetModuleι`. Thus its objects, actions and arrows are the
published actual Levi modules and their inclusions.
`temperedLeviJacquetPartsCofanIsColimit` constructs its universal property:
the published tempered-source splitting makes the two underlying
submodules complementary, and `SmoothRep.complementaryCofanIsColimit`
extends any two morphisms by adding their values on the unique two
components. This is a coproduct in smooth representations of `M(F)`.

The construction imports existing published results by Lean name; it does
not alter their definitions. Its provenance is the composition of
pointwise admissibility, topological transport, inheritance under an
injective intertwiner, and the algebraic coproduct construction for
complementary invariant subspaces.

This supplies admissibility and an actual coproduct decomposition for the
first host-task target. It does not establish the arbitrary-parabolic
exponent cone condition for the unitary module, so it does not prove
`UnitaryJacquetPartTemperedStatement`. The exact restriction proposition
and the square-integrability criterion remain separate results.

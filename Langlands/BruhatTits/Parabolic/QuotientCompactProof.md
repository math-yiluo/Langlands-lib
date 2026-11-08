# Compactness of actual dynamic-parabolic quotients

`dynamicParabolicQuotientCompact` proves the unchanged published
`DynamicParabolicQuotientCompactStatement` at an arbitrary universe `u`. Fix a
nonarchimedean local field `F`, a connected reductive group scheme `G` over
`Spec F` and a rational cocharacter `χ`. Let `P` be the identity-test points of
`Dynamic.parabolic χ`. Then the `gP` quotient `Gpts ⧸ P` and the `Pg` quotient
`Langlands.Induction.LeftQuotient P` are both compact. Each carries the
quotient topology of the canonical `rationalPointTopology F G.X`. The theorem
adds no hypothesis; every field, group, cocharacter and parabolic covered by
the target is covered by the proof.

The proof applies the comparison theorem
`dynamicParabolicQuotientCompact_of_flag_and_proper_points` to two published
unconditional theorems.

1. `Langlands.GroupScheme.dynamicFlagQuotientExistence` proves
   `DynamicFlagQuotientExistenceStatement`. For every field `k`, every connected
   reductive `G` and every cocharacter `χ`, it gives one actual relative scheme
   `Q` and morphism `π : G.X ⟶ Q`. Here `Q` is proper over `k`. On every test
   scheme, `g ≫ π = h ≫ π` holds exactly when `g⁻¹ * h` lies in
   `Dynamic.parabolic χ`. Each rational point of `Q` lies in an open subscheme
   with an algebraic section of `π`. The statement has no restriction on the
   field or the cocharacter. It therefore includes finite and infinite residue
   fields of either characteristic, nonsplit groups, the trivial cocharacter and
   `P = ⊤`.
2. `Langlands.AlgebraicGeometry.PointTopology.localFieldProperPointProperties_proof`
   proves `LocalFieldProperPointProperties K hK` for every nondiscrete Hausdorff
   locally compact topological field `K`. The adapter
   `properSchemePointCompactness_of_localFieldProperties` takes its compactness
   component. Using the original field topology of `F`, the adapter supplies
   `T2Space F` from `localField_t2Space` and nondiscreteness from
   `localField_not_discreteTopology`. For every proper `Q` over `F`, it yields
   compactness of the actual point space `RingPoint F Q F` in
   `schemePointTopology F Q F`. This is exactly the comparison theorem's
   proper-point premise.

Inside the comparison theorem, Mathlib's local-field instances and the
compatible additive uniformity give continuous multiplication and
`IsOpenUnits F` for the original topology. The map `g ↦ g ≫ π` on actual
points is continuous. The algebraic sections near every rational point of `Q`
become continuous local sections of it. Both facts are transported to `Gpts`
through the published homeomorphism between identity-test and evaluation
points. The sections show in particular that `Gpts → RingPoint F Q F` is
surjective. Exactness of the fibers identifies its fibers with the actual `gP`
cosets. The local-section quotient comparison therefore gives a homeomorphism
`dynamicParabolicFlagHomeomorph` from `Gpts ⧸ P`, in its canonical quotient
topology, onto `RingPoint F Q F` in `schemePointTopology`. Since `Q` is
proper, its point space is compact, so `Gpts ⧸ P` is compact. Finally,
`dynamicParabolicQuotientInversion` is the homeomorphism of the two canonical
quotient topologies induced by inversion. It uses continuity of inversion on
the canonical rational-point topological group. It carries compactness from
the `gP` quotient to the `Pg` quotient `Langlands.Induction.LeftQuotient P`.

The target corresponds to Renard, V.5.1 corollary, printed page 123 / PDF page
129: `G/P` is compact for every parabolic subgroup. This Lean proof does not
follow the source's route through the adapted compact subgroup. It goes
through the algebraic flag quotient and compactness of points of proper
schemes over locally compact fields. The K0-conjugacy assertion of the same
corollary is not proved here.

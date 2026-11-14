# Pointed dynamic presentations of relative parabolics

This internal construction extends a supplied dynamic presentation of a
relative parabolic residue fibre to a pointed etale neighbourhood, while
recovering exactly its prescribed ambient cocharacter. It combines the
published cocharacter factorization through a represented dynamic parabolic
with pointed cocharacter lifting, local persistence of a supplied presentation,
relative parabolic base change, source geometry and pullback comparison
coherence. No new assertion from external literature is introduced.

For an arbitrary scheme `S`, a reductive group scheme `G`, a relative parabolic
inclusion `i : P → G`, a point `s : S` and an ambient cocharacter `ν` over
`κ(s)` presenting the range of `i_s`, `pointedPresentation i hG hi s ν hν`
returns an actual scheme `U`, an etale map `p : U → S`, a map
`b : Spec κ(s) → U` with `b ≫ p = S.fromSpecResidueField s`, and a cocharacter
`χ : G_m,U → G_U`. Its dynamic parabolic is the range of the actual pullback
of `i` along `p`, as subgroup functors on all test schemes. Its value along
`b`, followed by the canonical direct-pullback comparison, equals `ν` as a
group-scheme homomorphism. `PointedPresentationData` records these data and
equalities.

The residue inclusion is closed and monic. The dynamic factorization gives a
cocharacter `χ₀` into `P_s` with ambient composite `ν`. Pointed etale
cocharacter lifting applies to the smooth affine group `P` and recovers `χ₀`
exactly. On that etale neighbourhood, relative parabolic base change gives
the smooth affine subgroup, closed residue fibres and a monic inclusion.
The source geometry theorem and reductivity give geometrically connected
fibres for both groups. Exact ambient recovery supplies the presentation on
the specified field-valued fibre, so `parabolicPresentationNeighbourhood`
gives an open restriction with the prescribed presentation. The composite
of this open map and the etale projection is etale and retains the same
residue point. Pullback naturality and range invariance transfer the
presentation to the direct pullback, and `pullbackCocharacter_recovers`
retains the exact value `ν`.

The construction assumes the initial residue-fibre presentation. It does not
assert that an arbitrary lifted cocharacter presents the subgroup, nor does
it by itself produce a conjugator. No affine, reduced or Noetherian condition
on `S`, and no global closedness hypothesis on `i`, is imposed. The
construction works in one arbitrary universe.

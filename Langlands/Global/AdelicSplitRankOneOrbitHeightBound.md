# Statement: the arithmetic rank-one height bound for split groups

`SplitRankOneParabolicRationalOrbitHeightBoundStatement` is the split case of the
published `RankOneParabolicRationalOrbitHeightBoundStatement` (module
`Langlands.Global.AdelicRankOneOrbitHeightBound`). It has the same quantifiers
and hypotheses, plus one more: the given maximal split torus `i : T ⟶ G` is
also a maximal torus (`IsMaximalTorus i`), so `G` is split over the number
field `F`.

In more detail, it quantifies over
- every number field `F` in universe `u`;
- every affine finite-type connected reductive group scheme `G` over `F`;
- every actual maximal split torus `i : T ⟶ G` that is also a maximal torus;
- every generic cocharacter `ν` whose set of simple relative roots is a
  singleton `{α}` (positive semisimple relative rank one);
- every finite-coordinate representation `ρ` and coordinate index `j` whose
  exact selected-line stabilizer, over all relative scheme tests with unit
  scalars, is the empty-index standard parabolic `standardParabolic i ν ∅`.

The conclusion is the published `HasUniformNormOneRationalOrbitHeightBound F G
ρ (Pi.single j 1)`. There is one real constant `C > 0` such that every ambient
norm-one adelic point `g` has an actual rational point `q` with selected-vector
height `orbitHeight F G ρ e_j (g q) ≤ C`.

The theorem `splitRankOneParabolicRationalOrbitHeightBound_of_rankOne` records
that the general statement implies this one: forget the extra hypothesis
`IsMaximalTorus i`.

Provenance: this is a derived restriction of the published internal rank-one
interface to split groups. It corresponds to the split rank-one case of
Springer, *Reduction theory over global fields* (1994), §3.3, which is the base
case of the split reduction theory in §3.4–3.5. The nonsplit case is reduced to
split groups by Galois descent in §3.6. The module asserts the bound without
proving it, and it does not prove the general rank-one statement.

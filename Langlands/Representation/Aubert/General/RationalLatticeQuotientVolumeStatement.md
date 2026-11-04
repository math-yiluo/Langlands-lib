# Upper Haar volumes of actual rational lattice cells modulo the full center

`Langlands.Aubert.General.RationalPointFamily.RationalLatticeQuotientVolumeStatement`
is a derived geometric and measure-theoretic proof target. The field ranges over
all nonarchimedean local fields, including positive characteristic. The group is
any connected reductive group scheme with the supplied actual maximal split
torus, generic cocharacter and global `StandardCocharacterStatement`. No split or
quasi-split hypothesis on the group is imposed. The finite ray-index type has a
universe independent of the field universe.

The topology is the canonical evaluation topology `pointTopology` on the actual
rational-point group `H`. Local compactness, the nonarchimedean group property,
Hausdorffness and closedness of each actual standard unipotent subgroup are
retained as explicit premises. The geometric input is a supplied
`SimultaneousStandardBasisAt i ν K0`. This statement does not construct that basis
or the special compact subgroup needed in the square-integrability application.

For each ray `a`, choose a finite set `J a` of the literal simple-root labels and
an actual cocharacter `x a`. Its pairings vanish on `J a` and are nonnegative
outside `J a`. Supply a point `z a` of the full center of the actual standard
Levi for `J a`, whose ambient value is exactly the uniformizer evaluation of
`x a`. Write `δ_a` for
`HaarModulus.closedRestrictCharacter` of the actual radical for `J a`, evaluated
at `z a` and viewed as a positive real number.

For every compact open subgroup `K` of `H`, every finite set `F₀ ⊆ H`, and every
supplied Borel Haar measure `μ` on `Q = H / Subgroup.center H`, the conclusion
provides a real constant `D > 0`. For all natural tuples `n` and every `t ∈ F₀`,
the actual subset

```text
q(K * uniformizerPowers(sum_a n_a • x_a) * t * K)
```

is measurable and has measure at most
`ENNReal.ofReal (D * product_a δ_a^(-n_a))`. Here `q` is the ordinary quotient map
by the full abstract center of the entire rational-point group, with its
quotient topology. The constant may depend on the supplied data, rays, subgroup,
finite set and Haar measure, but is uniform in `n` and `t`. The real upper bound
also implies finiteness of each cell measure. There is no disjointness or
covering assertion for these cells. Empty ray families and empty root sets are
allowed. For an empty ray family the product is one.

The internal derivation intended for this target uses a common sufficiently
small member `L` of the supplied simultaneous basis inside `K`. A ray may need
a positive integral multiple before it lifts to the supplied split component.
After making that comparison, the component character chamber gives contraction
on `L ∩ U_J` and expansion on the opposite intersection; the point centralizes
`M_J`. Unique ordered intersection factorization should reduce
`[L : L ∩ z_a^r L z_a^(-r)]` to the index of the contracted unipotent
intersection. Haar scaling on that actual unipotent group then gives
`δ_a^(-r)`. Division of the natural exponents by the fixed positive multiples
leaves only finitely many residual powers, whose indices can enter the constant.
Index submultiplicativity controls powers, products and the finitely many
translates. Finite-index comparison passes from `L` to `K`, and projection
to the central quotient can only decrease the relevant coset count.
The left-Haar double-coset measure formula gives the intended upper bound.
Compactness and openness of the quotient image of `K` give measurability and
finite measure. These are obligations for a proof of this statement.

Each ray uses its own actual standard-parabolic Haar character, matching the
weights in `RationalLatticeCoefficientDecayStatement`. No comparison with a
minimal-parabolic character is required in this formulation. A proof must
establish the contraction, factorization and index steps for these actual
groups; no index formula, volume bound, right-invariance law or desired
integrability conclusion is supplied as a premise. This derived statement is
not a proof of the general strict Jacquet square-integrability criterion.

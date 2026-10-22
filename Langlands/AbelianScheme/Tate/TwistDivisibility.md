# Full and prime-to-p integral Tate twists

This module constructs the full and prime-to-`p` inverse limits of actual roots
of unity, their continuous residue scalar actions, and the maps induced by
ring homomorphisms. Its namespace is `Langlands.TateTwist.Divisibility`.
`Langlands.TateTwist.Full R` and `Langlands.TateTwist.Away R p` are public
abbreviations for the two specializations.

## Provenance and dependencies

This is a derived extension of the published
`Langlands.AbelianScheme.Tate.Twist` construction from prime powers to positive
integers ordered by divisibility. It imports that module's actual groups
`Level R n = Additive (rootsOfUnity n R)` and its power transitions, without
redefining them. It also imports `Langlands.AbelianScheme.Tate.Scalars` and
reuses its residue maps from the published full and prime-to-`p` scalar rings.
Those rings are `Langlands.Global.ProfiniteIntegerRing` and
`Langlands.Global.PrimeToProfiniteIntegerRing p`, not newly supplied rings.

The underlying source for roots-of-unity twists is B. Edixhoven,
G. van der Geer and B. Moonen, *Abelian Varieties*, preliminary draft built
2012-02-08, Chapter X (10.8), printed p.144 (PDF p.148), with the prime and field
convention on printed p.141 (PDF p.145). Registered source:
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The original passage was read directly in developing the imported construction;
its retained excerpt was reread for this extension. No source-specific errata
file was present in the available Library.

The cited passage treats the prime-adic twist over a separable closure. The
all-positive and coprime index sets, arbitrary commutative coefficient ring,
residue scalar actions and universal-property API here are an internal
extension, not an assertion that the source states these exact interfaces.
The extension uses only the imported finite-level power maps and their
compatibility with reduction of residue scalars. It makes no geometric
finiteness or freeness inference. The coherent-family and universal-lift
implementation adapts Worker 143's published integral Tate construction;
the module and continuity proofs adapt Worker 142's published scalar-action
construction. Both workers are credited as coauthors.

## Objects and topology

Let `R` be any commutative ring and let `P : ℕ → Prop`. The shared type
`Langlands.GroupScheme.Tate.Index P` consists of positive integers `n` satisfying
`P n`. `Integral R P` is the additive subgroup of families

```text
x_n ∈ Additive (rootsOfUnity n R)
```

such that for every selected pair `n ∣ m`, raising the underlying unit of
`x_m` to the power `m / n` gives the underlying unit of `x_n`. Every selected
pair is required; no chosen cofinal sequence or compatible generators are
inputs. The imported `transition_self` and `transition_comp` establish the
identity and composition of those power maps. Positivity of the indices is
used for identity.

`Full R` selects every positive integer. `Away R p` selects those coprime to
`p`; it is defined for any natural `p`, with the usual prime-to-`p`
interpretation when `p` is prime. Each root group has the published discrete
topology. The inverse limit has the induced topology as a subgroup of their
product and an `IsTopologicalAddGroup` instance. No finiteness of these root
groups or compactness of this limit is asserted for an arbitrary ring `R`.

`evaluation` is the additive coordinate projection and is continuous.
`evaluation_transition` gives its compatibility with the power maps.
`lift` maps an additive group into the inverse limit from a compatible family
of additive coordinate maps. `evaluation_lift` is its coordinate formula;
`lift_unique` proves uniqueness by equality of every coordinate.
`continuous_lift` proves continuity when all coordinate maps are continuous.

`restrictAway R p` forgets the coordinates not coprime to `p`. It is additive
and continuous by the universal lift. No surjectivity claim is made.

## Residue scalars

The helper `ScalarAction.module` accepts a commutative ring `A`, maps
`r_n : A →+* ZMod n`, and their compatibility with every selected residue
reduction. Its action on a family is

```text
(a • x)_n = r_n(a) • x_n.
```

Here the action on the right is the published `ZMod n` action on actual roots
of unity. The proof that this family is coherent uses
`TateTwist.transition_zmod_smul` and compatibility of `r_n`. The module laws
hold coordinatewise. This helper does not assume a Tate module or a basis.
Its continuity theorem assumes a topology on `A` and continuity of each
`r_n`; each coordinate of the joint scalar-action map then factors through
the discrete product `ZMod n × Level R n`.

`fullModule` and `fullContinuousSMul` instantiate this construction for the
actual full residue inverse-limit ring, for every `P`. In particular they
apply to `Full R` and to `Away R p`. `awayModule` and `awayContinuousSMul`
give the additional action of the actual prime-to-`p` residue ring on
`Away R p`. The evaluation lemmas expose exactly these residue formulas.
`full_intCast_smul` and `away_intCast_smul` show that an integer embedded in
either scalar ring acts by the usual integer multiple of the additive group.

`restrictAway_smul` expresses compatibility of restriction with the published
scalar-ring restriction. `full_smul_eq_away_smul` identifies the full scalar
action on the away limit with its action through that restricted scalar.
Both are coordinate identities, not comparisons with a newly chosen ring.

## Ring-map functoriality

For an actual ring homomorphism `f : R →+* S`, `map P f` applies the imported
`TateTwist.levelMap f n` at each coordinate. Thus it applies `f` to the
underlying unit of each root of unity. Its coherence follows from the
published compatibility of `levelMap` with the power transitions.
`evaluation_map` gives the coordinate formula, `map_id` and `map_comp` give
covariant identity and composition, and `continuous_map` follows from
continuity into each discrete root group.

`fullLinearMap P f` bundles that same additive map as linear over the full
profinite-integer ring. `awayLinearMap p f` bundles it as linear over the
prime-to-`p` ring. Their proofs use `ZMod.map_smul` at every coordinate.
`restrictAway_map` proves that ring-map functoriality commutes with restriction
to the away indices.

## Scope

The construction retains the actual roots of unity without selecting a basis
or trivializing an automorphism action. Rationalization, rational adelic
scalar identification, automorphism actions on these full and away limits,
and comparisons with products of the prime-adic twists are separate units.
The scheme-theoretic identification with points of `μ_n`, geometric monodromy,
Weil pairings, rank-one theorems and their characteristic hypotheses are
separate obligations. The elementary construction here needs neither a field
nor an invertible torsion order; those general parameters do not imply the
geometric conclusions.

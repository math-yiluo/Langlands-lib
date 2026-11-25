# Strictly lower-rank orbit finiteness for VIII.2

This derived interface restricts the exact local VIII.1.2 predicate to actual
relative semisimple ranks strictly below a natural-number bound. It supplies
the finiteness input for the proper spectral support step of Waldspurger VIII.2.
Synthesis reconstruction is a separate induction premise.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), printed p.321 (PDF p.87), the induction
paragraph preceding VIII.2 and the proper-Levi use of VIII.1.2 and VIII.1.3.
Registered source `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The paper assumes both VIII.1 theorems on strictly smaller semisimple ranks.
This interface isolates only the VIII.1.2 part of that assumption. The explicit
Lean packaging and the elementary specialization proofs are derived content.

The field is any nonarchimedean local field under the Library convention,
including its finite residue field requirement. The groups are affine locally
finite type connected reductive group schemes. There is no characteristic,
splitting, quasi-splitness or positive-rank restriction. Field universe `u`
and complex representation-carrier universe `uV` remain independent.
The imported local predicate retains canonical rational-point topology,
every split component, every quotient Haar measure and every compact open
level of the actual complex smooth representation category.

## Definitions and implemented proofs

All declarations below belong to `Langlands.HarishChandraSchwartz`.

| Declaration | Content | Status and dependencies |
| --- | --- | --- |
| `RationalStrictlyLowerRankOrbitFinitenessStatement n` | For every indicated group and maximal split torus, `relativeRootRank i < n` implies the exact `RationalLocalDiscreteSeriesOrbitFinitenessStatement G`. | Prop-valued restricted analytic premise; no finiteness proof. |
| `rationalStrictlyLowerRankOrbitFiniteness_mono` | A premise at bound `m` restricts to bound `n` when `n ≤ m`. | Applies the same premise after transitivity of the natural-number inequality. |
| `rationalStrictlyLowerRankOrbitFiniteness_zero` | The restricted premise at bound zero is vacuous. | Eliminates an impossible natural-number inequality. |
| `rationalLocalOrbitFiniteness_of_rank_lt` | Specialization to a fixed actual group whose rank is below the bound. | Direct application; all local field and group hypotheses remain explicit. |
| `rationalLocalOrbitFiniteness_properLevi_of_lowerRank` | Local VIII.1.2 on every closed connected reductive model of each literal proper semistandard Levi. | Uses the actual torus factorization, its maximal splitness, and the explicit `SemistandardProperLeviRankStatement` premise. |
| `rationalLocalOrbitFiniteness_properLevi_of_lowerRank_at_torus` | The same specialization at any maximal split torus in the same Levi model. | Uses `relativeRootRank_properLevi_lt`, retaining its actual change-of-torus comparison and strict-decrease premise. |

The rank is the published `relativeRootRank`, the rational dimension of the
span of all actual relative roots. It is not the full split rank and is not an
arbitrary numerical assignment. Properness is inequality of the all-test
parabolic subgroup functor with the whole group. The model is the published
`RationalSemistandard.LeviModel`: its inclusion represents precisely the literal
Levi, is closed, and has a connected reductive source. Reductivity supplies the
model's affine and locally finite type instances. The first proper-Levi adapter
factors the ambient torus through that actual inclusion and applies the rank
premise at this inherited maximal split torus. The second uses the already
established rank independence to work at any maximal split torus of the model.

The bound `relativeRootRank i` excludes the ambient group. A well-founded
induction on natural-number rank can supply this restricted finiteness premise
from its induction hypotheses for smaller ranks. At rank zero the premise is
proved without any analytic input. The emptiness of the proper parabolic part
itself is the separate conditional result
`isEmpty_properSemistandard_of_rank_zero` in `GroupScheme.Rational.SemistandardProperLeviRank`. These statements do
not identify split rank zero with semisimple rank zero.

## Dependency boundary

The local predicate `RationalLocalDiscreteSeriesOrbitFinitenessStatement` is
defined in `RationalLocalOrbitFiniteness`; this module imports it and does not
redefine either its full-Levi or proper-Levi restrictions. The pointwise
proper-Levi conclusions are exactly that local predicate, the input of
`RationalSemistandard.ProperLeviOrbitFiniteness` (module `RationalSemistandardThetaFixed`);
the module `RationalStrictlyLowerRankProperLeviFiniteness` packages them into that premise.
The strict proper-Levi rank comparison is the explicit structural premise
`SemistandardProperLeviRankStatement` here; it is proved as `semistandardProperLeviRank`
in `GroupScheme.Rational.SemistandardProperLeviRankProof`. Its elementary torus and
boundary adapters are reused.
The actual full semistandard index, literal Levi models and rank definitions
are imported. No new spectral index, orbit measure or representation model is
introduced here.

Neither local synthesis reconstruction, same-rank VIII.1.1 or VIII.1.2, full
Fourier support, an inverse, nor a projector is assumed or constructed in this
module. Lower-rank finiteness is used only for proper support. Detection of
zero induced constant terms requires a separate lower-rank reconstruction
input, not treated here.

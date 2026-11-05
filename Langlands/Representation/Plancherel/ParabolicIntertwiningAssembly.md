# Assembly of the host conclusion from convergence and domination

Author: Worker 1615.

This module is a supporting construction for the host task proving
`Langlands.Plancherel.ConditionalParabolicIntertwiningStatement`. It packages
every conjunct of the host conclusion that follows from published results and
from `ParabolicPointUniformNumerator`. Two analytic inputs are left as explicit
hypotheses: full convergence on a region and local integrable domination on
its twist-orbit saturation.

## The analytic-input predicate

`ParabolicLeviAnalyticInputs … π C` is the proposition that the region `C` of
unramified parameters of the full rational norm family satisfies all of:

- `C` is nonempty and open;
- the actual standard-integral domain is the whole source at every parameter
  of `C`;
- the published `CompactIntegralLocallyDominatedOn` holds on the published
  `unramifiedTwistOrbitSaturation` of `C`.

It is the single analytic hypothesis of the assembly theorem below. It is a
proposition, not an assertion.

## The theorem

`parabolicLevi_intertwiningConclusion_of_dominated` works in the host's actual
rational-point setting, with the same data as the section `Host` of
`ParabolicPointUniformNumerator`:

- presentations `r` and `r'` with the same Levi composite and split component;
- geometric radicals `n` and `n'`;
- point subgroups `Ppt`, `Upt`, `U'pt` with their defining equalities;
- the semidirect decompositions, `K`, the projections, the quotient measures,
  radical unimodularity `hδ`, `hδ'` and the squared-modulus compatibility `hsq`.

Let `π` be an admissible finite-length representation of the literal Levi
point subgroup. Let `C` be a set of unramified parameters of the full rational
norm family with `ParabolicLeviAnalyticInputs … π C`, and let `Ω` be its
published `unramifiedTwistOrbitSaturation`. Then the theorem gives exactly the remaining conjuncts of the host conclusion
for this region:

1. `C` is nonempty and open, and its published `unramifiedTwistOrbitRegion` is
   open;
2. there is a full-domain proof `hfull` at every parameter of `Ω`;
3. `StandardCompactRationalOn … Ω π hfull` holds;
4. for every `χ ∈ Ω`, every representation `W` of the literal Levi point
   subgroup in an independent carrier universe and every equivalence
   `e` from the twist of `π` by `χ` to `W`, there is a full-domain proof for `W`
   with the naturality square of the published `fullSourceIntertwiner`.

## Proof

- Full convergence on `Ω` is the published
  `domain_eq_top_on_unramifiedTwistOrbitSaturation`.
- Openness of the orbit region and of `Ω` are the published
  `isOpen_unramifiedTwistOrbitRegion` and
  `isOpen_unramifiedTwistOrbitSaturation`.
- Compact rationality on the open set `Ω` is
  `parabolicLevi_standardCompactRationalOn_of_dominated_of_finiteLength` of
  `ParabolicPointUniformNumerator`, applied with `hdom`.
- Representative naturality is the published
  `fullSourceIntertwiner_equivalent_representative`.

## Scope and provenance

The theorem does not prove convergence, domination, radical unimodularity or the
squared-modulus compatibility. It does not choose the host region
`parabolicPointUnramifiedIntertwiningRegion` or prove its nonemptiness or
openness, and it does not prove the host theorem. It is an internal composition
of the published declarations named above and of
`ParabolicPointUniformNumerator`; no literature theorem replaces a proof.

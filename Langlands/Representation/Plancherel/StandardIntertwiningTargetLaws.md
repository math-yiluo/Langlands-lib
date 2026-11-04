# Naturality and full-source normalization of the standard intertwiner

Author: Worker 200.

This derived construction packages naturality of the actual standard integral
as equalities in the target normalized induction. It also constructs the
intertwiner on the entire source when the existing convergence and
representability domain has been proved to be the whole source. For the
diagonal pair, both the full-domain and squared-modulus equalities are proved:
the resulting ambient intertwiner is the total-mass multiple of the identity,
and is the identity for a probability quotient measure.

## Source and conventions

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003),
235–333, registered as `waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
I.3, printed p.243 (PDF p.9), fixes the positive Levi half-modulus and the
uniform open right stabilizer in the induced-function model. IV.1, printed
p.277 (PDF p.43), gives the change-of-representative square. The end of that
page and printed p.278 (PDF p.44) define the integral through absolute
convergence against every smooth-contragredient functional and representation
by a vector in the original inducing carrier, and then define the full-source
homomorphism when these conditions hold for all inputs and ambient arguments.

The present result derives these formal laws from the existing actual integral.
The source discusses admissible representations in its reductive setting;
these elementary laws require only the displayed smooth-representation and
subgroup hypotheses. No admissibility or irreducibility claim is added.
The diagonal normalization is an internal consequence of the constant
integrand and the actual chosen measure, rather than a separately numbered
source theorem.

All declarations are in `Langlands.Plancherel.StandardIntertwining`. The
modules `StandardIntertwiningIntegral`, `StandardIntertwiningNaturality`,
`StandardIntertwiningMeasure`, `StandardIntertwiningTarget` and
`StandardIntertwiningModulus` supply the actual objects used below.
The quotient is the left-coset space `(U ∩ U') \ U'`, implemented as
`QuotientSpace (U := U) U'`; the intersection need not be normal.
The normalized inductions are the canonical
`DynamicNormalization.leviTwistedInductionFunctor` objects on `SmoothRep`,
with ambient action by right translation.

## Hypotheses

For the target-valued and full-source maps, `G` is a locally compact Hausdorff
nonarchimedean topological group. The actual subgroups have semidirect
decompositions `P = M U` and `P' = M U'`, with closed `U`, `U'` and `M`.
Borel measurable structures on `U'`, its nested intersection `U.subgroupOf U'`,
and the actual quotient are supplied. The fixed regular two-sided Haar
measures `μU'` and `μI` and quotient measure `ν` satisfy the existing
`QuotientIntegration.IsCompatible` relation.

`SquaredModulusCompatibility h hU h' hU'` is an explicit additional premise
for these maps. It is the actual squared identity of the source and target
radical Haar characters and the restricted intersection automorphism
character. Its proof and actual reductive comparison remain obligations,
as documented in the imported target and modulus modules.

The inducing representations `A` and `B` are smooth complex representations
of the common actual Levi. Their carrier universes `uV` and `uW` and the group
universe `uG` are independent. Levi intertwiners can cross those two carrier
universes. No topology or norm is placed on either carrier.

The helper `sourceToDomain` needs only the source decomposition and closed
source radical, locally compact nonarchimedean `G`, a measurable quotient,
and the displayed full-domain equality. It needs no target decomposition,
closed Levi, Haar measure or compatibility, squared identity, Hausdorff
assumption, or Borel quotient hypothesis.

## Actual target naturality

`targetOperator_map` states that postcomposition by any Levi intertwiner `T`
commutes with the actual target-valued integral. On the source, `domainMap`
restricts the induced map to the already proved integral domain; on the target,
`inducedMap` is the actual map of normalized induced functions. Two subtype
extensionality steps reduce the equality to the existing `operator_map`, so
the proof retains every value of the original selected integral.

`targetIntertwiner_natural` states the same square as equality of actual
ambient `Representation.IntertwiningMap`s. Extensionality reduces it to
`targetOperator_map`. `targetOperator_domainEquiv` specializes the equality to
the existing equivariant `domainEquiv` associated to an equivalence of inducing
representations. That equivalence is the published forward and backward
restriction of the induced maps; no equality of unrelated carrier types is
assumed.

## Full-source construction

For an explicitly proved equality

```text
domain h hU U' A ν = ⊤,
```

`sourceToDomain` sends each induced function to that same function with its
domain membership proof. Its linearity and ambient equivariance are
definitional after subtype extensionality. `sourceToDomain_val` records that
forgetting membership returns precisely the original function.

`fullSourceIntertwiner` composes this inclusion with `targetIntertwiner`.
It is therefore an actual ambient intertwiner from the entire source
normalized induction to the target normalized induction, using the original
chosen integral. `fullSourceIntertwiner_eval` is definitional equality of
its evaluation with `operator` on the included input.
`fullSourceIntertwiner_spec` is the original `operator_spec`: for every `g`,
each smooth-dual scalar integrand is absolutely integrable and its integral
is evaluation on the output vector in the original carrier.

`fullSourceIntertwiner_natural` proves equality of the two composite ambient
maps for any Levi intertwiner. It displays the full-domain equalities for
`A` and `B` separately. After map extensionality it applies
`targetOperator_map`; the two source-domain membership proofs agree by proof
irrelevance. In particular, changing the proof of full-domain equality does
not replace any source function or any integral.

## Diagonal case and proof

For `P' = P`, `M` and `U' = U`, the theorem
`squaredModulusCompatibility_diagonal` proves the required squared identity
from `squaredModulusCompatibility_iff`. The ambient intersection is `U`, and
both sides become the square of the same actual closed Haar character.
This proof needs the locally compact nonarchimedean ambient group, closed
source radical, source decomposition and a Borel structure on
`U.subgroupOf U`. It needs no Haar or quotient measure, representation,
closed Levi or Hausdorff hypothesis.

With the diagonal Borel structures, actual regular two-sided Haar measures
and their compatible quotient measure `ν₀`, `diagonalTargetIntertwiner`
instantiates `fullSourceIntertwiner` using that proved squared identity and
the existing `domain_diagonal`. The latter proves convergence and original
carrier representability for every input under `IsFiniteMeasure ν₀`, because
the diagonal quotient integrand is constant. The target-valued map retains
the Hausdorff and closed-Levi assumptions needed by the target construction.

`diagonalTargetIntertwiner_eq` identifies this actual ambient intertwiner with

```text
((ν₀ Set.univ).toReal : ℂ) • Representation.IntertwiningMap.id ...
```

Extensionality of intertwining maps, linear maps and the two induced-function
subtypes reduces the claim to the existing `operator_diagonal` for the
included source input. `diagonalTargetIntertwiner_probability` substitutes
the probability mass `1`. Thus no measure is rescaled to force the identity
normalization: it follows for the chosen measure when that measure is a
probability measure.

## Retained obligations

The full-domain equality for distinct parabolics is an analytic premise to
this construction, not a permitted structural input for completion of the
Plancherel program. It includes both absolute convergence and original-carrier
representability. No such equality is assumed implicitly or proved here
outside the diagonal case. IV.1.1's character convergence cone and rational
continuation remain open, as do the general squared-modulus proof and actual
reductive realization, composition scalars, and the remaining Plancherel
analysis. This pair supplies formal compatibility of the constructed maps
and the proved diagonal normalization, without a claim of prerequisite or
whole-program completion.

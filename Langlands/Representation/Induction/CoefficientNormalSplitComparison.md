# Native coefficient normal coinvariants and split quotient

Worker 1759 constructs the actual normal-coinvariant comparison for compact
induction over a commutative ring `R`, and proves it is an equivalence when
`R` is a complex algebra. This is an internal extension of the published
`NormalCoinvariantMap`, `NormalSplitComparison` and `SplitQuotientProof`
constructions. It is an intermediate comparison for the native coefficient
geometric-lemma route; it does not establish the rational universal-family
Jacquet finiteness statement.

## Objects and canonical maps

The ring, ambient group `G`, split quotient group `L`, and coefficient
carriers `V` and `W` have independent universes. A representation over `R`
means the original `R`-linear action, and coinvariants mean Mathlib's actual
quotient by the `R`-span of `rho(n)v - v`. No topology is required on `R`
or on a coefficient carrier.

The elementary transport constructions require only a commutative ring.
`normalCoinvariantsMap` descends the original inducing intertwiner and
retains its ambient group equivariance. `normalCoinvariantsEquiv` applies
that construction to an equivalence and its inverse.
`normalCoinvariantsCongr` transports along equality of normal subgroups,
with the identity formula on vector classes. `restrictAlongEquiv` restricts
the action along a group homomorphism without changing the linear map.
`compactInducedEquiv` postcomposes actual compact covariant functions with
the original equivalence; its inverse postcomposes with the inverse.
The inverse laws and evaluation formula follow pointwise.

For the normal comparison, `G` is a topological group, `N` is a normal
subgroup of `G`, `H` is a subgroup and `N ≤ H`. For a representation `sigma`
of `H`, define

`compactNormalCoinvariantsMap :
  ((compactInduced H sigma).toCoinvariants N).IntertwiningMap
    (compactInduced H (sigma.toCoinvariants (N.subgroupOf H)))`.

This is the actual pointwise coefficient quotient. On a compact function
`f`, its value on the class `[f]` at `g` is `[f(g)]` in the inducing
`N`-coinvariants. To descend the map, the proof rewrites
`g*n = (g*n*g⁻¹)*g`. Normality places the conjugate in `N`, containment
places it in `H`, and covariance followed by the defining coinvariant
relation removes its action. Equivariance follows from right translation
on functions. Naturality in every `R`-linear inducing intertwiner reduces
on representatives to the identity `[T(f(g))] = [T(f(g))]`.

## Complex restriction and proved bijectivity

For bijectivity, assume `Algebra ℂ R`, `Module ℂ V` and the compatible
scalar tower `IsScalarTower ℂ R V`. The inherited quotient scalar tower
comes from `CoefficientSplitKernelIntegral`; the actual scalar-restriction
comparisons come from `CoefficientCompactCoinvariants`.

`normalCoinvariantsComplexEquiv` identifies the normal coinvariants after
complex restriction with the complex restriction of the native normal
coinvariants, preserving the ambient operators. Both it and its inverse
send an original vector class to the same vector class. The proof uses the
published equality of native and complex relation spans, so it preserves
the original quotient rather than introducing a new coefficient action.

`compactNormalSourceComplexEquiv` combines that quotient comparison with
the identity-on-functions compact-induction comparison.
`compactNormalTargetComplexEquiv` uses the same comparison pointwise on
the inducing quotient. `compactNormalCoinvariantsMap_complex` proves that
the resulting square with the published complex pointwise quotient map
commutes. Quotient surjectivity and evaluation reduce the square to the
identity on original vector classes.

Now assume `G` is Hausdorff and has the explicitly supplied compact-open
subgroup neighborhood basis. Assume `H` and `N` are closed and `sigma`
is smooth. Smoothness is unchanged by complex scalar restriction. The
published complex `compactNormalCanonicalEquiv` is therefore available.
The commuting square expresses the native map as the composition of that
proved bijection and the two actual scalar-comparison equivalences.
`compactNormalCoinvariantsMap_bijective` proves bijectivity of the native
map as a function; its `R`-linearity was already established by its direct
construction. `compactNormalCanonicalEquiv` bundles this very map using
`IntertwiningMap.ofBijective`, retaining its definitional representative
formula. No equivalence or bijectivity premise is supplied by the caller.

## Actual split quotient

Let `r : G →* L` and `s : L →* G` be continuous group homomorphisms with
`r(s(l)) = l`. The group `L` is a topological group. Assume the same
Hausdorff and compact-open basis conditions on `G`, closedness of `H`
and `r.ker`, containment `r.ker ≤ H`, and smoothness of `sigma`.
Then `normalSplitCompactEquiv` is an `R`-linear representation equivalence
from

`((compactInduced H sigma).toCoinvariants r.ker).comp s`

to

`compactInduced (H.comap s)
  ((sigma.toCoinvariants (r.ker.subgroupOf H)).comp (s.subgroupComap H))`.

Restrict the native canonical normal equivalence along `s`, then compose
with the published arbitrary-coefficient `splitQuotientEquiv`. Its
kernel-triviality premise is proved directly: on an original vector class,
every inducing element in `r.ker` acts trivially by
`Coinvariants.mk_self_apply`. The resulting comparison sends `[f]` at
`l` to `[f(s(l))]`, exactly as stated by
`normalSplitCompactEquiv_eval_mk`.

`normalSplitCompactEquiv_natural` quantifies over an independent target
carrier `W`, its compatible complex scalar tower, every smooth native
representation on it, and every inducing `R`-linear intertwiner. Quotient
induction and function extensionality reduce the formula to the same
original class `[T(f(s(l)))]`.

## Provenance and remaining obligations

The new maps and equivariances are proved internally from the original
representation laws and actual quotient definitions. The only
representation-theoretic bijectivity input is the already published
complex normal-coinvariant theorem; the scalar comparisons prove that it
applies to the very native map constructed here. The final split step
reuses the published arbitrary-coefficient split quotient equivalence.
This is not presented as a new verbatim assertion from external literature.

This unit has no Haar integral or correction character. It supplies the
outer normal/split comparison needed for compact induction in stages.
Assembling that comparison with the native inner relative integral,
proving normalized cancellation, constructing actual rational orbit data
and finite orbit filtrations, and proving native compact-open fixed-module
finiteness remain separate obligations. In particular no new finiteness
hypothesis or supplied comparison replaces the unchanged
`RationalSupercuspidalJacquetFamilyFiniteStatement`.

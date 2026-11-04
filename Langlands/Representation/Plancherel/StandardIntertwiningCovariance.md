# The actual Levi transformation factor of the standard integral

This derived construction extends `StandardIntertwiningIntegral` by computing
its Levi transformation factor on its actual domain. It uses the existing
compatible-quotient change of variables, without imposing normality on the
intersection of the two subgroups.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082: I.3, printed p.243 (PDF p.9), for positive
Levi-normalized induction, and IV.1, printed pp.277–278 (PDF pp.43–44), for
the integral tested against smooth contragredient functionals. The explicit
factor proved here is an internal deduction from that function law and the
published quotient-automorphism integration theorem. This unit does not prove
Waldspurger's convergence cone or rational continuation theorem IV.1.1.

## Setting and scope

The ambient group `G` is locally compact and nonarchimedean. Its universe and
the universe of the canonical complex smooth representation `A` of `M` are
independent. The actual subgroups satisfy `IsSemidirectDecomposition P M U`,
and `U` is closed. A second subgroup `U'` is normalized by `M`; neither a target
parabolic nor a target semidirect decomposition is an input. In particular,
the construction does not assume that these arbitrary subgroup data arise
from rational points of reductive parabolics.

Write `I = U.subgroupOf U'`. The integration space is the actual left quotient
`I \ U'`, whose elements are the left cosets `I u'`. The subgroup `I` need not
be normal in `U'`. For the modulus and integration statements, `U'` is locally
compact, and Borel measurable structures on `U'` and `I` are supplied. Closedness
of `U` makes `I` closed in `U'` and supplies its local compactness.

The change-of-variables statements additionally require Hausdorff `G`, a Borel
structure on `I \ U'`, fixed regular two-sided Haar measures `muU'` and `muI`,
and a compatible quotient measure `nu` in the sense of
`QuotientIntegration.IsCompatible I muU' muI nu`. The pushforward and scalar
integrability lemmas only need right invariance of `muI`; the complex integral
lemma uses the existing theorem with both two-sided Haar inputs. No closedness
of `U'` is required because its local compactness is supplied directly.

The weak-integral law holds whenever the actual integrand at `g` has a
representing vector. The selected-operator law additionally requires closed
`M` and a vector in `StandardIntertwining.domain`, which imposes scalar
integrability and representability at every point. No full-domain convergence
is inferred.

## Actual maps and moduli

For `m : M`, let `alpha` be conjugation by `m` on `U'`, namely
`u' -> m u' m^-1`. Normalization of `U'` defines this continuous group
automorphism. The semidirect decomposition supplies normalization of `U`, so
`intersection_conj_invariant` proves that `alpha` preserves `I`.

`quotientConjugation` specializes the existing quotient automorphism to the
homeomorphism

```text
alphaQ : I \ U' -> I \ U',    [u'] -> [m u' m^-1].
```

Its inverse on representatives is exposed by
`quotientConjugation_symm_mk`. This construction uses an actual quotient
homeomorphism, without a quotient group structure.

Let `deltaU'` be `mulEquivHaarChar alpha`, and let `deltaI` be
`mulEquivHaarChar` of its actual restriction to `I`. The convention for
`mulEquivHaarChar` is that `delta * map alpha mu = mu` for a regular Haar
measure `mu`. The positive real factor

```text
c(m) = deltaU'(m) / deltaI(m)
```

is defined by `quotientConjugationModulus`; its positivity is proved in
`quotientConjugationModulus_pos`. Both terms come from the actual
automorphisms, with no assumed determinant or root formula.

`quotientConjugation_map` specializes
`IsCompatible.map_quotientAutomorphism` to give
`map alphaQ nu = c(m)^-1 * nu`, where multiplication denotes measure scaling.
`integrable_quotientConjugation_symm` proves that `F` is integrable exactly
when `F` composed with `alphaQ^-1` is integrable. Its proof applies
`integrable_map_equiv` to that composition and then removes the finite,
strictly positive scaling factor from the mapped measure.

`integral_quotientConjugation_symm` specializes
`compatibleQuotientAutomorphismScaling` to the genuine complex Bochner
integral identity

```text
integral F(alphaQ^-1(q)) dnu(q) = c(m) * integral F(q) dnu(q).
```

The scalar integral is the total Mathlib integral, so this equality is stated
for every complex function. The separate integrability equivalence supplies
the convergence information used below.

## Weak integrals and the selected operator

Let `a(m)` be the positive source half-character
`HaarModulus.closedHalfCharacter U hU M h.levi_le_normalizer m`, viewed as a
complex scalar. The source function covariance proves
`integrand_levi_mul`:

```text
F_(m*g)(q) = a(m) * A(m)(F_g(alphaQ^-1(q))).
```

The proof is on actual quotient representatives and uses the source inducing
function law and the group identity `u' m = m (m^-1 u' m)`.

`weakIntegral_levi_mul` carries both scalar convergence and a representing
vector through this equation. Given a smooth functional `ell`, its pullback
along `A(m)` is the smooth functional obtained by the contragredient action
of `m^-1`. The scalar convergence equivalence applies to this functional;
constant multiplication preserves integrability. The complex integral scaling
and the original scalar test then show that a representing vector `v` at `g`
gives representing vector `a(m) * c(m) * A(m)v` at `m*g`.

Finally, `operator_levi_mul` compares this representing vector with the
selected integral using the existing smooth-dual uniqueness theorem:

```text
(J f)(m*g) = (a(m) * c(m)) * A(m)((J f)(g)).
```

Closedness of `M` supplies the compact-open cofinality required for uniqueness;
no admissibility, topology, or completeness of the representation carrier is
needed.

This is the explicit Levi factor for arbitrary subgroup data. Identifying it
with the positive target half-modulus for parabolics sharing `M` requires the
separate reductive comparison
`deltaU(m) * deltaU'(m) = deltaI(m)^2`, using the corresponding actual Haar
moduli. That comparison is neither assumed nor proved here. Target normalized
induction membership, a target-valued intertwiner, rational-point realization,
full-domain convergence and rational continuation remain separate obligations.

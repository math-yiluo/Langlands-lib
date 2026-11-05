# Actual base-object comparisons of the full smooth orbit representation

Author: Worker 200.

This derived unit extends the existing actual-object reindexing to the full
canonical smooth representation, the actual descended coefficient and the
original full invariant form. It also constructs a linear isometry for the
original entire orbit-integral cores and proves its full equivariance. These
are internal consequences of the actual objects, rather than separately
stated theorems attributed to Waldspurger.

The source context is *La formule de Plancherel pour les groupes p-adiques*
(2003): VI.1, printed pp.295–296/PDF pp.61–62, for coherent actual orbit
sections and their compact finite smooth-family model; V.1, printed
p.288/PDF p.54, for the actual coefficient map; V.2, printed p.293/PDF p.59,
for the inverse-degree fiber form; and the proof of Proposition VI.4.1,
printed p.306/PDF p.72, for the full product action. Registered source
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

## Actual base-object reindexing and the full action

Fix a canonical irreducible admissible complex inducing object `π` of the
actual Levi subgroup and an actual object `A` in its unitary unramified
orbit. The published `unitaryOrbitRepresentativeBaseEquiv` retains each
actual inducing object, changing its orbit-membership witness. The published
`productInducedSmoothOrbitBaseEquiv` reindexes the entire coherent section
by this equivalence. Its proof of smoothness already handles the resulting
torus translation and fixed compact coefficient equivalence. No triviality
of a stabilizer's action on the compact fiber is assumed.

The full representation comparison retains the generic locally compact
nonarchimedean group, actual semidirect `P = M U`, closed `P` and `U`, fixed
compact open `K` and actual `G = P K` factorization, continuous positive norm
characters and Levi projection. The supplied finite torus coordinates satisfy
`HasLaurentUnitaryCoordinates`; the same coordinates and Laurent premise
apply at both actual base objects. Group, character-index, inducing-carrier
and finite parameter-index universes are independent. No topology, norm or
finite dimension is imposed on the inducing carrier.

`productInducedSmoothOrbitBaseEquiv_action` holds because the reindexed
section has the same value at the same actual inducing object and the full
action is the original fiber action on that value. Subtype extensionality
proves equality of the resulting smooth sections. The definition
`productInducedSmoothOrbitBaseRepresentationEquiv` bundles the existing
linear equivalence with this full intertwining law. The entry
`productInducedSmoothOrbitBaseIso` applies the canonical `SmoothRep.mkIso`;
its hom-application theorem identifies its underlying map with the original
actual section reindexing.

## The actual coefficient across the same orbit classes

`unitaryOrbitCoefficientMap_baseChange` retains the actual coefficient
construction's additional second countability, Hausdorff and Borel
assumptions, local compactness of `P`, ambient unimodularity and the full
parabolic modulus identity. The central quotient, its Haar measure and the
square-integrability witness for `π` are fixed. The new base object's
square-integrability is supplied by the published orbit-representative
theorem. There is no additional square-integrability premise.

The two orbit spaces are identified by the published
`unitaryOrbitDiscreteSeriesBaseHomeomorph`, which preserves the actual
discrete-series class. At each point of the new orbit, the theorem equates
its coefficient after section reindexing with the original coefficient after
this homeomorphism, as entire locally constant functions of `g`. The proof
chooses an actual representative using the published surjectivity theorem,
rewrites both sides by actual representative independence, and uses the
published compatibility of the two orbit maps with actual reindexing. The
remaining actual fiber coefficient and section value are identical. This
comparison needs no Laurent premise, coordinate continuity, finite
stabilizer, inducing positive form or orbit measure. Both coefficients use
the same original compact Haar probability.

## The entire original form and induced norms

The form and norm comparisons retain all hypotheses of
`ProductInducedOrbitFormBaseChange`: the group/parabolic hypotheses and
normalizations above, compact-open cofinality in the Levi, Borel structures,
inversion invariance of the same quotient Haar measure,
square-integrability, the finite central norm quotient, continuous forward
torus coordinates and the same finite open-positive character measure `η`.
The measure `η` is multiplicatively invariant. This is exactly the premise
used by the published base-orbit measure comparison to cancel the change of
the base parameter; the measure is not replaced or rescaled.

`productInducedSmoothOrbitBaseForm_inner` adds the Laurent premise for the
full actions. Both full invariant forms retain their original entire cores
definitionally, so the existing whole-core base comparison gives equality on
every pair of sections. It preserves the actual orbit measure, its inverse
stabilizer-cardinality factor and the canonical inverse-degree fiber forms.

`productInducedSmoothOrbitBaseIsometry` requires no Laurent premise, since
constructing the norms and comparing their entire cores already precedes
the full action. It uses exactly the two norms constructed from those cores
and the original `productInducedSmoothOrbitBaseEquiv`. Its norm-preservation
proof applies the published full inner-product comparison to `(q,q)` and
takes the square root of the real part. The application theorem confirms
the original reindexing of actual fiber values. Adding the Laurent premise,
`productInducedSmoothOrbitBaseIsometry_action` is the earlier full-action
comparison for that same underlying map.

This unit treats changes of the actual base object within the same actual
unitary orbit. It introduces no induced irreducibility, arbitrary coefficient
norm, Hilbert completion, density weight, intertwining continuation,
constant-term regularity, wave packet estimate or Fourier inversion. Rational
parabolic realization and all standing whole-task acceptance conditions
remain separate obligations.

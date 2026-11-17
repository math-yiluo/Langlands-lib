# Actual comparison with the standard spectral family

This derived module compares the full family of
`RationalSemistandardSpectralFamily` with the existing family in
`RationalStandardSpectralFamily`. It constructs the orbit and coefficient maps
from the actual subgroup identifications and published representative changes.
Its maps are conditional on the explicit discrete-series and smoothness
comparison propositions described below. Neither proposition is proved here.

The field `F : Type u` is a nonarchimedean local field with finite residue field;
positive characteristic is allowed. The ambient group scheme `G` is affine and
locally of finite type. The comparison takes `hG : IsConnectedReductive G`,
`hi : IsMaximalSplitTorus i` for `i : S.toGrp ⟶ G`, and a generic cocharacter
`nu` with proof `hnu`. Ambient splitness is not required. Representation carriers
have the independent universe `uV`.

For every intrinsic semistandard index `p`, the full family has a split component
`a p` of `chosenLeviModel p`, with proof `ha p`, normal split-center image,
measurable quotient of the literal Levi by that image, and a Haar measure `mu p`.
The old standard family independently has `b I`, `hb I`, normality, a measurable
quotient and a Haar measure `eta I`, for each finite subset `I` of the simple
relative roots. Its representing scheme is `standardLeviModel hG hi hnu I`.
Both models represent the same actual all-test Levi at
`standardIndex hG hi hnu I`; their point identifications pass through the
identical subgroup `levi (standardIndex hG hi hnu I)` of `G(F)`.

`RationalSemistandardStandardDiscreteSeriesComparison` is the Prop-valued
target asserting, for every `I` and every identical actual `SmoothDualClass`
of this literal Levi, equivalence of `IsDiscreteSeriesClass` for the full and
old standard split-center and quotient-measure data. This compares membership
in discrete series on the actual class, not just abstract isomorphic quotient
sets. No discrete-series equivalence, coefficient equivalence or conclusion of
spectral finiteness is an input to this target. Its proof is a remaining
substantive obligation.

Given a proof `hds` of that target,
`rationalStandardFullDiscreteSeriesEquiv` changes only the discrete-series
membership proof and retains the underlying actual smooth-dual class.
`rationalStandardFullOrbitEquiv` descends it to unitary unramified twist orbits.
The character change is the companion module's `unitaryCharactersEquiv`,
obtained from the actual model identifications and fixing each character's value
on every literal Levi element. The relation proof applies equality of the
underlying classes to the actual twist equality in each direction.
`rationalStandardFullOrbitEquiv_mk` gives the quotient-constructor formula.

`rationalStandardFullIndex` sends an old standard pair `(I,O)` to the full pair
consisting of its actual standard triple and this mapped orbit.
`rationalStandardRepresentative_full_isSquareIntegrable` applies `hds` to
the old chosen representative's actual class.
`mk_discreteSeriesClass_rationalStandardRepresentative_full` proves that the
same actual representation lies in the mapped full orbit, by applying the orbit
equivalence to the old representative's published orbit-membership equality.

`rationalStandardFullComponentEquiv` first applies the published
`orbitSectionsBaseEquiv` to change the full orbit's chosen base representative
to that old actual representative. It then applies `orbitSectionsModelEquiv`
from the chosen model to the standard model through their literal common Levi.
The codomain is the existing actual normalized product-induced section space.
These are prescribed maps on actual inducing objects and coefficient values;
no freely supplied linear equivalence replaces them.

`rationalStandardFullRestrict` evaluates a full family at the mapped index and
applies this component equivalence. The map is complex-linear by pointwise
linearity. `rationalStandardFullRestrict_canonical` identifies it with canonical
standard-slice restriction followed by the specified orbit and component changes.
`rationalStandardFullRestrict_support` proves that its literal nonzero support
is exactly the preimage of the full support: each component equivalence is
injective and maps zero to zero.

`rationalStandardFullIndex_finite_fibers` proves that each index fiber is finite.
The fiber maps injectively into the finite type of root subsets `I`: for fixed
`I`, equality of the full image pairs implies equality of the old orbits by
injectivity of `rationalStandardFullOrbitEquiv`. Finiteness of root subsets uses
the published `finite_simpleRoot hG hi hnu`. This proof assumes neither
injectivity of all standard presentations nor finiteness of the whole
semistandard parabolic index.

For the smooth comparison, the full family additionally supplies
`d p : CompactData p` for each `p`. The old standard family uses a compact open
subgroup `K` of `G(F)`, its compactness proof `hK`, and `hPK`, the Iwasawa-pair
condition for the minimal standard parabolic. These give the published
`standardCompactData` and its definitional comparison
`smoothOrbitSections_standard` with `rationalInducedSmoothOrbitSections`.

The further hypothesis `hsm : ModelSmoothComparisonStatement` is the companion
module's explicit unproved target. For every actual triple, two representing
Levi models, two compact pictures, an actual irreducible admissible
representation and a raw orbit section, it asserts equivalence of smooth
membership under the specific `orbitSectionsModelEquiv`. Thus it includes the
prescribed parameter-coordinate and compact-picture choices. It is not an
arbitrary family of comparison maps.

`rationalStandardFullComponentEquiv_smooth` uses the published smooth base-change
equivalence and then `hsm` to prove smoothness of the constructed component map.
`rationalStandardFullSmoothRestrict` consequently lands in the existing
`rationalStandardThetaSmoothSections`. Its finite-support proof combines the
exact raw support equality with the finite-fiber theorem. Its value and
canonical-restriction compatibility formulas are definitional; its support
formula specializes the raw support theorem.

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), registered as
`waldspurger-2003-plancherel`, SHA256
`4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The source-to-construction map is:

| Source location | Role in this module |
| --- | --- |
| I.1, printed pp.238–239 (PDF pp.4–5) | Actual semistandard and standard Levi subgroups and split components used in the discrete-series comparison target. |
| VI.1, printed pp.295–296 (PDF pp.61–62) | Actual induced coefficient sections, representative equivalences and covariance inherited by the component maps. |
| VI.3, printed p.305 (PDF p.71) | Full `Theta`, smooth direct-sum families and their restriction to the existing standard family. |

The comparison target, implementation maps, finite-fiber argument and support
laws are derived interfaces for these source objects. Finite support remains a
defining property of an input family. This module makes no assertion about the
Fourier support of every Schwartz function, Weyl invariance, synthesis or
Plancherel.

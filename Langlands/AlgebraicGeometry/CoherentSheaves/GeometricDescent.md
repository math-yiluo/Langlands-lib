# Geometric descent of actual flat finitely presented families

Author: Worker 311. This is an internal consequence of the actual ordinary
module descent, finite-presentation descent and relative-flatness results.
It works in every universe `u` and uses the published `IsFamily`, `Family`
and `FamilyGroupoid` without changing their definitions.

In a Cartesian square with `p : X → Y`, `q : X → T`, `f : Y → B` and
`g : T → B`, assume `g` is flat, locally of finite presentation and
surjective. Then an ordinary module `M` on `Y` is an actual family over
`f` if and only if its ordinary pullback along `p` is an actual family
over `q`. No quasi-coherence of `M` is assumed. The forward direction
uses preservation of finite presentation and Cartesian relative flatness.
For the reverse direction, the three covering properties pass to `p`;
finite presentation descends by `isFinitePresentation_of_pullback_fppf`,
and relative flatness is detected by the published Cartesian detector.

The namespace `GeometricDescent` uses the all-scheme-test `Datum p F` and
`Str D t M` of `LineBundleFlatDescentStr`. These structures place no
rank-one restriction on their modules. An effective structure on `Y`
gives the actual isomorphism `p*M ≅ F` via
`GeometricQuasicoherentDescent.pullbackIsoOfStr`. If `p` is flat, locally
of finite presentation and surjective, and `F` is locally finitely
presented, this isomorphism makes `p*M` locally finitely presented and
finite-presentation descent proves the same for `M`.

With the Cartesian square above and `F` an actual family over `q`,
`isFamily_of_str` combines this finite-presentation result with
`isFlatOver_of_str_of_isPullback`. The construction `familyOfStr` bundles
that very module `M` and those proved properties as an object of the
actual category `Family f`; it introduces no surrogate family condition.

If `g` is also affine, `exists_family` first obtains an effective ordinary
module and its all-test `Str` from geometric quasi-coherent effectivity.
Finite presentation of `F` supplies the required quasi-coherence. The
preceding construction makes the effective module an actual family.
`existsUnique_family_iso` lifts the unique compatible actual module
isomorphism to the full family category. Compatibility means the stated
`Str.Hom` equation on every scheme test; uniqueness is for compatible
isomorphisms, with both effective structures fixed.

The `FamilyGroupoid` consequences specialize detection and effectivity
to the published actual relative-space square for any morphism `h` in
the full slice `Over S`. The cover object is an actual object of the
published family groupoid, and the result is an actual object of that
groupoid carrying the same all-test effective structure. `effectiveComparison` turns the actual pullback isomorphism into an arrow
from the ordinary groupoid pullback to the cover object, with no covering
hypotheses needed once the effective structure is given.
`existsUnique_effective_iso` expresses the uniqueness result as uniqueness
of a compatible actual groupoid arrow. No assumptions
are made on the test schemes beyond the stated properties of the cover
map. In particular no noetherian, reduced, nonempty or quasi-compact
test-scheme restriction occurs.

This unit proves effectivity for the specified geometric cocycles along
single affine fppf covers. It does not construct the conversion from
arbitrary pseudofunctor descent objects or arbitrary covering families to
these cocycles, and does not assert a stack condition or a scheme atlas.
The provenance is internal; no new literature assertion is used.

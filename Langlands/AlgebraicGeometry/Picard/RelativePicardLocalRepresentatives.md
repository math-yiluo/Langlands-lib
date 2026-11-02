# Local representatives of the actual fppf Picard sheaf

Author: Worker 509.

This derived construction applies to every morphism `f : X ⟶ S` of schemes in
universe `u`. It uses the published ordinary line-bundle class presheaf
`RelativePicard.classPresheaf f` and its actual set-valued fppf sheafification
`RelativePicard.classSheaf f`. A line bundle over a test object `T : Over S`
lives on the published fibre product `(RelativePicard.relativeSpace f).obj T`.
No properness, field, finiteness or reduction hypotheses are imposed here.

## Representative sieves

`representativeSieve f T s` is Mathlib's image sieve of the exact sheafification
unit `toClassSheaf f` at a section `s` over `T`. An arrow `g : U ⟶ T` belongs
precisely when the restriction of `s` is the image of an ordinary line-bundle
class. The lemma `representativeSieve_iff` replaces that class with an actual
line bundle `L` and the equality

```text
sheafClassOf f U L = (classSheafPresheaf f).map g.op s.
```

The replacement uses `exists_representative` from the published ordinary
Picard presheaf. It does not assume that `s` has a representative over `T`.

The two instances `toClassSheaf_isLocallyInjective` and
`toClassSheaf_isLocallySurjective` expose Mathlib's local bijectivity of
sheafification for this named unit. Local surjectivity gives
`representativeSieve_mem`: the representative sieve is fppf-covering.
`representativeSieve_pullback` is the equality of this sieve's pullback with the
representative sieve of the restricted section. It is a direct specialization
of `Presheaf.pullback_imageSieve`.

`localRepresentative` chooses an actual bundle on each arrow belonging to the
sieve, and `localRepresentative_spec` records its class. These choices have no
asserted coherence or global gluing property. The lemma
`commonRepresentativeSieve_mem` intersects the two covering sieves for any two
sections, giving a single covering sieve on which both have representatives.
All constructions quantify over arbitrary tests, including nonreduced and
non-quasi-compact schemes.

## Equality and comparison

`isomorphismSieve f T L M` is the equalizer sieve of the ordinary classes of
two actual line bundles on the fibre product over `T`. By `map_classOf` and
`classOf_eq_iff_iso`, its membership condition is the existence of an
isomorphism between the two actual pulled-back line bundles.

`sheafSection_ext` specializes the separation axiom of the actual sheaf: two
arbitrary sections are equal if their restrictions agree on a covering sieve.
Using local injectivity of the unit in one direction and this separation axiom
in the other, `sheafClassOf_eq_iff_isomorphismSieve_mem` proves that the sheaf
classes of `L` and `M` agree exactly when their isomorphism sieve is
fppf-covering. It asserts local isomorphism, without asserting a global bundle
isomorphism from equality in the sheaf.

Finally, `isIso_classLift_of_locallyBijective` applies to any set-valued fppf
sheaf `G` and any natural transformation `η : classPresheaf f ⟶ G.obj`.
If `η` is locally injective and locally surjective, the canonical extension
`classLift f G η` is an isomorphism of presheaves. The implemented proof uses
`toClassSheaf_classLift` to factor `η` through the unit. Cancellation lemmas
for local injectivity and surjectivity give local bijectivity of the extension.
Regarding the extension as a sheaf morphism, Mathlib's
`Sheaf.isLocallyBijective_iff_isIso` gives an isomorphism, which is then
forgotten to presheaves.

## Provenance and scope

This is an internal derived API, specialized from Mathlib's image and equalizer
sieves, local bijectivity of sheafification, and the independently published
`RelativePicardPresheaf` and `RelativePicardSheaf` modules. It is not a separate
translation of a literature theorem. The named sieves and local choices record
exactly how the actual published sheafification admits local bundle
representatives. The module constructs no algebraic-space atlas and proves no
algebraicity or representability theorem. In particular the comparison lemma's
local bijectivity assumptions must still be proved for any proposed comparison
functor.

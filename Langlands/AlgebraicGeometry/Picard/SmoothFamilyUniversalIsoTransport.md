# Universal smooth families and isomorphic abelian schemes

`Langlands.AbelianScheme.smoothFamilyUniversalIsoTransport.{u}` proves
`SmoothFamilyUniversalIsoTransportStatement.{u}`.

This internal derived helper transports a supplied universal smooth-family
rigidified family along an actual isomorphism of abelian schemes. For
`e : A ≅ A'` over any scheme `S` and an actual family `L` for `A'` over
`P : Over S`, `isUniversalSmoothFamilyOnQuasiSeparatedTests_homIso` proves
that `(homFamilyPullback e.hom P).obj L` is universal for `A` when `L` is
universal for `A'`. The final existential theorem
`isUniversalSmoothFamilyOnQuasiSeparatedTests_transport` supplies that
specific pulled-back family on the same parameter `P`.

The construction uses the existing `homFamilyPullback`, which pulls the
actual bundle on `P ×_S A'` back along `P ×_S A → P ×_S A'` and transports
its rigidification using preservation of the unit section. The helper
`smoothFamilyGroupIso` forgets an abelian-scheme isomorphism to the
isomorphism of its underlying group schemes. Applied after base change to
`T`, this gives the isomorphism needed by the published smooth-family
invariance lemma from `SmoothFamilyUniversalBaseChangeProof`.
`homFamilyLineBundleIso` from `HomPicardZeroPullbackProof` compares this
pullback with the parameter-order convention in `familyLineBundle`.
These two existing comparisons prove the family-level smooth-family
condition in both directions. Quotient induction proves the corresponding
class-level equivalence.

`homClassesPullbackIsoEquiv` is the bijection on actual rigidified
isomorphism classes whose forward and inverse maps are pullback along
`e.hom` and `e.inv`. Its inverse laws use the published identity and
composition comparisons for rigidified pullback, with the proved
`RigidifiedModule.pullbackCoherence` supplied explicitly.

For a quasi-separated test `T` and a smooth-family class `q` for `A`, the
proof pulls `q` back along `e.inv` to get a smooth-family class for `A'`.
Universality of `L` supplies its unique classifying map `g : T ⟶ P`.
The existing `homClassesPullback_naturality` identifies classification by
the new family with classification by `L` followed by the class bijection.
The inverse law proves existence for `g`; injectivity of the bijection
transfers uniqueness. Both conjuncts of the unchanged universal predicate
are proved.

This is categorical transport derived from the imported Library results.
It makes no new comparison with ordinary Picard classes, divisor algebraic
equivalence or translation invariance. It constructs no representer from
scratch. Bases and parameter schemes are unrestricted, all data remain in
universe `u`, and every quasi-separated test is retained, including
nonreduced tests. There is no quasi-separatedness hypothesis on `S` or `P`.

# Reflection of open immersions by analytification

For a monomorphism of algebraic spaces, the range of its presheaf map is
isomorphic to the source and is an fppf sheaf. If a presheaf maps locally
surjectively onto the source, the sheafified range of the composite equals
that range. Every section in the range lifts locally through the
presentation. The reverse inclusion follows since the range is a sheaf.
`sheafifiedImageIsoOfMono` records the resulting isomorphism and its
factorization of the original monomorphism.

For an étale monomorphism of algebraic spaces, the composite of a
surjective étale atlas with the monomorphism is a representable étale
map. Its sheafified image is a representable open subfunctor by the
Library's étale image theorem. The image isomorphism therefore gives a
representable open immersion.

The analytification result uses a complete, nontrivially normed
ultrametric field `K` and separated algebraic spaces `X'` and `X`
locally of finite type over `Spec K`. It takes supplied analytifications
with point families `p'` and `p`, together with an analytic map `F`
compatible with the algebraic map `f` on every presented affine test
point. In Lean this compatibility is
`p' A P x ≫ F = p A P (RingPoints.map f x)`. Two further hypotheses
supply pullbacks along localized étale maps with étale base-change
projection and reflect the étaleness of a localized affine
analytification to its algebra map.

On the analytic side, an open immersion is monic and étale because it is
isomorphic to the canonical inclusion of an open domain. Under affine
étale reflection, monicity reflects by comparing the closed affine
overlaps supplied by separatedness of both spaces. The analytic
composite of an étale affine source test with the open immersion is
étale. Compatibility identifies that composite with the analytic map
of the composed algebraic point. The pointwise reflection theorem uses
the target's separatedness and local finite type hypotheses along with
the two analytic inputs to show that this algebraic point is étale.
Local finite type of the source gives the criterion that these
finite-type affine tests detect étaleness of the algebraic map. The
étale monomorphism result then gives the algebraic open immersion.

This is an internal consequence of the Library's open-domain and
sheafified image interfaces.

# Direct restricted levels and image-fixed raw classes

This internal comparison uses the original universe-zero Harris arithmetic
data, an actual abelian family with its supplied dual witness and polarization
map, and an integral endomorphism action on the pullback to `T`. For a map
`f : T′ ⟶ T`, the direct family has action literally
`(relativeEndRestrict B f).comp a`. The successive family is the pullback along
`f.left` of the family over `T`. All tensor, duality, Weil-transition,
rational-adelic and torsion inputs of
`HarrisIntegralCMLevelOrbitCoverLevels` are retained. The equivalence retains
quasi-separatedness of both test schemes, finite geometric fibres, invertible
torsion orders and finite-etale roots of unity on both bases. It requires no
connectedness, algebraically closed point field, nonempty level tower or
surjectivity of a fundamental-group map.

At a level `V` and point `t` of `T′`,
`harrisIntegralCMRestrictionImageFixedClass` evaluates any direct fixed level
as an old raw orbit class at `t ≫ f.left`, equipped with its invariance under
the image of the actual `fundamentalGroupMap`. The evaluation first uses the
existing direct/successive restriction comparison and then the pointed
Weil-frame orbit base-change equivalence. `RightOrbit.map_smul`, the actual
Weil-frame monodromy comparison and the fixedness of the successive level prove
image invariance. The `_val` theorem identifies its underlying class with the
previous `harrisIntegralCMRestrictionRawClass`.

`harrisIntegralCMImageFixedLevel_evaluate` proves that applying the previous
image-fixed pullback construction to this evaluation returns the original
direct level. On underlying successive classes this is the inverse law of
the orbit base-change equivalence. Subtype extensionality and the inverse law
of the direct/successive comparison give equality of the direct fixed levels.

`harrisIntegralCMRestrictionImageFixedEquiv` packages evaluation and the
previous image-fixed pullback as an equivalence between the actual direct fixed
level set at `V` and the subtype of old raw orbit classes fixed by the image of
the new fundamental group. The other inverse law is the previous exact recovery
theorem for image-fixed pullback. Thus the target is the full image-invariant
subtype at this level, not just one specified monodromy orbit.

`harrisIntegralCMRestrictionImageFixedEquivAt` retains an arbitrary old
geometric point `s` and a propositional equation `t ≫ f.left = s` by
substitution. Its `_apply_val` theorem identifies the forward value with the
previous actual restriction evaluation at `s`; its `_symm_apply` theorem
identifies the inverse with the previous `harrisIntegralCMImageFixedLevelAt`.
Both equations follow definitionally after eliminating the point equality.
`harrisIntegralCMRestrictionRawClass_injective` also proves that this old raw
evaluation determines the direct level uniquely. It applies injectivity of the
orbit equivalence, subtype extensionality and the inverse restriction
comparison. This last proof does not need the old base's finite-etale
roots-of-unity or invertible-order hypotheses; the new base's required inputs
remain in the direct fixed level.

The provenance is the existing actual pointed Weil-frame base-change
comparison, its monodromy equation and the direct/successive restriction
isomorphism. This unit proves a pointwise equivalence with image invariants. It
does not identify them with equivariant functions on a cover fibre, prove
naturality of such a comparison, extend the orbit-cover representation to the
full test category or construct the normalized CM moduli scheme. Output
admissibility, smoothness, projectivity and
`DivisionCMRepresentabilityStatement` remain open.

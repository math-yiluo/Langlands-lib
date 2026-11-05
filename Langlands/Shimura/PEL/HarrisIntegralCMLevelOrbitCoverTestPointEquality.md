# Equality of test points in original Harris orbit-cover levels

This is an internal deduction from canonical equality transport on the
existing fixed Weil-level sets and the actual Harris finite orbit-cover
correspondence. It restricts that transport to selected base-orbit subtypes
and extends the original test-precomposition comparison to a supplied point
with a propositional compatibility equation. No external source assertion
is introduced.

All arithmetic carriers, schemes and the point field have universe zero.
The inputs retain the Harris CM fields, central simple unitary datum,
normalized signature charts and scalar structures of the imported modules.
An actual abelian scheme `B/S`, dual witness `W`, dual-valued homomorphism
`lam`, named tensor/Picard prerequisites, finite Weil transition
compatibility and rational adelic comparison are supplied. The tests are
quasi-separated objects of `Over S`. Every original fixed-level tower retains
its torsion finite-etale statement, invertible positive torsion orders,
finite-etale roots of unity and finite-fibre witnesses. The test morphisms
are arbitrary.

## Canonical equality transport

Fix `f : T' → T`, an integral action `a` on the direct family over `T`,
and the literal restricted action
`aD = (relativeEndRestrict B f).comp a` over `T'`. Let `t` and `t'` be points
of `T'` in the same field, with `et : t = t'`, and supply finite-fibre
witnesses at both points. Fix a base point `s` of `T` and equations
`es : t ≫ f.left = s` and `es' : t' ≫ f.left = s`.

`harrisIntegralCMRestrictionRawClass_pointEq` proves that the existing
`Tate.weilAdelicLevelPointEq` for `et` preserves the original raw evaluation
back at `s`, for every original Harris level. The proof substitutes `et`.
The existing fixed-level equality equivalence is then the identity by its
definition; proof irrelevance identifies the finite-fibre witnesses and the
point equations. The original evaluations therefore agree definitionally.
No evaluation-preservation equation is supplied as input.

The base monodromy is the original rational Tate monodromy at `s`; its right
action is the existing opposite source-similitude action on Weil frames,
with the proved commuting-action instance.
`harrisIntegralCMTestLevelOrbitPointEq` restricts that existing fixed-level
equivalence to the subtypes of direct levels whose original raw evaluations
lie in the base monodromy orbit of a fixed raw class `q`. The preceding
equality proves the predicate equivalence needed by `Equiv.subtypeEquiv`.
`harrisIntegralCMTestLevelOrbitPointEq_val` records that the underlying level
is exactly the existing fixed-level equality transport. These results need
only a field for the points, and need no connectedness or local
noetherianity.

For `harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_pointEq`, the base and
test are connected and locally noetherian, the point field is algebraically
closed, and a reference Harris level with a nonempty original fixed-level
set is supplied. These are the assumptions of the existing constructed
finite orbit cover and test equivalence. For every actual scheme map `k`
from the test into this cover, canonical equality transport sends its image
under the correspondence at `t` to its image under the correspondence at
`t'`. The proof applies subtype extensionality and injectivity of original
raw evaluation. The proved evaluation-transport identity and the two
existing value formulas reduce the result to equality of the lifts of `k`
at `t` and `t'`. Over-morphism extensionality and congruence of
`v ↦ v ≫ k.left` along `et` prove that equality.

## Precomposition with a supplied test point

Let `g : T'' → T'`, let `u` be a point of `T''`, and supply a point `t` of
`T'` with `et : u ≫ g.left = t`. Fix `es : t ≫ f.left = s`. Write
`esG = (congrArg (fun v => v ≫ f.left) et).trans es` and
`esC = (Category.assoc u g.left f.left).symm.trans esG` for the corresponding
induced and composite point equations. The target integral action on the
direct family over `T''` is literally restriction along `g ≫ f`.

`harrisIntegralCMTestLevelOrbitPrecompositionAt` first applies
`harrisIntegralCMTestLevelOrbitPointEq` for `et.symm`, from the supplied
point `t` to the induced point `u ≫ g.left`, then the previously constructed
`harrisIntegralCMTestLevelOrbitPrecomposition`. The latter is original
fixed-level restriction along `g` followed by the inverse of the constructed
composite-to-successive literal-action comparison. Thus the new map uses
exactly these original operations on levels.
`harrisIntegralCMTestLevelOrbitPrecompositionAt_val` states its underlying
value definitionally. `harrisIntegralCMRestrictionRawClass_precompositionAt`
proves that it preserves original raw evaluation by applying the established
induced-point precomposition identity and the preceding equality-transport
identity. The selected base orbit remains unchanged.

`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_precompositionAt` assumes
connectedness and local noetherianity of the base and both tests, algebraic
closure of the common point field, and the same reference-level nonemptiness.
For every actual map `k` from `f.left` into the selected orbit cover, its
image under the supplied-point direct-level precomposition is the image of
`Over.homMk g.left rfl ≫ k` under the correspondence for `g ≫ f` at `u`.
The proof unfolds the new map, applies the equality-of-points compatibility
just proved, then the established induced-point precomposition square. No
naturality premise or equivalence transported from Hom sets defines the
level map.

This unit handles equality of points in a common field and compatible
supplied points under test precomposition. General changes of geometric
points, disconnected-test gluing and the normalized rational-isogeny moduli
comparison remain open. It constructs no representing PEL scheme and proves
no new admissibility, smoothness or division-case projectivity result. The
host `DivisionCMRepresentabilityStatement` and every imported Lean/Markdown
pair are preserved; that representability target remains open.

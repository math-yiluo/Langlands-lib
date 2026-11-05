# Test precomposition of original Harris orbit-cover levels

This is an internal deduction from the original fixed-level restriction,
the constructed literal-action comparison, and the actual finite orbit-cover
correspondence. It identifies test precomposition on the selected direct-level
subtypes with precomposition of actual scheme morphisms into the supplied
orbit cover. It introduces no external literature assertion.

The arithmetic carriers, schemes and point field have universe zero. The
Harris CM fields, central simple unitary datum, normalized signature charts
and scalar-tower hypotheses are those of the imported constructions. An
actual abelian family `B/S`, dual witness `W`, dual-valued homomorphism `lam`,
the named tensor/Picard prerequisites, finite Weil transition compatibility
and rational adelic comparison are supplied. The tests are quasi-separated
objects of `Over S`. The torsion finite-etale statement, invertible positive
torsion orders, finite-etale roots of unity and finite-fibre witnesses needed
for each original fixed-level tower remain explicit. No finite or etale
condition is imposed on either test morphism.

## Evaluation at a specified point

For `f : T' → T`, an integral action `a` on the direct family `B_T`, and a
point `t` of `T'`, the action on the direct family `B_T'` is literally
`aD = (relativeEndRestrict B f).comp a`.
`harrisIntegralCMRestrictionRawClass_eq_pointEquiv` identifies original raw
evaluation at an arbitrary point `s` with supplied equality `t ≫ f.left = s`.
It equals `harrisIntegralCMRestrictionRawEquiv` on the underlying raw class,
followed by the existing `weilAdelicFrameRightOrbitPointEq` for that equality.
The proof substitutes the point equality, applies the established original
raw-evaluation formula, and uses quotient induction for the reflexive point
comparison. No point-comparison equation is assumed.

## Original restriction followed by action comparison

Let `g : T'' → T'` be arbitrary and let `u` be a point of `T''`. The point of
`T'` is `u ≫ g.left`. Write `aComposite` for restriction of `a` along `g ≫ f`,
and `aSuccessive` for restriction along `f` and then `g`. These actions are
literally equal by the proved relative integral-action composition law.
The existing `harrisIntegralCMFullActionLevelRestrictionCompIso` compares the
original towers for composite and successive action on the same direct
family `B_T''`, at `u`.

`harrisIntegralCMFullActionLevelPrecomposition` is a natural transformation
from the original direct-level tower on `T'` to the original tower with
`aComposite` on `T''`. It first applies the unchanged
`harrisIntegralCMFullActionLevelRestriction` for `g` and `aD`, then the inverse
of that constructed comparison. Naturality in every original Harris level
arrow follows from composition of these natural transformations. The theorem
`harrisIntegralCMFullActionLevelPrecomposition_apply` states this exact value
at each level; it is definitional.

`harrisIntegralCMRestrictionRawClass_precomposition` proves that original raw
evaluation is unchanged by this map. For any supplied equation
`es : (u ≫ g.left) ≫ f.left = s`, the composite evaluation uses the canonical
equation `(Category.assoc u g.left f.left).symm.trans es`. Evaluation of the
new level along `g ≫ f` equals evaluation of the old level along `f`, in the
same raw orbit set at `s`.

The proof substitutes `es` and uses the preceding point-evaluation formula.
The forward and inverse action comparisons cancel, so the raw composite-action
comparison sends the new level to the underlying class of original restriction
along `g`. The established `harrisIntegralCMRestrictionRaw_comp` rewrites the
composite evaluation as evaluation along `g` followed by evaluation along `f`,
with the canonical associativity comparison of the point. The existing
`harrisIntegralCMFullActionLevelRestriction_rawValue` cancels evaluation along
`g` against its original restriction. These are deductions from actual maps;
no evaluation compatibility premise is supplied.

These constructions and identities need neither connectedness nor local
noetherianity, and the point field need only be a field.

## Selected orbit subtypes and actual covers

At `s`, fix a Harris level `V` and a raw orbit class `q`. The base monodromy
uses the original actual rational Tate transport. The right action and
commuting-action instance are precisely the original Weil-frame actions,
with the existing opposite right-action convention.
`harrisIntegralCMTestLevelOrbitPrecomposition` maps direct fixed levels on
`T'` whose original raw evaluation lies in the base monodromy orbit of `q`
to the corresponding subtype of original direct levels on `T''` with
`aComposite`. Its value is the natural transformation just constructed.
The membership proof uses the proved equality of original evaluations and
the input membership. The theorem
`harrisIntegralCMTestLevelOrbitPrecomposition_val` records the original
restriction and inverse-comparison value definitionally. No choice of a
monodromy-fixed frame is made.

For `harrisIntegralCMFiniteOrbitCoverTestLevelEquiv_precomposition`, the base
and both tests are connected and locally noetherian, and the common point
field is algebraically closed. A reference Harris level with a nonempty
original fixed-level set is supplied, as required to construct the existing
finite orbit cover. For every actual map `k` from the test `f.left` into that
cover, the orbit-subtype precomposition of its image under the existing
`harrisIntegralCMFiniteOrbitCoverTestLevelEquiv` equals the image of
`Over.homMk g.left rfl ≫ k` under that equivalence for `g ≫ f`. Both sides
are elements of the same original direct-level subtype with `aComposite`.

The proof applies subtype extensionality and the established injectivity of
original raw restriction evaluation for `g ≫ f`. The proved evaluation
compatibility reduces the left side to the evaluation along `f`. The existing
value formulas for the two actual test equivalences then reduce the result
to equality of geometric-fibre maps. Over-morphism extensionality and
`Category.assoc u g.left k.left` prove that equality. Thus the theorem compares
the unchanged original level restriction with actual scheme-morphism
precomposition; it does not assume the desired naturality square.

This unit proves this test-precomposition square with the induced point
`u ≫ g.left` and an arbitrary propositional base-point equation. Further
point-independence comparisons, disconnected-test gluing and the normalized
rational-isogeny moduli comparison remain open. No representing PEL scheme,
admissibility, smoothness or division-case projectivity is constructed here.
The host `DivisionCMRepresentabilityStatement` remains open, and its statement
and imported Lean/Markdown pairs are preserved.

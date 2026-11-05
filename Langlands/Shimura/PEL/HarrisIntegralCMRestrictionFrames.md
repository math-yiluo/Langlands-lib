# Actual frame and raw-orbit transport for Harris test restriction

This is an internal deduction from the actual integral-action family comparison,
polarized Tate frames and their pointed base-change maps. It constructs the
frame and raw-orbit evaluation maps for the original Harris restricted family,
proves their composition law, and identifies them with the published original
raw evaluation and fixed-level restriction. It introduces no literature assertion.

## Data and actual maps

The number fields, arithmetic algebra, schemes and point field have universe
zero. The data retain the Harris CM fields, central simple unitary datum `D`,
normalized signature charts `C` and scalar-tower hypotheses of the existing
Harris constructions. The actual abelian scheme `B` over `S`, its dual witness
`W`, dual-valued homomorphism `lam`, tensor/Picard prerequisites `P`, finite Weil
transition compatibility and rational profinite-integer/adele comparison are
supplied. The source and target tests are quasi-separated objects of `Over S`,
with an arbitrary morphism `f : T' → T`. The integral-order action `a` is on the
actual direct pullback `B_T`. The geometric test point `t` is over a field;
this construction needs no algebraic closure, connectedness, local
noetherianity or finite-etale hypothesis on `f`.

Write `aD = (relativeEndRestrict B f).comp a`. Frames on `T'` use the direct
family `B_T'`, its direct pulled dual witness and polarization, and the rational
extension of this literal integral action. Frames on `T` use `a` and the point
`t ≫ f.left`. The intermediate family is the ordinary pullback `f* B_T` with
its ordinary pulled dual data and rational action. All are the existing
`harrisIntegralCMWeilFrame` or `WeilAdelicFrame` types with actual Tate modules
and actual Weil forms.

`harrisIntegralCMRestrictionFrameEquiv` first applies the existing
`weilAdelicFrameIsogeny` for the canonical relative integral-action rational
comparison from `B_T'` to `f* B_T`, then the existing
`weilAdelicFrameBaseChange` from that ordinary pullback to `B_T` at the
composite point. The multiplier-one compatibility of the canonical
polarizations is the published `harrisIntegralCMFullActionRestriction_multiple`;
it is not assumed as another pairing premise.

`harrisIntegralCMRestrictionFrameEquiv_apply` states its actual value. For a
frame `eta` and a vector `x` in the finite adelic scalar extension of `A`, the
value is `rationalHomMap` for `homToHom0` of the actual
`relativeBaseChangeComparisonIso B f`, followed by actual
`rationalBaseChange f.left`. The proof is definitional. The right-equivariance
lemma follows by subtype and linear-equivalence extensionality: both sides
apply this same map to `eta` precomposed with the original source similitude.
The opposite-group convention for this right action is unchanged.

`harrisIntegralCMRestrictionRawEquiv` descends this actual frame equivalence
through `RightOrbit.equiv` for every subgroup of the original finite adelic
source-similitude group. Its representative formula is
`harrisIntegralCMRestrictionRawEquiv_mk`. This is an equivalence of all raw
right-orbit classes, without a monodromy fixedness condition.

## Equality of actions and repeated restriction

`harrisIntegralCMWeilFrameActionEq` transports frames for two literally equal
integral actions on the same direct family at the same point. A private generic
form-isomorphism construction changes only the proofs of linearity for the
equal target module structures; its forward and inverse functions are the
original linear equivalence and its inverse. The form, source module, target
additive group and actual values are unchanged. Equality of the actual
`finiteAdeleAlgebraModule` structures follows by applying their defining
function to the given action equality. Subtype and linear-equivalence
extensionality prove the two inverse laws. The value lemma is definitional,
and the right-equivariance lemma has the same extensionality proof as above.
`harrisIntegralCMWeilRawActionEq` descends this comparison to right orbits.

For a second morphism `g : T'' → T'` of quasi-separated tests, the published
literal `harrisIntegralCMRestrictionAction_comp` identifies the action
restricted along `g ≫ f` with the action successively restricted along `f`
and `g`. `harrisIntegralCMRestrictionFrameCompEquiv` specializes the constructed
action-equality comparison in the direction from composite to successive
restriction. Its value is again unchanged. The corresponding raw equivalence
is `harrisIntegralCMRestrictionRawCompEquiv`.

`harrisIntegralCMRestrictionFrame_comp` proves the square of the actual frame
maps. Begin with a frame for the composite-restricted action at `u` on `T''`.
Transport its action to the successive one, evaluate along `g`, then along
`f`. This equals evaluation along `g ≫ f`, followed by the existing
`weilAdelicFramePointEq` for
`u ≫ (g.left ≫ f.left) = (u ≫ g.left) ≫ f.left`. The point comparison is the
canonical associativity identification, rather than a supplied coherence map.

The private Tate computation first applies
`harrisIntegralCMRestrictionRationalComparison_comp` to the actual rational
homomorphisms. Applying `rationalHomMap` converts their composition identity
to an equality of Tate values. Naturality of rational base change moves the
first family map through the second base change. The published group-scheme
Tate base-change composition formula compares the two test objects through
the actual `Over.mapComp` isomorphism. Ordinary pullback-comparison hom and
inverse cancel by functoriality. This proves the computation for arbitrary
Tate test objects and index predicates. In the frame theorem, the published
point-equality underlying-map formula identifies the point comparison with
this actual `Over.mapComp` isomorphism. Extensionality and the proved actual
value formulas reduce the frame square to that Tate computation.

`harrisIntegralCMRestrictionRaw_comp` is the corresponding composition square
on all actual right subgroup-orbit classes. Quotient induction reduces it to
the proved frame square, and congruence of `RightOrbit.mk` concludes. Its point
comparison is the published `weilAdelicFrameRightOrbitPointEq`. No composition
law on raw orbits is assumed.

## Original evaluation and fixed-level restriction

The final section retains the finite-fibre witnesses at `t` and `t ≫ f.left`,
the torsion finite-etale statement, invertible torsion orders on `T'`, and
finite-etale roots of unity on `T'`, as required to form the original direct
fixed-level tower. A level is an orbit class fixed by the actual monodromy;
no fixed representative is required.

`harrisIntegralCMRestrictionRawClass_eq_rawEquiv` identifies the original
`harrisIntegralCMRestrictionRawClass` at this composite point with
`harrisIntegralCMRestrictionRawEquiv` applied to the underlying class of the
original direct fixed level. Unfolding the original raw evaluation gives
ordinary orbit base change applied to the raw class of the actual family
comparison. The latter is the original right-orbit map of the actual frame
isogeny. `RightOrbit.map_comp` identifies their composite with the defined
frame evaluation. The original function and tower are not redefined.

The fixed-restriction subsection additionally retains invertible torsion orders
and finite-etale roots of unity on `T`, as required by the original
`harrisIntegralCMFullActionLevelRestriction`.
`harrisIntegralCMFullActionLevelRestriction_rawValue` proves that applying the
constructed raw evaluation to the underlying class of this actual restricted
level returns exactly the original raw class. The preceding identification
reduces it to the original evaluation formula. The forward and inverse
components of the canonical family-comparison tower isomorphism cancel, and
the ordinary orbit base-change equivalence cancels its inverse.
`harrisIntegralCMFullActionLevelRestriction_val` then uses the inverse law of
the constructed raw equivalence to express that underlying restricted class
as its inverse applied to the original class.

These results concern supplied polarized families and actual test restriction.
They do not yet construct the fixed-level composition comparison, establish
full-test naturality of the orbit-cover equivalence, perform disconnected-test
gluing, or identify the full normalized rational-isogeny moduli presheaf with a
representer. Existence, admissibility, smoothness and division-case projectivity
of a representing PEL scheme remain obligations. The contribution preserves
`DivisionCMRepresentabilityStatement` and every imported Lean/Markdown pair.

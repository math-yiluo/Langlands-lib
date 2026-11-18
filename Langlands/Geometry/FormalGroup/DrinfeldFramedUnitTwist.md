# Actual integer-unit target conjugation of framed triples

This internal construction specializes actual framed target transport to the
specified integer-order unit conjugation maps. It proves that the resulting
actual conjugated triples have the same class in the existing framed quotient,
and that the descended maps are the identity natural transformation of the
actual framed comparison-class Nilp functor.

The retained hypotheses are those of `DrinfeldFramedAtlas`: a nonarchimedean
local field `K`, a finite-dimensional central division algebra `D`, supplied
embedded and residue fields, a fixed height-certified special formal frame
`Φ`, a Nilp object `A`, and the actual height-zero framed representative `X`.
For an actual unit `u : (IntegerRing K D)ˣ`, `X.twistIntegerUnit u` retains the
same residue map and uses exactly the height-certified target constructed in
`SpecialAtlasUnitTwist`. The underlying target formal `𝒪[K]`-atlas is unchanged;
the order action is conjugated by `a ↦ u⁻¹ a u`.

The new framing is the canonical whole rational target-isomorphism transport.
Here the target covers are identical, so source transport is the identity.
`twistIntegerUnit_rho` exposes the resulting whole quasi-isogeny: the original
framing postcomposed with the quotient reduction of the actual target
isomorphism whose forward map is the action of `u⁻¹` and whose inverse is the
action of `u`. It follows by cancellation of the identity source map. Actual
local kernel-rank height zero and both rational inverse equations are retained
by the target-transport construction.

`twistIntegerUnitComparison` is an actual comparison in the original framed
relation. Its original target comparison is exactly
`SpecialAtlas.twistIntegerUnitComparison`, and its original all-test framing
certificate is proved by the generic target-transport theorem. Thus
`comparisonClassOf_twistIntegerUnit` proves equality in the SAME existing
framed comparison quotient. It imposes no new equivalence relation and assumes
no extra framing square.

`Comparison.twistIntegerUnit` preserves any original framed comparison by
composing it with the two canonical unit comparisons. This gives an actual
operation `ComparisonClass.twistIntegerUnit` by the original quotient lift.
Quotient induction and the canonical unit comparison prove that it fixes every
class. Naturality follows from this equality to the identity operation;
`integerUnitTwistNatTrans` is defined using the descended actual operation and
`integerUnitTwistNatTrans_eq_id` proves its equality to the identity natural
transformation. No equality of representatives after coefficient extension is
asserted by this proof.

The provenance is internal, using the actual integer-unit inverse formal maps,
whole target-isomorphism transport, and the original framed quotient. The
source motivation is Drinfeld 1976, §2 A, printed p.109 (PDF page 3), whose
inverse-conjugation convention and integer-unit triviality are recorded in
`DivisionOrder`. This realizes the unit-conjugated triple and its triviality on
our actual framed quotient. It does not construct a matrix quasi-endomorphism
identification, the full `GL(d,K) × Dˣ` action, its determinant/Frobenius
correction, or representability.

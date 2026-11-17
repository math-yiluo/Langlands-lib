# Actual determinant subobjects in Deligne admissibility

This module identifies the established admissibility predicate with
Drinfeld's three conditions using actual determinant subobjects in
condition (c). It proves base-change stability of that formulation and
preservation under the established determinant-corrected general linear
operations. The existing admissible objects, isomorphism classes and
class functor can therefore be used with this literal subsheaf
formulation.

The source is V. G. Drinfeld, *Coverings of p-adic symmetric regions*
(1976), Section 2 A, the final paragraph of printed p.109 and the
opening paragraph of printed p.110 (PDF pp.3–4). These passages specify
the four data eta, T, u and r and conditions (a), (b) and (c).
The registered source is
`drinfeld-1976-coverings-p-adic-symmetric-regions`, SHA256
`7dd09e1967f46c29195ec87a400e145a17374368fc3b9dd0a782b5b7bfc44e2f`.
The results here are derived comparisons and transport results for
those conditions, rather than additional theorems attributed to the
source.

The parameters are a commutative ring O, an O-algebra field F, a
nonzero natural d, an element pi of O with nonzero image in F, a scheme
S and a scalar map O to its global sections. They use the common
universe of the existing modules. The input is the actual
`SheafPreDatum`. The final normalized general linear result further
assumes O is a discrete valuation domain, F is its fraction field and
pi is irreducible. No representing or universal object is supplied.

`SheafPreDatum.SubsheafAdmissible` is the conjunction of the existing
`ConstantOnPiZeroLoci` and `ResidueFibreInjective` predicates and the
independently constructed `DeterminantSubsheavesNormalized` condition.
Thus condition (a) is constancy of the inverse-image component sheaf
on each actual Pi-zero subspace with fibre O^d. Condition (b) is
injectivity of the constructed total quotient-to-residue-fibre map.
Condition (c) is equality, for every integer n, of the component
determinant subobject and the normalized translated-frame determinant
subobject on the actual Pi-zero subspace of degree n modulo d. The
factor pi^(-n) is applied after taking the d-th exterior power.
These subobjects are images in the rational exterior sheaf, with the
scope documented in `DeligneDeterminantSubsheaf`.

`subsheafAdmissible_iff` proves that this conjunction is equivalent to
the established `Admissible` predicate. It unfolds the two conjunctions
and substitutes `determinantSubsheavesNormalized_iff`, whose proof
computes both actual determinant stalk images and detects equality of
sheaf subobjects by their stalks. This comparison introduces no
additional mathematical premise.

`DeterminantSubsheavesNormalized.pullback` proves condition (c) for the
independently constructed determinant subobjects of `D.pullback f`
along any scheme morphism f. It converts the original equality to
`DeterminantNormalized`, applies its established pullback theorem, and
converts back using the comparison for the actual pulled datum.
`SubsheafAdmissible.pullback` combines this with the existing pullback
theorems for (a) and (b). There is no flatness, surjectivity or
nilpotence assumption on f. Reflection or descent is not concluded.

`SheafDatum.determinantSubsheavesNormalized` and
`SheafDatum.subsheafAdmissible` expose these actual conditions for
every representative in the existing admissible type.
`ofSubsheafAdmissible` constructs a member of that same type from the
three subsheaf conditions, retaining exactly the given preliminary
datum. `pullback_ofSubsheafAdmissible` shows that this constructor
commutes with the existing admissible pullback; the underlying data
agree definitionally, so subtype extensionality proves the equality.
Consequently no second admissible quotient or class functor is needed:
every representative used by the established functor satisfies these
conditions, and every datum satisfying them supplies a representative.

`subsheafAdmissible_shiftReframe_iff` transfers the established
two-way preservation theorem for a member of `shiftReframeSubgroup`
through the proved equivalence. Membership is the existing integral
unit condition on the shift-corrected determinant, not an
admissibility premise. In the discrete valuation setting,
`subsheafAdmissible_normalizedReframe_iff` similarly proves preservation
for every F-linear automorphism g, using the canonical shift
minus the normalized order of det(g). Thus the established normalized
general linear operation preserves all three actual conditions.

These results identify the predicate used by the existing class
construction and prove its transport properties. They do not prove
integral injectivity, additional local freeness of determinant images,
existence of admissible objects, or representability.

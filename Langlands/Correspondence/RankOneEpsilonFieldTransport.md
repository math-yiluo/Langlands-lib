# Rank-one arithmetic epsilon expressions on the original base field

Worker 1555 derives this internal transport unit from the existing actual
bottom-field algebra equivalence, generic field transport, canonical abelian
epsilon transport, and the normalized rank-one arithmetic epsilon formula.
No additional original-literature assertion is introduced.

`baseFieldAdditiveCharacterEquiv` transports the actual continuous,
nontrivial, unit-circle-valued additive characters from the original field
`F` to the bottom intermediate field of its algebraic closure. It uses
inverse pullback along the inverse of `baseFieldPadicEquiv`, so evaluation
at a bottom-field element is evaluation of the original character at its
image in `F`. The canonical p-adic isometry proves continuity in both
directions. `isBaseCharacter_iff_eq_baseFieldAdditiveCharacterEquiv` uses
character extensionality to identify the unchanged `IsBaseCharacter`
predicate with equality to this transported character.

`baseFieldHaarMeasureEquiv` is the corresponding equivalence of actual
regular additive Haar measures. Its forward map pushes the original
measure along the inverse field equivalence. Its inverse pushes a
bottom-field measure back to `F`. No Jacobian scalar is inserted because
the measures themselves are transported.

`isSelfDual_baseFieldTransport_iff` specializes the existing intrinsic
Fourier self-duality transport to these same maps. The predicate retains
convergence of the second Fourier integral for every Schwartz--Bruhat test
function and the identity that Fourier squared is reflection. The
compatible-character version uses the character equality and the inverse
law of the Haar-measure equivalence. `baseSelfDualMeasureExists_iff`
transports the full existence proposition in both directions and asserts
no unconditional measure existence.

`abelianEpsilonExpression_baseFieldTransport` specializes the published
canonical field-transport identity for the full measure-dependent abelian
epsilon expression. Both the unramified volume expression and the
convergent ramified Gauss integral are covered by that imported theorem.
The multiplicative character map, additive character map and Haar map
agree with the existing maps by their definitions. The compatible-character
version applies the inverse Haar equivalence, hence covers every compatible
bottom-field additive character and every actual bottom-field Haar measure.

`conditionalPairEpsilonValue_on_baseField` rewrites the full normalized
rank-one pair epsilon formula using that comparison. The result is the
original field's actual `abelianEpsilonExpression`, evaluated at
`normalizedAbsPowerCharacter s * (chi * eta)`, the original additive
character and the inverse-transported actual measure. It applies to every
continuous actual bottom restriction of the two specified rank-one Weil
classes. The geometric Frobenius and complex parameter remain arbitrary.
The existing formula already includes the invariant-quotient determinant
correction, so the equality concerns the full epsilon value.

`isArithmeticPairEpsilonFactor_rankOne_on_baseField_iff` rewrites the exact
arithmetic certificate entirely in terms of the original field's harmonic
data. Its right side keeps existence of a self-dual regular additive Haar
measure, existence of a bottom-field geometric Frobenius, and the universal
identity for every original-field self-dual measure and every complex
spectral parameter. The forward direction transports an arbitrary supplied
measure to the bottom field and applies the original universal clause.
The reverse direction transports every compatible bottom-field datum back
to `F`. The Haar equivalence and preserved self-duality prove that no
witness or universal condition is lost. The epsilon monomial keeps the
original base residue cardinality, coefficient `c : Complex` units and
exponent `m : Int`.

The prime and finite p-adic field are arbitrary. The field, parameter-carrier
and supplied-system universes remain independent. Standalone reciprocity,
common-closure reciprocity, their compatibility and a validated local-constant
system are supplied premises. This unit constructs none of these inputs,
selects no self-dual measure or monomial constants, and proves neither an
analytic epsilon comparison nor the closed supercuspidal correspondence.

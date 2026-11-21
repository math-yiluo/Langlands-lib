# Finite locally free Cartier duality over an affine base

`finiteLocallyFreeCartierDuality` proves
`FiniteLocallyFreeCartierDualityStatement`. The coordinate construction
and its evaluation identification follow Demazure and Gabriel,
*Groupes algébriques*, Tome I (1970), Chapter II, §1, no. 2, 2.10(a)
and the proposition in 2.10(d), printed pp. 156–158.

Finiteness over `Spec R` makes the total space affine. Its coordinate
Hopf algebra `A` is finite and flat as a module and finitely presented
as an algebra. Finite presentation as a module then follows, and
flatness makes this module projective. Commutativity of the given
group supplies cocommutativity of its coordinate Hopf algebra by
testing the two tensor inclusions. The dual scheme is the relative
spectrum of the finite projective module dual. Convolution gives
its multiplication. Transposition gives its comultiplication,
counit and antipode. The finite projective module structure of the
dual gives finiteness, flatness and local finite presentation of its
structure map.

The coefficient tensor for a point of the dual evaluates to units on
the original group. The group-like equations give multiplicativity
and the identity law. On any test scheme the relative spectrum
adjunction identifies the points with algebra maps to its relative
global sections. Restricting the dual point on every map into the
test gives a natural family of group homomorphisms, and the relative
Yoneda comparison gives an actual relative character. Its evaluation
at a point is the value of that pairing.

On an affine test `Spec C`, any relative character gives a tensor in
`A ⊗[R] C` by evaluation on the universal point. The identity and the
two universal points for multiplication give the group-like
equations. Contracting the tensor against the dual gives the
corresponding algebra map to `C`. The universal point determines the
character and recovers the original coefficient tensor of a dual
point, so the comparison is bijective on these tests. The additive
point presheaf and the relative character presheaf are Zariski
sheaves. Affine covers make their comparison locally injective and
locally surjective, giving the natural isomorphism on all tests.

The module evaluation equivalence is a bialgebra equivalence with
the double dual. Its relative spectrum identifies the original
Hopf spectrum with the double-dual spectrum. Composing this
identification with the character comparison for the first dual
gives the required biduality. Flipping the universal pairing tensor
and applying the evaluation equivalence gives the tensor for the
reversed pairing, which proves the equality of actual evaluations
on every test scheme. Finally, the affine coordinate isomorphism
transports both representations to the given group scheme.
Compatibility of evaluation with precomposition preserves the
equation under this transport.

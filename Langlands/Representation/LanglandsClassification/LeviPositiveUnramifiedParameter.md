# Positive unramified Levi characters realizing actual real parameters

Worker 148. This internal construction realizes every real character
parameter of an actual rational Levi's split component by a positive
continuous unramified character of that same Levi. All groups and component
inclusions are the original group schemes. The field is a
nonarchimedean local field, and the Levi has its canonical rational-point
topology. No chamber assumption is required.

`leviPositiveParameterFunctional` chooses the extension furnished by the
published actual-image positive-character extension theorem. That theorem
extends the component functional to the actual integer valuation image of
the connected reductive Levi. `leviPositiveUnramifiedCharacter` exponentiates
it and uses the published canonical image/unramified-character equivalence
to obtain a continuous character trivial on the common norm kernel.
Connected reductivity supplies the affine and finite-type structures used
by this equivalence.

The restriction theorem is an equality of actual point homomorphisms: on
the component, the new character is exactly the positive character of the
input parameter. Its normalized real part is therefore the input.
This proves surjectivity of the Levi real-part map and injectivity of the
chosen section. Direct evaluation of the exponential proves that the
character has positive real part and zero imaginary part at every Levi
point. The choice of extension is not asserted to be unique, linear or
multiplicative.

For an individual supplied actual opposite standard Jacquet exponent,
`OppositeStandardJacquetFamily.positiveUnramifiedCharacter` applies this
construction to the exponent's original component real parameter. Its
restriction has the same modulus as the actual exponent at every component
point, by the published all-point split-torus norm formula. Dividing the
exponent by this restriction thus has norm one at every point. Under the
finite-type and monomorphism instances used by the supplied actual
reflection data, its actual full torus parameter is the full lift of the
original exponent, by full-parameter uniqueness. Representation and field
universes remain independent. Admissibility and finite length are not
needed for a supplied exponent. The exponent specialization retains the
Hausdorff field assumption of the actual Jacquet family.

The provenance is internal: the module specializes the actual-image
extension and canonical unramified-character comparison and combines them
with the published positive split-torus character, norm and lift laws.
It does not construct a positive-part cone projection or a tempered
representation, prove V.3.18, or establish Langlands exhaustion or the
classification.

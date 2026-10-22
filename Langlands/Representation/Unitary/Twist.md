# Invariant positive forms under unit-modulus scalar twists

This derived construction transports actual positive definite invariant
Hermitian forms through a scalar twist. The group and complex vector-space
carrier have independent universes. The carrier need not be finite dimensional,
normed, topological, or complete. The character is an actual homomorphism
`χ : G →* ℂˣ`, with the explicit hypothesis `‖χ g‖ = 1` for every group element.
No topology on the group or continuity of the character is needed for this
algebraic construction.

`InvariantPositiveForm.twist` retains the entire `InnerProductSpace.Core` of
the supplied form and proves its invariance for the twisted action.
`InvariantPositiveForm.untwist` retains the same core and proves invariance for
the original action. Sesquilinearity multiplies the inner product of two
transformed vectors by `conj (χ g) * χ g = ‖χ g‖² = 1`. The auxiliary calculation
therefore identifies the two invariance conditions. Positivity and definiteness
are preserved because the underlying form is unchanged.

The two transports are inverse, and `InvariantPositiveForm.twistEquiv` packages
them as an equivalence of the actual spaces of invariant positive forms. The
inner-product value formulas are definitional equalities. Finally,
`isUnitarizable_twist_iff` transports existence of a form in each direction.
These are intrinsic obligations of the construction and are fully proved.

The imports are the published `Representation.Unitary.Basic` definition of
unitarizability and `Representation.Twist.Definitions` scalar action. The
published finite-dimensional Weil result in `Weil.Representation.UnitaryProof`
uses the same sesquilinear calculation, but its finite-dimensional domain does
not cover potentially infinite-dimensional smooth supercuspidal carriers.
The present construction supplies that general algebraic prerequisite. It does
not construct a supercuspidal lattice restriction, a smooth contragredient, an
orbit classification, or a correspondence.

The motivating conventions are Guy Henniart, *Une preuve simple des conjectures
de Langlands pour GL(n) sur un corps p-adique*, Inventiones mathematicae 139
(2000), section 1.1 and footnote 1, printed page 439 (unitary characters), and
section 1.2(2), printed page 440 (scalar twisting through the determinant).
Literature ID: `henniart-2000-simple-proof`; retained original SHA-256:
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`.
The general form equivalence is an internal derived construction from the
published positive-form and scalar-twist definitions, not a theorem quoted
from Henniart or a proof of his correspondence compatibility.

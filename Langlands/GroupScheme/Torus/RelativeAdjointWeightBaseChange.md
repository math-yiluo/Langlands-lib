# Actual relative adjoint weights under arbitrary base change

Let `G` be a smooth affine group over `Spec r`, with `r` an arbitrary
commutative ring. For every commutative `r`-algebra `K`,
`Lie.smoothSchemeScalarExtension` identifies the tensor extension of
the actual base Lie module with the actual Lie module of the scheme
pullback over `K`. It combines the actual test-algebra scalar-extension
equivalence with the actual Lie-kernel scheme-pullback comparison.
The simple-tensor and all-test coefficient-change formulas are proved.

For an actual homomorphism from a coordinate split torus into `G`,
`splitTorus.baseChangeHom` is the resulting homomorphism from the
coordinate split torus over `K` into the actual pullback group. It
uses the inverse of the canonical split-torus base-change
isomorphism, followed by the pullback of the given homomorphism.

`exponentWeightBaseChangeEquiv` identifies the tensor extension of each
actual exponent weight submodule with the actual exponent weight
submodule of this homomorphism after scheme base change. There is
no flatness, field, reducedness or noetherian assumption on the
base-change algebra.

First, the all-test character weight equation is preserved on pure
extended vectors by actual Lie-kernel adjoint compatibility. Fixed
exponent characters commute with arbitrary base change, and the
existing character-weight reparametrization lemma identifies these
with the correct exponent weight spaces of `baseChangeHom`.

The image of each tensor-extended summand is therefore contained in
its prescribed actual target weight summand. The extended source
summands still span the entire tensor module. The target summands
are independent, by the actual universal-coefficient decomposition.
The modular-lattice lemma
`iSupIndep.le_iff_eq_of_iSup_eq_top` consequently makes all these
containments equalities at once. Finally, extension of the
source internal direct-sum decomposition makes the tensor map onto
each extended source submodule bijective. Transport through the
actual Lie-module equivalence and the proved image equality
constructs the asserted weight-summand equivalence.
Its proved simple-tensor formula identifies its inclusion into the
target Lie module with the actual scheme scalar-extension map.

The provenance is internal: this generalizes the existing field
weight-vector base-change proof using actual smooth Lie scalar
extension, the fixed-exponent character comparisons and the actual
relative adjoint-weight decomposition. It provides the actual
scheme-fibre comparison needed to interpret relative weight ranks;
reductive-locus openness remains a separate structural obligation.

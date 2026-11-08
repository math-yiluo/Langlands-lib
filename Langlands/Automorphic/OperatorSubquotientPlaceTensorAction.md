# Actual two-place enveloping tensor actions on automorphic operator quotients

This internal construction works with every number field `F : Type uF`,
every natural rank `n`, complex coefficients and an actual
`OperatorSubquotient F n`. It uses the unchanged quotient carrier
`Q.Space` and the genuine global enveloping action `Q.envelopingAction`,
which is the action induced on the module quotient by the existing global
differentials. No additional invariance, covariance, finiteness or
distinctness hypothesis is supplied beyond those stated below.

The three commutation theorems state that the actual quotient place
enveloping operators of `OperatorSubquotientPlaceAction` commute, for all
local enveloping elements, at two distinct real places, at two distinct
complex places, and at one real and one complex place. Each proof applies
`Q.envelopingAction` to the proved commutation of the actual included
global algebra elements and uses multiplicativity.

`realPlacesEnvelopingTensorAction`,
`complexPlacesEnvelopingTensorAction` and
`realComplexPlacesEnvelopingTensorAction` compose `Q.envelopingAction`
with the existing actual two-place algebra tensor maps of
`ArchimedeanPlaceEnvelopingTensor`. They are unital complex algebra
homomorphisms from the complex algebra tensor product of the two local
enveloping algebras into `Module.End ℂ Q.Space`. Same-type place pairs
retain the explicit hypothesis `h : v ≠ w`; the mixed pair takes one real
place and one complex place and needs no inequality. At a complex place
each factor is still the universal enveloping algebra of the
complexification of the full underlying real matrix Lie algebra.

The `_tmul` theorems identify the action of a pure tensor `a ⊗ b` with the
product, that is composition, of the place-`v` quotient action of `a` and
the place-`w` quotient action of `b`. The `_projection` theorems hold by
definition for every tensor element: on the canonical projection of a
numerator vector, the quotient tensor action is the projection of the
existing numerator tensor action of `PlaceEnvelopingTensorAction` on
`Q.upper.Space`. The three `...TensorProjection` definitions package the
canonical projection, with underlying linear map `Q.projection`, as an
intertwining map from the numerator tensor action to the quotient tensor
action.

Every quotient tensor action commutes with every finite adelic translation
of the quotient, by the published quotient finite/enveloping commutation
applied to the global image of the tensor element.

For `p : ArchimedeanCompactFactors F n`, the product of orthogonal groups
at real places and unitary groups at complex places, the three
`...CompactConjugatedEnvelopingTensorAction` definitions compose each
tensor action with `Q.compactEndConjugation` at
`toStandardCompact F n p`, the conjugation of `Module.End ℂ Q.Space` by
the actual compact quotient translation. The
`compactRepresentation_...EnvelopingTensorAction` theorems state, for
every tensor element `a` and every quotient vector `f`, that compact
translation applied to the tensor action of `a` on `f` equals the tensor
action of the tensor adjoint of `a` on the translated vector. The
`compactEndConjugation_...` theorems state the same identity as an
equality of quotient endomorphisms. The adjoint is
`unitaryMatrixEnvelopingTensorConjugation` with the convention
`X ↦ k X k⁻¹`; it uses `p.1 v` and `p.1 w` in the real/real case,
`p.2 v` and `p.2 w` in the complex/complex case, and `p.1 v` and `p.2 w`
in the mixed case. The three `_eq` theorems identify each conjugated
action, as a complex algebra homomorphism, with the tensor action composed
with that tensor adjoint. These statements cover every tensor element, not
only pure tensors.

The covariance proofs apply the published quotient compact/enveloping
identities `compactRepresentation_envelopingAction` and
`compactEndConjugation_enveloping` to the global image of the tensor
element and rewrite with the published whole-tensor adjoint compatibility
`envelopingConjugation_realPlacesTensorMap`, or its complex/complex or
mixed counterpart. Algebra-homomorphism extensionality gives the `_eq`
theorems.

For an equivalence `e : Q.Equivalence T` of actual quotients, the three
`Equivalence....TensorRestriction` definitions keep the linear equivalence
`e.toLinearEquiv` and show that it intertwines the corresponding tensor
actions of `Q` and `T`, using that `e` intertwines every concrete operator,
in particular every global differential.

Provenance is internal. The construction reuses `OperatorSubquotient`,
`OperatorSubquotientArchimedean`, `OperatorSubquotientPlaceAction`,
`OperatorSubquotientPlaceCovariance`, `PlaceEnvelopingTensorAction`,
`ArchimedeanPlaceEnvelopingTensor` and
`ArchimedeanPlaceEnvelopingTensorAdjoint`. It is the quotient analogue of
the numerator modules `PlaceEnvelopingTensorAction` and
`PlaceEnvelopingTensorCovariance`. No quotient induction, original
literature assertion, topology or normalization convention is introduced.

These results retain the entire quotient carrier. They do not construct
`(𝔤, K)`-module structures, a tensor decomposition of the carrier, a
faithful tensor action, irreducible or admissible archimedean tensor
factors, local Langlands attachments, automorphic existence or spectral
existence. The local additive-group instances have explicit module-specific
names and use the original submodule additive-group structures.

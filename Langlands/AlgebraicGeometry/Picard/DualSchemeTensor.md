# Tensor multiplication on a chosen dual parameter scheme

Let `A/S` be an abelian scheme and let `hA : HasDualScheme A`. The existing
existence proposition asserts that an actual rigidified Picard-zero family on
some parameter scheme satisfies the specified universal property. Write `D`
for the chosen parameter scheme `dualScheme A hA`, an object of `Over S`, and
`P` for its chosen universal family.

This module constructs an actual multiplication morphism `D ×_S D → D` by
classifying the tensor of the two pullbacks of `P`. It proves its action on
all test schemes, its two unit equations, and commutativity under the explicit
premises stated below. No group-scheme structure is asserted yet.

## Classification by actual pullback

The construction takes `PicardZeroPullbackStatement` as the parameter
`stability`. This is the existing proposition that actual relative pullback
preserves the geometric Picard-zero condition. For every `T : Over S`,
`dualPointClass f` is the actual rigidified pullback class of `P` along a
morphism `f : T → D`, with its Picard-zero membership proof. It is a
specialization of `picardZeroClassifyingMap`.

`dualPointClass_classify` and `dualClassify_pointClass` prove that this map and
the existing `dualClassify` are inverse functions. The first follows by subtype
extensionality from the universal classification equation; the second follows
from uniqueness in that universal property. `dualPointClass_injective` is the
injectivity part of the already proved bijectivity of the actual classification
map. Thus these statements do not introduce an arbitrary bijection as data.

`dualPointClass_comp` identifies the class of a composite parameter map with
the pullback of its class. It uses the published proof
`RigidifiedModule.pullbackCoherence`, rather than adding that theorem as a new
hypothesis.

## Multiplication and its point formula

`dualTensor` additionally takes `pullbackTensorComparisonIsIsoStatement` as
`preservation`, the invertibility proposition for the fixed canonical tensor
comparison. It uses the categorical product `D ⨯ D` in `Over S`, which is a
fibre product over `S`, and is defined by

`dualClassify (dualPointClass prod.fst ⊗ dualPointClass prod.snd)`.

Here the tensor is exactly `picardZeroClassesTensor`, constructed from the
actual rigidified line-bundle tensor and its proved geometric closure. The
universal property produces a morphism in `Over S`; neither a multiplication
morphism nor a desired classification equation is stored as unconstrained data.
`dualTensor_spec` is its universal classification equation.

For the point formula, the module additionally retains
`PullbackTensorCompositionStatement` and
`PullbackTensorLeftUnitorStatement`, the compatibility equations for the fixed
canonical maps. `dualTensor_points` says that for every test scheme `T` and
all `f,g : T → D`, the class classified by

`prod.lift f g ≫ dualTensor`

is the tensor of the classes classified by `f` and `g`. The proof uses
classification under composition, the defining equation of `dualTensor`,
tensor-pullback naturality, and the two product-projection identities.
`dualClassify_tensor` gives the equivalent formula starting with any two
Picard-zero classes. It follows by injectivity of `dualPointClass` and the
inverse identities above.

## Origin, units, and commutativity

The distinguished `dualOrigin : S → D` already classifies the canonically
rigidified trivial bundle. `dualPointClass_origin` proves that its pullback
to any test scheme classifies that scheme's trivial family, using the existing
`dualClassify_trivial` equation and the inverse classification identity.

The two unit equations take
`PullbackTensorUnitCoherenceStatement`, the conjunction of the specified left
and right tensor-unit diagrams, in addition to stability, preservation, and
tensor-composition compatibility. They assert that pairing the identity of `D`
with the origin pulled back along `D → S`, in either order, followed by
`dualTensor`, equals the identity of `D`. Applying the injective classification
map reduces these morphism equalities to the two previously proved unit laws
on Picard-zero classes. The point formula uses the left component of the
stated unit-coherence conjunction.

`dualTensor_points_comm` instead retains the left-unit and composition
premises and additionally takes `PullbackTensorSymmetryStatement`. It asserts
commutativity on every pair of test-scheme points, by the corresponding
commutativity of their Picard-zero classes. `dualTensor_comm` specializes this
to the two projections and uses the product identities to prove the morphism
equation

`prod.lift prod.snd prod.fst ≫ dualTensor = dualTensor`.

This is the actual factor-swap map on `D ×_S D`, not an independently supplied
commutativity witness.

## Provenance and scope

This is the derived transport of the Library's actual tensor operation through
the universal rigidified family. Edixhoven–van der Geer–Moonen,
*Abelian Varieties*, Chapter VI, paragraph (6.2), printed p.88 (PDF p.92),
specifies tensor and pullback on rigidified classes and the universal
classification property of the Poincare family. The module implements that
universal-property construction using the previously defined geometric
Picard-zero subfunctor and chosen dual.

The existence proof `hA` remains explicit. No arbitrary-base existence theorem
is asserted, and no projectivity or noetherianity assumption is added to this
conditional construction. The canonical comparison propositions named above
are not proved here. Associativity, an inverse morphism, and the geometric
properties needed for the chosen parameter scheme to be an abelian scheme are
separate obligations. These results therefore supply a binary multiplication
with the proved conditional unit and commutativity equations, not yet a
complete dual abelian scheme.

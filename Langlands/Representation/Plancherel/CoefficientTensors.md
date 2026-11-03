# Coefficient tensors of a canonical smooth representation

This module constructs the algebraic coefficient tensor and its coefficient
map on the existing `Langlands.SmoothRep` framework. All declarations below
are in `Langlands.Plancherel`.

## Source and scope

J.-L. Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI [10.1017/S1474748003000082](https://doi.org/10.1017/S1474748003000082),
V.1, printed p.288 (PDF p.54), identifies the source's product-induced
space `L(ω,P)` with the tensor of the normalized induced representation
and its smooth contragredient. It defines the coefficient on a pure tensor
by `ℓ(π(g)v)`, extends it linearly, and identifies the image with the
coefficient space `A(π)`.

VI.1, printed pp.295–296 (PDF pp.61–62), transports such tensors along
representation isomorphisms using the original isomorphism on vectors
and inverse pullback on functionals. Its stabilizer example explicitly
uses `A ⊗ transpose(A⁻¹)`.

The present construction is an internal general prerequisite for those
passages. It implements the tensor side, for any canonical smooth
representation and any commutative coefficient ring. It does not yet
identify a product-induced space with this tensor, specialize to normalized
parabolic induction, or prove independence from the chosen representation
isomorphism. The two transport coherence laws proved here concern a
specified isomorphism, its identity, and its composite. The source's
choice independence for irreducible admissible inducing representations
requires an additional Schur argument on the inducing representation;
irreducibility of the induced representation is not a hypothesis here.

## Hypotheses and reused objects

Let `R : Type uR` be a commutative ring and `G : Type uG` a topological
group. Let `A : SmoothRep.{uR,uG,uV} R G`. This uses the existing canonical
category and its actual action `A.representation`, rather than a new
representation interface. The carrier has an `R`-module structure and no
topology. No local compactness, admissibility, irreducibility, field
characteristic, splitness or reductive-group hypothesis is needed.

`SmoothDual A.representation` is the existing submodule of the algebraic
dual consisting of smooth functionals for the contragredient action.
`smoothContragredient` is the actual restricted dual action.
`matrixCoefficient_isLocallyConstant` and `matrixCoefficient_biInvariant`
are imported from `MatrixCoefficient.LawsProof`.

The field/ring, group and representation universes remain independent.
The dual and tensor carrier naturally lie in `Type (max uR uV)`.
For transports, the target representations can have independent carrier
universes `uW` and `uX`.

## Tensor and coefficient map

`CoefficientTensor A` is the algebraic tensor

`A ⊗[R] SmoothDual A.representation`.

`smoothCoefficientBilinear A` is the bilinear map taking `(v,ℓ)` to the
locally constant function `g ↦ ℓ.val (A.representation g v)`. Local
constancy follows from smoothness of `v`. Additivity and scalar linearity
are proved pointwise using the linearity of the action and the functional.

`coefficientTensorMap A` is its actual tensor-product linear extension.
`coefficientTensorMap_tmul` proves the displayed formula by definitional
equality.

`range_coefficientTensorMap` identifies the range with the `R`-linear span
of the functions `smoothCoefficientBilinear A v ℓ`. Tensor induction gives
containment in the span; each generating coefficient is the image of its
pure tensor, which gives the reverse containment. This is the generic
coefficient-space assertion used in V.1. No injectivity is asserted.

## Product action and translations

`coefficientTensorAction A` is the actual representation of `G × G`
obtained by pulling `A.representation` back along the first projection,
pulling its smooth contragredient back along the second projection, and
using `Representation.tprod`. `coefficientTensorAction_tmul` states

`(a,b) · (v ⊗ ℓ) = A.representation a v ⊗ smoothContragredient A.representation b ℓ`.

`isSmooth_coefficientTensorAction` proves smoothness. Open subgroups
fixing `v` and `ℓ` give a product open subgroup fixing their pure tensor.
Smoothness is closed under addition, so tensor induction gives the result.
`coefficientTensorObject A` bundles this proved action as a canonical
`SmoothRep` of `G × G`.

`coefficientTensorMap_action` proves, for all tensors `t` and `g : G`,

`coefficientTensorMap A ((a,b) · t) g = coefficientTensorMap A t (b⁻¹ * g * a)`.

For a pure tensor this is the inverse in the dual action together with
multiplicativity of `A.representation`; tensor induction extends the
formula. This explicitly fixes the order and inverse of the two
translation coordinates.

`coefficientTensorMap_biInvariant` proves that for every tensor `t` there
exists one open subgroup `K` such that

`coefficientTensorMap A t (k * g * l) = coefficientTensorMap A t g`

for every `k,l : K` and `g : G`. The pure-tensor case uses the imported
smooth matrix-coefficient theorem. The addition step intersects the two
open subgroups. No compactness of `K` is claimed.

## Transport along a specified representation equivalence

For `e : A.representation.Equiv B.representation`,
`coefficientTensorCongr e` is a linear equivalence of coefficient tensors:
it uses `e.toLinearEquiv` on vectors and the existing
`smoothContragredientEquiv e.symm` on smooth functionals.
`coefficientTensorCongr_tmul` gives its formula

`v ⊗ ℓ ↦ e v ⊗ (ℓ ∘ e⁻¹)`.

The functional in this formula is the actual
`contragredientMap e.symm.toIntertwiningMap ℓ`, with smoothness supplied
by the existing dual construction.

`coefficientTensorMap_congr` proves equality of the resulting locally
constant coefficient functions. On pure tensors, equivariance of `e`
and `e⁻¹(e v)=v` give the equality; tensor induction extends it.
`coefficientTensorCongr_action` proves that this transport intertwines
the actual `G × G` actions, using equivariance on both tensor factors.

`coefficientTensorCongr_refl` proves identity transport.
`coefficientTensorCongr_trans` proves that transport by `e.trans f` is
successive transport by `e` and `f`. Both laws reduce to definitional
identities on pure tensors and then use tensor induction.

These constructions do not assert a scalar smooth-family space over a
twist orbit, a compact-picture comparison, a stabilizer quotient, the
Schwartz property of coefficients, or any wave-packet or Plancherel
conclusion. Those remain downstream obligations of the source program.

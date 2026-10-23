# Associative multiplication on a chosen dual scheme

This derived module transfers the proved associativity of geometric Picard-zero
tensor classes to the actual multiplication morphism on a chosen dual parameter
scheme. It also packages multiplication on every set of points as a semigroup.
Worker 144 supplies the construction and proofs.

## Provenance and hypotheses

Edixhoven–van der Geer–Moonen, *Abelian Varieties*, preliminary draft, Chapter VI,
paragraph (6.2), printed p.88 (PDF p.92), defines tensor of rigidified classes and
classification by a universal rigidified Poincare family. The source is
`edixhoven-vandergeer-moonen-abelian-varieties-draft`, SHA256
`81e88e484e1e830286ffed93d4636c80e50a1c341ffe19cc198bd856be713b42`.
The result here is a categorical consequence of that classification property,
using the Library's constructed tensor and its separately proved conditional
associativity. It does not assert a new representability theorem.

For an abelian scheme `A` over `S`, the inputs are:

- `hA : HasDualScheme A`, existence of an actual universal Picard-zero family;
- `PicardZeroPullbackStatement`, preservation of the geometric condition by
  parameter pullback, needed for `dualPointClass`;
- `pullbackTensorComparisonIsIsoStatement`, invertibility of the fixed pullback
  tensor comparison;
- `PullbackTensorCompositionStatement` and
  `PullbackTensorLeftUnitorStatement`, the fixed composition and left-unit
  equations used by the multiplication formula on points;
- `ExplicitPullbackTensorAssociativityStatement` and
  `TensorMonoidalLeftUnitorComparisonStatement`, the fixed-map hypotheses used
  by the rigidified associator and its class law.

All these assumptions remain explicit. The multiplication is the existing
`dualTensor`, defined by classifying tensor of the two universal pullback
classes, and the chosen parameter scheme is the existing `dualScheme A hA`.

## Point and scheme equations

Write `D = dualScheme A hA`, write `mu` for `dualTensor`, and let `T` be any
scheme over `S`. For `f,g,h : T -> D`, `dualTensor_points_assoc` proves

`mu(mu(f,g),h) = mu(f,mu(g,h))`,

where `mu(f,g)` means `prod.lift f g` followed by the actual morphism `mu`.
The proof applies injectivity of `dualPointClass`, rewrites the four
multiplication occurrences using `dualTensor_points`, and applies
`picardZeroClassesTensor_assoc` to the three actual classified classes.
Thus the law is derived from the tensor associator, not assumed for the scheme
multiplication.

`dualTensor_assoc` gives the corresponding equality of morphisms
`(D product D) product D -> D` in `Over S`. If `p12` and `p3` are the outer
projections and `p1,p2` are the projections from `D product D`, its left side
pairs `p12;mu` with `p3` and then applies `mu`; its right side pairs `p12;p1`
with `mu(p12;p2,p3)` and then applies `mu`. The proof specializes the point
law to these three projections and simplifies the product universal property.
Products here are categorical products in `Over S`, hence fibre products over
`S`.

## Semigroup of points

`dualPointSemigroup ... T` is a `Semigroup (T -> D)`, with multiplication exactly
`(f,g) |-> prod.lift f g;mu` and associativity supplied by
`dualTensor_points_assoc`. It is an explicit definition with the standard
instance reducibility annotation, so consumers can install the chosen
structure locally. No global competing instance is installed.

This module asserts associative multiplication. It does not construct tensor
inverses, a group structure, an abelian-scheme structure on `D`, or existence of
`D` without `HasDualScheme A`.

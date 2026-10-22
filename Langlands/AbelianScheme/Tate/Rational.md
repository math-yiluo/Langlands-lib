# Rational full and prime-to-p Tate modules

This module rationalizes the actual torsion-point inverse limits from
`Langlands.AbelianScheme.Tate.Integral`. It specializes the construction to the
bundled abelian schemes of `Langlands.AbelianScheme.Basic`, extends their maps to
rational homomorphisms, and constructs the rational endomorphism-algebra action.
It uses the published `Langlands.CategoryTheory.RationalizationLift` extension
of additive functors.

## Inputs and definitions

For a scheme `S`, a commutative group object `G` in `Over S`, a test scheme
`T : Over S`, and a predicate `P : ℕ → Prop`, `GroupScheme.Tate.Rational G T P`
is `ℚ ⊗[ℤ] Integral G T P`. The integral module is the compatible family of
actual torsion sections indexed by positive integers satisfying `P`; it is not
a family of supplied abstract modules. The inherited `fibreLevelEquiv` identifies
these sections at a point with points of the actual fibre of the kernel of
multiplication by the relevant integer.

The rational factor is placed first to use Mathlib's scalar-extension module
structure. `rationalTensorComm` explicitly identifies this tensor product with
`Integral G T P ⊗[ℤ] ℚ`, the order used in Harris–Taylor. The comparison is
integer-linear, and its pure-tensor formula is proved. `toRational` sends an
integral family `x` to `1 ⊗ x`; injectivity is not asserted.

`RationalFull` takes `P` to be true, and `RationalAway p` takes it to be
coprimality with `p`. The latter definition makes sense for every natural
number `p`; the prime-to-a-prime application uses prime `p`. The `At` variants
use `T = Over.mk s` for a field-valued point `s`. For a geometric point one
chooses an algebraically closed field. The definitions themselves do not need
algebraic closure, characteristic zero, or finite étaleness.

The names in `Langlands.AbelianScheme.Tate` specialize these constructions
through `A.toGrp` for an actual bundled abelian scheme `A`. These are aliases
of the group-scheme constructions, not a new assumed Tate-module interface.

## Maps and rational homomorphisms

`GroupScheme.Tate.rationalMap` is scalar extension of the integral Tate map.
On pure tensors it sends `q ⊗ x` to `q ⊗ map(f)(x)`. Its identity,
composition, and addition laws follow by tensor extensionality from the
corresponding integral laws. In the category of group objects, pointwise
multiplication of homomorphisms is the operation giving addition of Tate maps,
so the general addition lemma is named `rationalMap_mul`. The bundled
abelian-scheme version is named `rationalMap_add`, using the actual preadditive
structure on abelian schemes. `rationalMap_toRational` proves compatibility
with the canonical map from the integral limit.

`rationalRestrictAway` is the scalar extension of restriction of compatible
families to coprime levels. Its pure-tensor formula is proved. No inverse to
this restriction is claimed.

`rationalFunctor T P` packages the bundled construction as an additive functor
to `ModuleCat ℚ`. `rationalizedFunctor` applies the published
`Rationalization.lift`. The linear map `rationalHomMap` exposes its map on
`Rationalization.Hom A B = ℚ ⊗[ℤ] (A ⟶ B)` as an ordinary rational-linear map
between Tate modules. In particular,

\[
\operatorname{rationalHomMap}(q\otimes f)=q\,\operatorname{rationalMap}(f).
\]

Its rational linearity is part of the definition's type. The unit and
composition laws are proved; composition sends `f` followed by `g` to the
linear map for `g` composed with the linear map for `f`.

`rationalEndAction` is the rational-algebra homomorphism from
`Rationalization.End A` to `Module.End ℚ (Rational A T P)`. It is obtained from
`Rationalization.liftEnd` by projecting a `ModuleCat` endomorphism to its
linear map, preserving the usual composition multiplication. Its value on an
integral endomorphism is the integral-homomorphism-induced rational Tate map.
`algebraAction i` composes this with any rational-algebra homomorphism
`i : D →ₐ[ℚ] Rationalization.End A`. Thus it gives an actual rational-linear
representation of `D`, without an assumption of faithfulness.

`rationalIso` sends an isomorphism in the rationalized abelian-scheme category
to a rational-linear equivalence of Tate modules by mapping its two inverse
morphisms. Its formula, identity law, and composition law are proved. This is
the algebraic transport attached to an invertible rational homomorphism; no
geometric characterization of such morphisms is assumed.

## Provenance and scope

The source convention is Harris–Taylor, *The Geometry and Cohomology of Some
Simple Shimura Varieties* (2001), Chapter I, printed p.18 (PDF p.26), registered
as `harris-taylor-2001-geometry-cohomology-simple-shimura`, SHA-256
`5be28164b61d6f6cc28dd9e6b990d669504f3470860b230ebbc97e3da10af56b`.
That page defines the full and away-from-a-set rational Tate modules by
rationalizing the integral limits, defines rational endomorphisms, and uses
invertible rational homomorphisms as isogenies. The predicate-indexed,
test-scheme-level construction and categorical extension are derived
implementations of these conventions. The intrinsic proofs use scalar
extension and the tensor universal property, not an unproved geometric
comparison.

This module establishes no finite-adelic scalar action or restricted-product
comparison. It never tensors the integral Tate module over the integers with
the finite adeles. A profinite-integer action, identification of its rational
scalar extension with `Langlands.Global.FiniteAdeles ℚ`, and the corresponding
adelic and prime-to-p algebra actions remain separate obligations. It asserts
no finite-dimensionality, rank, rational topology, monodromy, pairing,
pointed base-change theorem, or unpointed canonical transport. These require
the geometric hypotheses and constructions specified by the parent task.

# Ordinary line-bundle inverses and Picard representatives

This module uses the published full equivalence
`locallyFreeRankOneIffTensorInvertible X` to connect actual locally free
rank-one module sheaves with the tensor-invertible sheaves and scheme
Picard group in `Picard.Basic`. All constructions apply to an arbitrary
`X : Scheme.{u}` without additional hypotheses.

`InvertibleSheaf.toLineBundle` equips the same underlying module sheaf
with the local rank-one property proved by the forward implication.
`LineBundle.toInvertibleSheaf` equips the same underlying module sheaf
with the tensor-inverse property proved by the reverse implication.
Neither changes the module object.

`LineBundle.inverse L` converts `L` to an invertible sheaf, takes the
chosen inverse from `InvertibleSheaf.inverse`, and converts that inverse
back to a line bundle using the same proved equivalence. Thus the output
is an actual locally free rank-one sheaf, with no supplied inverse or
evaluation premise. It is a choice of tensor inverse and is not asserted
to be definitionally the internal-Hom dual.

`LineBundle.tensorInverseIso L` has exactly the type

```text
Langlands.Scheme.Modules.tensorObj L.obj L.inverse.obj ≅
  SheafOfModules.unit X.ringCatSheaf.
```

It first uses the inverse of `localizedTensorIso` to pass from the explicit
sheafification of sectionwise tensor to the monoidal tensor, then uses
the chosen inverse's evaluation isomorphism from `Picard.Basic`. The
target monoidal unit is definitionally the displayed structure module.
These are ordinary line-bundle data; rigidification of a supplied inverse
and evaluation belongs to the separate `RigidifiedInverse` interface.

`LineBundle.classOf` sends a line bundle to the class of its underlying
tensor-invertible sheaf in `Group X`. `classOf_eq_iff` characterizes
equality by an isomorphism of underlying module sheaves.
`classOf_eq_iff_iso` gives the equivalent condition of an isomorphism in
the full subcategory `LineBundle X`, by lifting the module isomorphism
or forgetting the line-bundle isomorphism.

`classOf_trivial`, `classOf_tensor` and `classOf_inverse` identify the
trivial bundle, tensor product and chosen inverse with zero, addition
and negation. For tensor product the existing
`LineBundle.tensor preservation` API takes the proved-comparison
proposition as an explicit argument. The class lemma accepts that same
argument and uses `localizedTensorIso` followed by `Basic.classOf_tensor`.
The unconditional theorem
`Langlands.Scheme.Modules.pullbackTensorComparisonIsIso`, already imported
through `Basic`, supplies the argument whenever needed; this module does
not assume the comparison globally. The other class laws are the
corresponding `Basic` laws on the same underlying objects.

`Group.lineBundleRepresentative X x` converts the chosen invertible-sheaf
representative to a locally free rank-one sheaf.
`classOf_lineBundleRepresentative` proves that its class is exactly `x`.
Together with `classOf_eq_iff_iso`, this identifies every group element
with an isomorphism class of actual line bundles.
`Group.pullback_lineBundle_classOf f L` proves that the Picard homomorphism
sends the class of `L` to the class of the published actual
`LineBundle.pullback f`. It is `Basic.pullback_classOf` on the same
underlying module objects. The identity and composition laws of that
homomorphism and the contravariant functor are in `Picard.Functor`.

The group and both kinds of representatives lie in `Type (u+1)`, retaining
the universe of actual module sheaves. No smaller quotient or relative
Picard representability is claimed.

Worker 148 authored this internal packaging of the published comparison,
inverse, quotient and tensor-comparison APIs. Its geometric interpretation
is Stacks Definition 17.14.1(3), Lemma 17.25.4 and Definition 17.25.9, with
inverse existence as in the first equivalence of Lemma 17.25.2. The original
source is the registered retained snapshot
`stacks-local-freeness-invertibility-sections-2026-10-21`, SHA-256
`6d1641a9deb284be889ee6e2630a2be6e57cc5985c80af2c9da7d17543ed0785`,
files `01C5.html` and `01CR.html`. The full comparison proof is reused by
Lean name; this module repeats neither directional geometric proof.

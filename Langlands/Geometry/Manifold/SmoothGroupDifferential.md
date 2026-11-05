# Real tangent differentiation of complex functions on a smooth group

This is an internal construction from Mathlib's manifold derivative, tangent
bundle and smooth group law. Fix a real normed vector space `E`, a model with
corners `I : ModelWithCorners ℝ E H`, a topological group carrier `G` with
`ChartedSpace H G`, and `LieGroup I ∞ G`. No finite dimension or number-field
hypothesis is required. All derivatives below use the specified real atlas.

For an actual identity tangent vector `X : GroupLieAlgebra I G`, an arbitrary
function `f : G → ℂ`, and `g : G`, `groupDirectionalValue I X f g` is

```
mvfderiv I (fun h => f (g * h)) 1 X.
```

Here `GroupLieAlgebra I G` is Mathlib's tangent space at the identity, and
`mvfderiv` identifies the target tangent space of the complex normed vector
space with `ℂ`. Thus the definition differentiates the original positive right
orbit `h ↦ f(g*h)` at the identity in the real direction `X`. It uses no
supplied family of endomorphisms. Like the underlying manifold derivative,
this is a total definition even for a nonsmooth function.

`contMDiff_groupDirectionalValue` proves that if `f` is real `C∞`, the resulting
function of `g` is real `C∞`. The implemented proof applies the smooth tangent
map of `(g,h) ↦ f(g*h)` to the smooth tangent family `(g,1;0,X)`, using the
canonical identification of the tangent bundle of a product with the product
of the tangent bundles. Projection to the complex tangent coordinate is
smooth. The derivative-of-a-product-domain formula cancels the zero first
direction and identifies this composite with the displayed definition.

`groupDirectionalValue_eq_invariant`, under the same smoothness assumption,
identifies the value with `mvfderiv I f g (mulInvariantVectorField X g)`.
The chain rule and `g*1=g` give this formula; the vector field is the actual
derivative of left multiplication by `g` applied to `X`.

The remaining laws describe this same definition:

- `groupDirectionalValue_add_direction` and
  `groupDirectionalValue_smul_direction` prove additivity and real scalar
  linearity in `X` for every function. These follow from linearity of the
  totalized derivative as a map on the identity tangent space.
- `groupDirectionalValue_add` proves additivity in two smooth functions.
  `groupDirectionalValue_const_smul` proves complex scalar linearity in a
  smooth function, even though the tangent scalar field is real. The proofs
  use the derivative sum rule and the chain rule with the real continuous
  linear map given by multiplication by the fixed complex scalar.
- `groupDirectionalValue_leftTranslation` states
  `D_X (fun x => f(a*x)) g = D_X f (a*g)`. It holds for every function by
  associativity of the original group multiplication, so it needs no
  smoothness premise.

The linearity and left-translation identities that do not use the smooth
group law omit that instance from their Lean hypotheses. This unit constructs
one directional derivative and proves its intrinsic laws. Bundling it on the
existing adelic smooth-function spaces, compatibility with the original
matrix differential, the Lie bracket and enveloping algebra action,
exponential-curve comparison, growth conditions, measures and cuspidal
realizations remain separate obligations.

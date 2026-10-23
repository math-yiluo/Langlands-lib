# Real-place splitting of a finite-dimensional algebra

For a totally real number field `E` and an `E`-algebra `A` with a supplied finite
basis, this module constructs

\[
\mathbb R\otimes_{\mathbb Q}A
\;\simeq_{\mathbb R}\;
\prod_{\tau:E\to\mathbb R}(\mathbb R\otimes_{E,\tau}A).
\]

Its component at `τ` sends `r ⊗ a` to `r ⊗ a`, where the source tensor is over
the rationals and the target tensor is over `E` through `τ`. The algebra `A`
may be noncommutative.

## Hypotheses, provenance and scope

The hypotheses are `Field E`, `NumberField E`, `IsTotallyReal E`, `Ring A`,
`Algebra E A`, `Algebra ℚ A`, and `IsScalarTower ℚ E A`. For bijectivity and the
algebra equivalence, `b : Basis ι E A` is supplied with `Fintype ι`. The field,
algebra and basis index may have different universes. No map from `E` to the
reals is selected globally: every factor uses its indexing embedding `τ`.

This is an internal construction. It imports the real field tensor equivalence
`Langlands.Global.TotallyReal.tensorEquiv` from
`Langlands.Global.RealTensorSplitting` and Mathlib's basis, finite-product and
scalar-extension linear equivalences. It proves the assembly map is bijective
by comparing actual coordinates. No new external theorem is invoked, and the
assembly equivalence is not an input.

This module supplies the algebraic assembly prerequisite for the existing
Harris real-place charts. It does not yet compose those charts, compare their
involutions, or construct a Deligne homomorphism or Shimura scheme.

## Actual scalar extensions and evaluation

Within `Langlands.Global.TotallyReal`, `At E A τ` abbreviates the actual tensor
algebra `ℝ ⊗[E] A`, using `τ.toAlgebra` for the scalar action on `ℝ`.
`atInclusion E A τ` is the canonical inclusion of `A` into this tensor algebra,
restricted from an `E`-algebra homomorphism to a rational algebra homomorphism.
The scalar-tower hypotheses ensure this restriction uses the given rational
structure on `A`.

`algebraEvaluation E A` first takes the product of these inclusions and then
extends scalars from the rationals to the reals through `AlgHom.liftEquiv`.
It is a real algebra homomorphism to the actual product of real-place tensor
algebras. `algebraEvaluation_tmul` proves the component formula above. These
constructions and their formula do not require total reality or the finite
basis; those hypotheses enter the proof of bijectivity.

## Coordinate proof of bijectivity

The private `algebraCoordinates` equivalence is the composite

\[
\begin{aligned}
\mathbb R\otimes_{\mathbb Q}A
&\simeq \mathbb R\otimes_{\mathbb Q}(\iota\to E)\\
&\simeq (\iota\to\mathbb R\otimes_{\mathbb Q}E)\\
&\simeq (\iota\to(\tau:E\to\mathbb R)\to\mathbb R)\\
&\simeq ((\tau:E\to\mathbb R)\to\iota\to\mathbb R).
\end{aligned}
\]

The first step uses the basis coordinate equivalence, restricted to rational
scalars and extended to the reals. The second uses
`TensorProduct.piRight` for a finite index type. The third applies the actual
field tensor splitting in each basis coordinate, and the last exchanges the
two function indices. Each step is a real linear equivalence.
`algebraCoordinates_tmul` proves that the final coordinate at `(τ,i)` of
`r ⊗ a` is `r * τ (b.repr a i)`.

On the target, private `localCoordinates` takes the product of the coordinate
equivalences for the bases `b.baseChange ℝ`, with the real scalar action chosen
separately at each `τ`. Private `localCoordinates_evaluation` proves that these
local coordinates after `algebraEvaluation` equal `algebraCoordinates`.
Tensor induction reduces the equality to the displayed pure-tensor coordinate
formula, with the two real scalar factors commuting.

`algebraEvaluation_bijective` therefore identifies the evaluation linear map
with `algebraCoordinates` followed by the inverse of `localCoordinates`.
This composite of actual linear equivalences proves bijectivity.

## The algebra equivalence

`algebraEquiv E A b` applies `AlgEquiv.ofBijective` to the actual evaluation
homomorphism and the preceding proof. The resulting object includes its
noncomputable inverse and both inverse identities.
`algebraEquiv_tmul` proves its exact component formula.

The basis is an auxiliary device for proving bijectivity.
`algebraEquiv_basis_independent` proves equality of the algebra equivalences
constructed from any two finite bases, including bases with different index
types. Their forward maps are definitionally the same evaluation map, so
extensionality of algebra equivalences proves the equality.

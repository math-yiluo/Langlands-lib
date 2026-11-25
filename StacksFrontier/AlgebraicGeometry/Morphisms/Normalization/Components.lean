module

public import StacksFrontier.AlgebraicGeometry.Limits.ReducedInducedSubscheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Stability
public import StacksFrontier.AlgebraicGeometry.Morphisms.Normalization.IntegralBirational
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import StacksFrontier.AlgebraicGeometry.NormalizationBirational.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.ReducedClosedSubscheme
public import Mathlib.Tactic.CrossRefAttribute

set_option autoImplicit false
set_option maxSynthPendingDepth 3

/-!
# Normalization of the irreducible components

Let `X` be a scheme whose quasi-compact opens have finitely many irreducible components. Each
irreducible component of `X`, with its reduced induced closed subscheme structure, is an integral
scheme and so has a normalization, and the coproduct of those normalizations, with its canonical
morphism to `X`, is the normalization of `X`.

## Main definitions

* `AlgebraicGeometry.Scheme.reducedComponent` is an irreducible component of `X` with its reduced
  induced closed subscheme structure, and `AlgebraicGeometry.Scheme.reducedComponentι` is its
  closed immersion into `X`.
* `AlgebraicGeometry.Scheme.reducedComponentToReduction` factors that closed immersion through
  the reduction of `X`, and `AlgebraicGeometry.Scheme.reducedComponentsToReduction` assembles
  those factors into a morphism from the coproduct of the components.
* `AlgebraicGeometry.Scheme.sigmaNormalizationReducedComponent` is the coproduct of the
  normalizations of the reduced irreducible components, and
  `AlgebraicGeometry.Scheme.sigmaNormalizationToReduction` is its canonical morphism to the
  reduction of `X`.

## Main results

* `AlgebraicGeometry.Scheme.exists_iso_normalizationScheme_sigma_reducedComponent` is Tag 0CDV:
  the coproduct of the normalizations of the reduced irreducible components, with its canonical
  morphism to `X`, is the normalization of `X`.
* `AlgebraicGeometry.Scheme.exists_iso_sigma_isIntegral_isNormal_normalizationScheme` is part (1)
  of Tag 035Q: the normalization of `X` is a disjoint union of integral normal schemes.
* `AlgebraicGeometry.Scheme.isIntegral_reducedComponent`: a reduced irreducible component is an
  integral scheme, so it has a normalization.
* `AlgebraicGeometry.Scheme.isGenericPoint_reducedComponentι`: the generic point of a reduced
  irreducible component is the generic point of that component of `X`.
* `AlgebraicGeometry.Scheme.finite_setOf_irreducibleComponents_inter_nonempty`: only finitely
  many irreducible components of `X` meet an open set with finitely many irreducible components.
* `AlgebraicGeometry.Scheme.isBirational_reducedComponentsToReduction`: the coproduct of the
  reduced irreducible components is birational over the reduction of `X`.
* `AlgebraicGeometry.Scheme.exists_iso_normalizationScheme_of_isIntegralHom_of_isBirational`: an
  integral morphism onto `X` from a normal scheme which is birational over every quasi-compact
  open *is* the normalization of `X`.

## Implementation notes

`AlgebraicGeometry.Scheme.reducedComponent` is the *reduced* induced structure on an irreducible
component, cut out by the vanishing ideal sheaf of the component. It is not Mathlib's
`AlgebraicGeometry.Scheme.irreducibleComponent`, which carries a different, generally non-reduced,
closed subscheme structure and is defined only for a locally Noetherian scheme.

The source reduces to the case of a reduced `X` and then invokes Tag 035Q part (3). The reduction
is unavoidable: the morphism from the coproduct of the components is birational only over the
reduction, since the local ring of a non-reduced `X` at a generic point is not a field. So the
whole argument is carried out over `X.nilradical.subscheme` and transported along the
isomorphism of Tag 035O at the end.

Part (3) of Tag 035Q is applied not to the coproduct of the components but to the coproduct of
their *normalizations*. That source is already normal, so Tag 0H7D makes its own normalization
morphism an isomorphism, which is what identifies it with the normalization of `X`. Applying
part (3) to the coproduct of the components instead would leave the separate task of showing
that normalization commutes with coproducts, and that is not formal: the pushforward along an
infinite disjoint union is a product rather than a sum, so it would need the same local
finiteness bookkeeping all over again.

Integrality of the morphism from the coproduct is `AlgebraicGeometry.isIntegralHom_sigmaDesc`,
whose local-finiteness hypothesis is supplied by
`AlgebraicGeometry.Scheme.finite_setOf_irreducibleComponents_inter_nonempty`.

## References

* [Stacks Project, Tag 0CDV](https://stacks.math.columbia.edu/tag/0CDV)
* [Stacks Project, Tag 035O](https://stacks.math.columbia.edu/tag/035O)
* [Stacks Project, Tag 035Q](https://stacks.math.columbia.edu/tag/035Q)
* [Stacks Project, Tag 0H7D](https://stacks.math.columbia.edu/tag/0H7D)
-/
@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

variable (X : Scheme.{u})

/-! ### The reduced irreducible components -/

/-! ### Factoring through the reduction -/

/-! ### Local finiteness of the family of irreducible components -/

/-! ### The coproduct of the reduced irreducible components -/

/-! ### An integral birational morphism from a normal scheme is the normalization -/

/-! ### The coproduct of the normalizations of the components -/

/-- The normalization morphism of a scheme is integral: it is the structural morphism from a
relative normalization. -/
theorem isIntegralHom_normalization
    (hX : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite) :
    IsIntegralHom (X.stacksNormalization hX) := by
  have := quasiCompactFromGenericPointResidueFields X hX
  have := quasiSeparatedFromGenericPointResidueFields X
  exact inferInstanceAs
    (IsIntegralHom (fromGenericPointResidueFields X).fromNormalization)

end AlgebraicGeometry.Scheme

end

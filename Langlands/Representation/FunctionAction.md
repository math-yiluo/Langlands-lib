# Inverse pullback on stable function spaces and paired carriers

Authors: Worker 1149 and Worker 6. Worker 1149 implemented this unit;
Worker 6 supplied the source/API audit and the restriction-and-transport
construction outline in the task context. The published function representation
is reused by import; its author is not a coauthor of this unit.

This unit implements the opening two paragraphs of David Renard,
*Représentations des groupes réductifs p-adiques*, French version dated
9 July 2026, II.3.1, printed p.43 / one-based PDF p.49. The registered original
is `renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
Worker 1149 read the complete II.3.1 passage and visually checked that page.
No Renard-specific errata file was found in the workspace, project or current
Library `notes/errata` locations.

The source gives inverse pullback on a space of functions and the induced
contragredient formula on a paired space. Its conventional wording presupposes
that these operations preserve the spaces involved. The explicit stability
and separation hypotheses below specify precisely the data used here. They
are a formalization of that convention, not an assertion that every function
subspace or every pairing admits the action.

## Carriers and hypotheses

All declarations are in `Langlands.FunctionAction`. The group `G : Type uG`,
the acted-on set `X : Type uX`, and the paired carrier `D : Type uD` have
independent universes. Coefficients are explicitly complex numbers. `G` is
an arbitrary group with a `MulAction G X`; `D` is an arbitrary complex vector
space. No nonemptiness, finite dimension, topology, smoothness, compactness,
countability or reflexivity assumption occurs.

For any complex representation `ρ` and actual submodule `E`, `IsStable ρ E`
is the proposition `∀ g, E ≤ E.comap (ρ g)`: applying every group element
preserves membership in that submodule.

The function carrier is an actual `E : Submodule ℂ (X → ℂ)`, with its actual
subtype inclusion `E.subtype`. The pairing is an actual complex-linear map
`j : D →ₗ[ℂ] Module.Dual ℂ E`. The value of the pairing at `T, f` is `j T f`.
The input `Function.Injective j` says that pairing against all `f : E`
distinguishes elements of `D`. The other input is stability of the actual
submodule `j.range` under the full dual representation. No separation in the
`E` variable, surjectivity onto the full dual, perfect pairing, or preexisting
representation on `D` is assumed.

## Function and dual actions

`functionRepresentation G X` transparently aliases the published
`Langlands.Induction.functionRepresentation (Representation.trivial ℂ G ℂ) X`
from `Langlands.Representation.Induction.PermutationDual`.
`functionRepresentation_apply` gives

```text
(functionRepresentation G X g f) x = f (g⁻¹ • x).
```

Given `hE : IsStable (functionRepresentation G X) E`,
`stableFunctionRepresentation E hE` is Mathlib's actual
`Representation.subrepresentation` on `E`.
`stableFunctionRepresentation_apply` gives the same pointwise formula on
subtype elements. `stableFunctionRepresentation_subtype` proves equality
of the two linear composites expressing equivariance of `E.subtype`.

`dualRepresentation E hE` transparently aliases
`(stableFunctionRepresentation E hE).dual`, Mathlib's `Representation.dual`
on the full algebraic dual `Module.Dual ℂ E`.
`dualRepresentation_apply` is the formula

```text
(dualRepresentation E hE g T) f = T (stableFunctionRepresentation E hE g⁻¹ f).
```

These evaluation laws follow by unfolding the reused constructions. The
subtype-inclusion law follows by extensionality and the same definitions.

## Paired carrier and uniqueness

`pairedRepresentation E hE j hinj hRange` first restricts
`dualRepresentation E hE` to `j.range` using `hRange` and
`Representation.subrepresentation`. It then takes
`e := LinearEquiv.ofInjective j hinj : D ≃ₗ[ℂ] j.range` and composes the
restricted representation with `e.symm.conjRingEquiv.toMonoidHom`. Thus the
operator on `D` is the conjugate `e.symm ∘ ρrange(g) ∘ e`. The group and linear
laws are inherited from restriction and the endomorphism-ring equivalence.

`pairedRepresentation_intertwines` proves
`j (pairedRepresentation ... g T) = dualRepresentation E hE g (j T)` using
`LinearEquiv.ofInjective_symm_apply` and the definition of restriction.
Evaluating this equality proves `pairedRepresentation_pairing`:

```text
j (pairedRepresentation E hE j hinj hRange g T) f
  = j T (stableFunctionRepresentation E hE g⁻¹ f).
```

`pairedRepresentation_unique` says that any representation `σ` on this same
actual carrier `D` satisfying this formula is equal to the constructed one.
Its proof compares the operators at every `g, T`, applies injectivity of `j`,
and compares the resulting linear functionals at every `f : E`. No action on
`D` is an input to the existence construction; `σ` is quantified only in this
uniqueness theorem.

## Transparent specializations

`fullDualRepresentation E hE` specializes `pairedRepresentation` to the
identity map on `Module.Dual ℂ E`. `fullDualRange_stable` supplies stability
of its full range. `fullDualRepresentation_eq_dual` identifies this
construction with `dualRepresentation E hE`, by the uniqueness theorem and
the dual evaluation formula. `fullDualRepresentation_apply` gives that
formula directly for the specialization.

For an actual invariant `F : Submodule ℂ (Module.Dual ℂ E)`,
`dualSubmoduleRepresentation E hE F hF` specializes the same construction to
`F.subtype`. Its injectivity is the actual subtype-injectivity theorem, and
`dualSubmoduleRange_stable` uses `Submodule.range_subtype` to identify the
range with `F`. `dualSubmoduleRepresentation_eq_subrepresentation` identifies
it with direct restriction of the full dual action, again by uniqueness.
`dualSubmoduleRepresentation_apply` gives the source pairing formula on
this subtype.

The specializations and their compatibility equalities are intrinsic laws of
the construction. They are derived directly from the source formulas and the
stated stability and injectivity data; no stronger source theorem is claimed.

## Scope

This unit covers only those two opening conventions. The subsequent
left/right translations, automorphism and inner-automorphism actions,
inversion, actual test-function and distribution specializations, II.3.2,
Haar measure, convolution and sheaf constructions remain separate obligations.

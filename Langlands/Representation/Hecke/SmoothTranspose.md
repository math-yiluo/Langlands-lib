# The integrated transpose on the smooth dual

This is a derived construction using the published actual integrated Hecke
action and smooth contragredient. Let `G` be a topological group with its Borel
measurable structure, `μ` a measure finite on compact sets and invariant under
inversion, and `ρ` a smooth complex representation on an arbitrary algebraic
vector space `V`. The group and carrier universes are independent. No topology
or finite-dimensionality on `V`, admissibility, or irreducibility is assumed.
The measure need not be a Haar measure or normalized.

Write `π(f)` for `integratedAction μ ρ hρ f`, and write `fˇ(g) = f(g⁻¹)` for
the published `TestFunction.inversion`. The construction
`integratedTranspose μ ρ hρ` is complex linear in `f` and sends it to the
endomorphism of the actual `SmoothDual ρ` given by

`(integratedTranspose f ℓ)(v) = ℓ(π(f)v)`.

It is defined by restricting the algebraic transpose `π(f).dualMap`, using the
existing inclusion `smoothDualPairing ρ`. Its output has the same underlying
functional, with a proved smoothness witness. The factorization identity
`smoothDualPairing_comp_integratedTranspose` records this restriction exactly.

The implemented proof starts with `integratedAction_smoothDualPairing`:

`⟨π∨(f)ℓ, v⟩ = ⟨ℓ, π(fˇ)v⟩`.

Apply `integratedAction_dual` to evaluation at `v` on the smooth dual, and to
`ℓ` on the original carrier. The published smooth-dual action evaluates as
`ℓ(ρ(g⁻¹)v)`. Mathlib's `integral_inv_eq_self` changes variables in the scalar
integral, using the explicit inversion-invariance hypothesis on `μ`.
No continuity of either algebraic evaluation functional is required.

Applying this identity to `fˇ` proves that `π(f).dualMap ℓ` is the underlying
functional of `π∨(fˇ)ℓ`, hence is smooth. This supplies the codomain restriction
in the definition. Linearity follows from linearity of the original integrated
action and of `ℓ`. The evaluation and inclusion identities are definitional.
Finally, `integratedTranspose_eq_integratedAction_inversion` identifies this
restricted transpose with the actual integrated smooth-contragredient operator
on `fˇ`.

The provenance is internal: the construction and laws are derived from
`Hecke.IntegratedAction`, `Smooth.Contragredient.LawsProof`, and Mathlib's
measure-preserving inversion formula. This unit does not prove inversion
invariance for a particular Haar measure, any equality of traces or distribution
characters, or the Gelfand–Kazhdan equivalence. Those remain separate
obligations in the parent generic-contragredient proof.

# Hermitian transport of coefficient tensors

This derived construction supplies representative transport for the Hermitian
coefficient tensors in Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)* (2003), V.1, printed p.288 / PDF p.54,
V.2, printed p.293 / PDF p.59, and the representative-independence paragraph
of VI.1, printed p.295 / PDF p.61. The source is registered as
`waldspurger-2003-plancherel`. This module isolates a general algebraic
comparison needed by those constructions; it does not construct the spectral
families or prove the main Plancherel formula.

The group is an arbitrary topological group. Its universe and the two carrier
universes are independent. The Hermitian results use complex representations,
admissibility of both representations and cofinal compact open subgroups.
The carriers have no chosen topology or completion. Irreducibility is not
required.

For an equivariant linear equivalence `e : ρ.Equiv σ` and a positive invariant
form `b` on `σ`, the pullback `b.ofEquiv e` evaluates as
`b(e(v), e(w))`. The forward map on smooth duals is inverse pullback:
`smoothContragredientEquiv e.symm` sends `ℓ` to `ℓ ∘ e⁻¹`.
The lemmas `InvariantPositiveForm.smoothDualEquiv_ofEquiv` and
`InvariantPositiveForm.smoothDualEquiv_ofEquiv_symm` prove naturality of the
actual conjugate-linear Hermitian identifications and their inverses.
The first proof evaluates the functionals on a vector and cancels `e ∘ e⁻¹`.
The second applies injectivity of the target Hermitian identification.

`HarishChandraSchwartz.dualInvariantForm_ofEquiv` identifies the whole dual
positive form for the pulled-back original form with the pullback of the
target dual form. The proof evaluates the forms using the inverse Hermitian
identifications and applies their naturality on both arguments. It retains
the reversed argument order in the existing definition of the dual form.

`Plancherel.coefficientTensorCongrEquiv` equips the published linear map
`coefficientTensorCongr e` with its published intertwining law. This
definition works over any commutative ring and is an equivalence for the
actual external product-group actions. It sends a pure tensor to
`e(v) ⊗ (ℓ ∘ e⁻¹)`; the underlying linear map is unchanged.

`Plancherel.coefficientTensorInvariantForm_ofEquiv` proves equality of the
whole Hermitian coefficient form pulled back through that equivalence with
the coefficient form of `b.ofEquiv e`. On pure tensors this is the product
of the original-form pullback identity and the proved dual-form identity.
Double tensor induction and additivity extend it to all tensors in both
arguments.

The published coefficient map already preserves coefficient functions under
this same transport. This module adds the compatible Hermitian comparison.
Independence of the choice of `e` uses separate published Schur arguments
when the inducing representation is irreducible admissible. No such choice
independence, induced irreducibility, formal-degree normalization, or equality
between different Haar normalizations is inferred here.

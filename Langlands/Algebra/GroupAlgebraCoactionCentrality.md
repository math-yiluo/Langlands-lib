# Nilpotent rigidity of central group-algebra coactions

This is an internal algebraic extension of
[`GroupAlgebraCoaction`](GroupAlgebraCoaction.md), using
[`NilpotentModuleReduction`](NilpotentModuleReduction.md). The base ring K,
coalgebra or bialgebra A, and additive character group N have independent
universes. No finiteness, flatness, smoothness, or field hypothesis is imposed.

For a commutative K-bialgebra A and a bialgebra map
π : A → K[N], `leftCoaction π : A →ₐ[K] A[N]` is the algebra map obtained
from `(π ⊗ id) ∘ Δ` by interchanging its tensor factors and applying
`AddMonoidAlgebra.scalarTensorEquiv`. The existing `coaction π` instead
comes from `(id ⊗ π) ∘ Δ`. `leftCoaction_apply` gives this formula.
`coeff_leftCoaction` identifies the coefficient of n with the left
endomorphism `lact (coeffForm π n)`.

The coalgebra lemmas work for an arbitrary K-coalgebra module. `apply_lact`
identifies application of a linear form to a left action with convolution.
`lact_lact` states that composition of left actions reverses convolution
order. Its proof uses the existing left-action compatibility with
comultiplication and expands a finite comultiplication representation.
`ract_lact` and `ract_commute_lact` prove that every right action commutes
with every left action. After the same comultiplication compatibility,
this is naturality of the tensor maps, verified on pure tensors and extended
by tensor induction.

`lact_coeffForm_lact_coeffForm` proves orthogonality of the left character
endomorphisms from their composition formula and `conv_coeffForm`.
`isIdempotentElem_lact_coeffForm` and `isIdempotentElem_proj` supply
idempotence of the left and right character endomorphisms.

`isCentral_iff_leftCoaction_eq_coaction` identifies the existing algebraic
predicate `IsCentral π` with equality of the two algebra maps into A[N].
The forward direction uses the known coefficient identity for central π.
The converse uses injectivity of the scalar tensor equivalence and tensor
interchange. Extensionality of group-algebra coefficients then gives
`isCentral_iff_lact_coeffForm_eq_proj`: centrality holds exactly when each
left character endomorphism equals the corresponding right projection.

Finally, `isCentral_of_coeff_sub_mem` proves algebraic centrality when I
is a nilpotent ideal of K and, for every character n and a ∈ A,

`lact (coeffForm π n) a - proj π n a ∈ I • (⊤ : Submodule K A)`.

For each n these are commuting idempotent endomorphisms. The imported
`NilpotentModuleReduction.eq_of_sub_mem` equates them, and the preceding
coefficient criterion yields centrality.

This module proves an algebraic nilpotent rigidity criterion. It does not
construct a quotient bialgebra or a group-scheme comparison, establish
multiplicative type of a group scheme, or prove the host arbitrary-base
fibrewise central-isogeny statement. In particular, applying the criterion
to scheme-theoretic reduction data still requires the corresponding
coordinate-ring and base-change identifications.

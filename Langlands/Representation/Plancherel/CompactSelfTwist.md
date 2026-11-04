# Actual self-twists on the compact coefficient picture

This module constructs
`Langlands.Plancherel.unramifiedStabilizerCompactRepresentation`.
The actual subgroup of unramified characters fixing the canonical class of an
irreducible admissible smooth representation acts on its fixed compact
coefficient picture. The operator sends vectors through a self-twist
equivalence and pulls smooth functionals back through its inverse. It commutes
with the actual right `K × K` action.

## Source and provenance

The source is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, J. Inst. Math. Jussieu 2 (2003), 235–333,
DOI 10.1017/S1474748003000082, VI.1, printed pp.295–296
(PDF pp.61–62). Its registered identifier is `waldspurger-2003-plancherel`,
SHA256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.

Waldspurger transports product-induced coefficient spaces by an equivalence on
the inducing representation and the inverse transpose on its smooth
contragredient. For a self-twist this defines an automorphism of the compact
picture through the restriction square on p.296. His `GL(2)` example identifies
the operator with `A ⊗ transpose(A⁻¹)` and shows that it can be nontrivial.

The present generic subgroup construction, tensor pairing identity, explicit
product lifts and proofs of the action laws are derived content. They use
the published canonical smooth-dual transport, admissible Schur on the
inducing representation, and actual product compact restriction. No
irreducibility of parabolic induction is used.

## Data and scope

Let `G` be a nonarchimedean group and `M` an actual subgroup. The index type `I`
and the coefficient-carrier universe are independent of the group universe.
The data `ν : I → (M →* ℝ≥0ˣ)` define the existing continuous unramified
characters. Their proved open kernels supply actual canonical `SmoothRep`
twists.

The initial tensor constructions take any smooth complex representation `A`.
Choice independence requires `A.IsAdmissible` and irreducibility of its actual
action. The stabilizer representations use
`π : IrreducibleAdmissibleRep` and precisely
`unramifiedTwistStabilizer ν (Quotient.mk _ π)`, the actual stabilizer of its
canonical `SmoothDualClass`.

For compact sections, retain actual subgroups `P`, `U`, their semidirect
decomposition `h : IsSemidirectDecomposition P M U`, an actual open subgroup
`K`, closedness of `P`, compactness of `K`, continuity of `h.projection`, and
continuity of every `ν i`. These hypotheses prove the required character
triviality on the actual compact intersection. Local compactness, closedness
of `U` and the actual factorization `G = P K` are needed only for the final
restriction-square theorem.

No measure, finite-stabilizer premise, unitarity premise, discrete-series
premise, Hermitian structure or smooth parameter dependence is required.
This unit does not prove finiteness or unitarity of the full stabilizer,
identify rational-character data, realize the actual reductive Iwasawa
factorization, or identify the full-parabolic Haar normalization with the
source's Levi-inflated normalization. The invariant smooth-family description
at the end of VI.1 and the analytic Plancherel theorem remain separate.

## Tensor operator and independence

For an actual equivalence `e : A ≃ Aχ` of the underlying actions,
`selfTwistTensorEquiv` is the composite of `coefficientTensorCongr e` with
`productCompactTwistTensorEquiv ν χ A`. The latter removes the twist on the
actual smooth dual while retaining the underlying linear functional.
Consequently, on a pure tensor its underlying formula is

`v ⊗ ℓ ↦ e(v) ⊗ (ℓ ∘ e⁻¹)`.

`selfTwistTensorEquiv_tmul` gives the formula with the actual smooth-dual
maps; `selfTwistTensorEquiv_dual_apply` identifies the underlying functional
at every vector. The inverse pullback preserves smoothness through the
existing contragredient intertwiner and smooth-dual twist equivalence.
`selfTwistTensorEquiv_pairing` proves preservation of the full bilinear
contraction on every tensor by composing the two imported pairing identities.
There is no conjugation in this pairing.

`selfTwistTensorEquiv_independent` uses
`coefficientTensorCongr_eq_of_admissible`. Admissible Schur on the source
shows that two vector equivalences differ by a scalar; its inverse on the
functional factor cancels that scalar in the tensor.

`selfTwistComposite` explicitly lifts `χη` by first using `eη`, then the
`η`-twist of `eχ`. Commutativity of the characters identifies the resulting
twice-twisted action with `A(χη)`. The underlying vector map is `eχ ∘ eη`.
Tensor induction proves `selfTwistTensorEquiv_composite`: on pure tensors
both vector composition and inverse functional composition are definitional;
the sum case uses linearity. The identity lift and its tensor identity are
proved by the same route.

`stabilizerRepresentationEquiv` chooses an actual self-twist equivalence
from stabilizer membership, using equality of quotient classes and the
canonical smooth-category inclusion. The choices are not assumed to satisfy
a cocycle law. In `unramifiedStabilizerTensorRepresentation`, choice
independence compares the chosen identity lift with the explicit identity,
and the chosen product lift with `selfTwistComposite`. The tensor identities
then prove both representation laws.

## Compact action and restriction square

The carrier is the existing actual
`ProductInducedCompactPicture h K A`, consisting of covariant functions on
`K × K` with values in `CoefficientTensor A` and a common open right
stabilizer for each entire section.

`productCompactSelfTwistEquiv` composes compact representative transport by
`e` with smooth induction of the compact-intersection twist-removal
equivalence. Its evaluation is exactly `selfTwistTensorEquiv χ e` applied
pointwise, as stated in `productCompactSelfTwistEquiv_eval`.
Function extensionality and tensor independence prove
`productCompactSelfTwistEquiv_independent`.

`unramifiedStabilizerCompactRepresentation` uses the actual stabilizer lifts.
Extensionality reduces its identity and multiplication laws to the
corresponding tensor identities at each compact point, again removing the
chosen lifts by admissible Schur. The bundled self-twist equivalences already
intertwine the right compact action, which proves
`unramifiedStabilizerCompactRepresentation_action`. This is a genuine
representation of the full actual stabilizer; no triviality is asserted.

Finally, `productCompactSelfTwistEquiv_restriction` states that transporting an
actual globally induced coefficient function by `e` and restricting its
twist to the fixed picture agrees with first restricting the untwisted
function and applying the compact self-twist operator. Both vertical maps
are the actual normalized restriction equivalences. Equality follows by
evaluating the two actual functions at each compact point. This implements
the square in Waldspurger VI.1, under the displayed generic hypotheses.

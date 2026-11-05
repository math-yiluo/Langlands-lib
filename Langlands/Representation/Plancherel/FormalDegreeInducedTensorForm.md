# Formal-degree normalization of actual induced tensor forms

This module constructs a positive invariant form on the actual tensor
`I_P^G(A) ⊗[ℂ] I_P^G(A.contragredient)` with the inverse of the constructed
Schur formal degree. Its definition takes no chosen inducing form. Its
computation theorem holds for every actual invariant positive inducing form.
The existing compact quotient measures are retained literally; their
comparison with the fixed compact Haar normalization remains separate.

## Source and derived provenance

The source is Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.2, printed p.293 / PDF p.59, the paragraph
before Lemma V.2.2. There the two induced Hermitian forms give the pairing on
`L(ω,P)` by their product multiplied by `d(ω)⁻¹`. The original inducing form
is conjugate-linear in the first argument. The paragraph explains independence
by reciprocal positive rescaling on the inducing representation and its dual.
The positive degree has the crossed coefficient normalization of III.1 (3),
printed p.265 / PDF p.31.

This is a derived assembly of existing actual objects: square-integrable
unitarizability, the constructed Schur degree, the actual compact quotient
induced forms, the actual smooth-dual form, positive tensor products, and
positive-form uniqueness up to scale. The proof establishes arbitrary-form
independence; it does not assume it. In particular, neither a free positive
normalization parameter nor an arbitrary chosen invariant positive inducing
form is an input to `formalDegreeInducedTensorForm`.

The source measure and rational-point identifications are not silently imposed
on this generic construction. Its induced integrals use the existing selected
Bruhat measure, and its formal degree uses the explicitly supplied Haar measure
on the explicitly supplied central quotient of the Levi. The general reductive
source specialization and their fixed normalizations remain obligations.

## Actual data and hypotheses

`G : Type uG` is a locally compact Hausdorff nonarchimedean topological group
with a Borel measurable space. `P`, `M`, `U` are its actual subgroups, with
`h : IsSemidirectDecomposition P M U`. The subgroups `P` and `U` are closed;
`P` is locally compact and `Induction.LeftQuotient P` is compact. The ambient
modular character is trivial, and the modular character of `P` is equal to
`HaarModulus.closedRestrictCharacter U hU P h.le_normalizer`. These are exactly
the displayed hypotheses of the existing compact quotient induced forms.
Their realization for actual reductive parabolics is not proved here.

`A : SmoothRep.{0, uG, uV} ℂ M` is the actual inducing smooth representation,
and compact open subgroups of `M` are cofinal among its open subgroups. The
preliminary independence theorem additionally takes admissibility and
irreducibility of `A.representation` and two actual invariant positive forms.

For the normalized construction, `C : Subgroup M` is an explicitly normal
central subgroup. The actual quotient `M ⧸ C` carries a Borel measurable space
and a Haar measure `μ` invariant under inversion. The representation is
irreducible and satisfies the existing predicate

```lean
IsSquareIntegrableModCentralSubgroup C hC A.representation μ.
```

This predicate includes admissibility, a unitary central character of the full
abstract center, and square-integrability of all actual smooth-dual coefficient
norms on that quotient. Admissibility is taken from its first component; no
second admissibility witness is required by the normalized constructor.
Square-integrability specifies the inducing domain of the construction rather
than being asserted as a structural property of arbitrary representations.

The group and carrier universes `uG`, `uV` are independent. There is no norm,
topology or completion on the original algebraic complex carrier, no finite
length or global finite-dimensionality hypothesis, and no irreducibility or
admissibility assumption on either induced representation.

## Independence of the actual unnormalized tensor form

All declarations are in `Langlands.Plancherel`.
`normalizedInducedDualTensorForm_independent` proves equality of the actual
two-induced-factor tensor forms obtained from any `b` and `c`. The proved
`InvariantPositiveForm.exists_pos_rescale_eq` writes `c` as a positive real
rescaling of `b`. Substitution reduces the equality to the existing
`normalizedInducedDualTensorForm_rescale` theorem. Hence the conclusion is
equality of forms on all tensor pairs, not only equality on pure tensors and
not a hypothesis about the forms.

This theorem uses Schur only on the original inducing representation through
the positive-form uniqueness theorem. It assumes no induced irreducibility.

## The selected form and its computation

`formalDegreeInducedTensorForm` first selects an invariant positive form on
`A` from the proved
`HarishChandraSchwartz.isUnitarizable_of_isSquareIntegrableModCentralSubgroup`.
It forms the existing actual `normalizedInducedDualTensorForm` and rescales it
by the inverse of

```lean
representationFormalDegree C hC μ hcof hsq hi.
```

The positivity required by `rescale` is obtained from the proved
`representationFormalDegree_pos`. Thus the result is a positive definite
Hermitian form preserved by `normalizedInductionDualTensorAction`, the actual
external `G × G` action on the two normalized induced factors. The selection
of the positive inducing form is justified by the unitarizability theorem;
no existence certificate is added as an input.

`formalDegreeInducedTensorForm_eq` identifies the selected form with the
inverse-degree rescaling of the construction from **every** actual invariant
positive inducing form `b`. The proof unfolds the selection, applies the
all-form independence theorem, and maps that equality through the same
positive rescaling. This removes the arbitrary inducing-form choice from
the entire form, not only from one displayed computation.

`formalDegreeInducedTensorForm_inner_tmul` therefore gives, for every such `b`,

```text
⟨f ⊗ ℓ, j ⊗ m⟩ = d(A)⁻¹ · Iform(A,b)(f,j)
                         · Iform(A.contragredient,dual(b))(ℓ,m).
```

Here `dual(b)` is the existing actual smooth-dual form and `d(A)` is the
constructed degree on the same fixed central quotient and measure. Both
`Iform` factors are the existing actual compact quotient induced forms with
their literal chosen measure. The proof uses the preceding equality,
`rescale_inner`, the actual tensor product computation, the compatibility
of complex embedding with inversion, and associativity of multiplication.

## Retained obligations

The explicit central subgroup `C` and the parabolic subgroups have not been
identified here with their general reductive source realizations. The selected
Bruhat measure has not been compared with the task's fixed compact Haar
normalization. The comparison between induction of the dual and the dual of
induction, the comparison with product-induction coefficient models,
representative transport between distinct inducing carriers, and smooth
spectral-family forms remain separate. Lemma V.2.2, the analytic transform,
inversion and all seven whole-task completion conditions remain open. This
unit constructs the actual inverse-degree positive form and proves its
independence of all positive inducing-form choices under the stated inputs.

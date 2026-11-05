# Positive-form uniqueness for irreducible admissible representations

This module constructs the actual linear equivariant comparison between two
invariant positive Hermitian forms and proves that they differ by a strictly
positive real scalar on an irreducible admissible complex representation.
It proves this relation rather than accepting it as an input to subsequent
normalization constructions.

## Provenance

This is a derived consequence of the existing
`InvariantPositiveForm.smoothDualEquiv` and the proved
`admissibleSchur_scalarEndomorphism`. It supplies the arbitrary-form comparison
needed for Waldspurger, *La formule de Plancherel pour les groupes p-adiques
(d'après Harish-Chandra)* (2003), V.2, printed p.293 / PDF p.59, the paragraph
before Lemma V.2.2. That paragraph constructs the two induced Hermitian forms
and explains their tensor product's independence by reciprocal positive
rescaling. The source takes irreducible square-integrable inducing data. The
helper here uses irreducibility and admissibility for the form comparison;
it does not require or establish square-integrability, induction,
formal-degree normalization or the source Plancherel theorem.

The implemented proof uses the two actual Hermitian identifications and the
published admissible Schur proof. It does not claim that the source contains
these implementation details or a separately numbered theorem with this
statement.

## Setting

The original representation is `ρ : Representation ℂ G V`. The group and
carrier universes `uG` and `uV` are independent. The original carrier has only
its algebraic additive group and complex module structures; no norm, topology,
completion, finite length or global finite dimension is assumed.

The two diagonal-pairing adapters need no group topology. The comparison
intertwiner needs a topological group, compact open subgroups cofinal among
open subgroups, admissibility of `ρ`, and two actual invariant positive forms
`b` and `c`. Cofinality and admissibility give surjectivity of each existing
Hermitian identification with the actual smooth dual.

The positive scalar conclusion additionally requires `ρ.IsIrreducible`.
This yields a nonzero vector from the existing simple-module definition, so
no separate nontriviality or chosen-vector assumption is needed. No
irreducibility, admissibility or unitarity of an induced representation is
assumed or concluded.

## Diagonal pairings

All declarations are in `Langlands.InvariantPositiveForm`.
`inner_self_ofReal_re` identifies a diagonal pairing with the complex
embedding of its real part. It is a direct adapter of
`InnerProductSpace.Core.inner_self_ofReal_re` for the actual core of the form.
`inner_self_re_pos` proves strict positivity of that real part for a nonzero
vector: nonnegativity is part of the form, while equality to zero would imply
that the vector is zero by the existing core definiteness theorem.

These adapters do not install a norm on the carrier. A local algebraic
inner-product core is used only to apply the existing core lemmas.

## The actual comparison intertwiner

Write `E_b` and `E_c` for the existing `smoothDualEquiv` maps associated with
the two forms. Their forward maps send `v` to the actual smooth functional
`w ↦ b.inner v w`, respectively `w ↦ c.inner v w`. Both are conjugate-linear.
`comparisonIntertwiner b c hcof hρ` has underlying map

```text
T = E_b⁻¹ ∘ E_c : V → V.
```

The composition is complex linear because it composes the two conjugate-linear
maps. To verify equivariance, apply injectivity of `E_b`, use the existing
equivariance of the two Hermitian maps and the inverse law for `E_b`. Thus the
result is an actual `ρ.IntertwiningMap ρ`, not merely a linear map or a supplied
scalar comparison.

`comparisonIntertwiner_inner` evaluates the equality `E_b(T(v)) = E_c(v)` on
an arbitrary `w`. It gives

```text
b.inner (T(v)) w = c.inner v w.
```

The order of the arguments is essential because the convention is
conjugate-linearity in the first argument.

## Positive rescaling

`exists_pos_rescale_eq` proves

```lean
∃ a : ℝ, ∃ ha : 0 < a, c = b.rescale a ha
```

under the displayed cofinality, admissibility and irreducibility hypotheses.
Admissible Schur applied to the constructed intertwiner gives a complex scalar
`z` with `T(v) = z • v`. The comparison identity and first-variable
conjugate-linearity then give

```text
c.inner v w = conj(z) * b.inner v w.
```

Choose a nonzero vector using irreducibility and set

```text
a = re(c.inner v v) / re(b.inner v v).
```

Both diagonal real parts are strictly positive, so `a > 0`. The diagonal
comparison, the real diagonal identities and cancellation of the nonzero
`b.inner v v` give `conj(z) = (a : ℂ)`. Substituting this relation in every
pairing and applying `ext_inner` proves equality with the actual rescaled
form on all vector pairs.

The conclusion is uniqueness up to positive scale, expressed by existence of
a positive rescaling relating any supplied forms. The module does not choose
a preferred scale or identify unscaled forms. Combining it with cancellation
on an actual tensor, comparing different representation carriers, supplying
induced integral/Haar normalizations and formal degrees, and constructing
smooth spectral-family forms remain subsequent steps. No whole-task completion
condition is discharged by this helper alone.

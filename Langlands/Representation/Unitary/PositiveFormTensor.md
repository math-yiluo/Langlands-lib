# Positive rescaling and tensor products of invariant Hermitian forms

This module constructs the positive Hermitian form on the original algebraic
tensor of two complex representations, invariant under their actual external
product action. It also constructs positive real rescaling and proves that
reciprocal rescalings of the two factors cancel on every tensor. It reuses
`Langlands.InvariantPositiveForm` and the published binary positivity theorem in
`Langlands.Representation.Tensor.UnitaryProof`; it introduces no alternative
representation or Hermitian-form framework.

## Source and provenance

The motivation is J.-L. Waldspurger, *La formule de Plancherel pour les groupes
p-adiques (d'après Harish-Chandra)*, V.2, printed p.293 / PDF p.59, the paragraph
before Lemma V.2.2. The registered source is `waldspurger-2003-plancherel`,
SHA-256 `4b6a6162cd0b3863703fb2f65d1698f926caf813114917f2084c16e38f2e30f7`.
The original page was read, including its displayed formulas. Waldspurger uses
forms conjugate-linear in the first variable, tensors the two induced forms,
and multiplies the result by the inverse formal degree. He explains independence
under rescaling the inducing form using inverse rescaling of its dual form.

The present construction is a generic internal prerequisite for that argument.
It proves positivity, external-action invariance and the tensor cancellation
once the two invariant positive forms are given. It does not claim to construct
Waldspurger's induced integral forms, to identify the second factor as a dual,
or to supply his formal-degree normalization. In particular, the use here of
two possibly different groups does not translate the printed reference to a
`G`-invariant form on the inducing Levi representation: each given form is
invariant for its actual representation and group.

## Parameters and conventions

All declarations are in `Langlands.InvariantPositiveForm`. The common data are

```lean
universe uG uH uV uW
{G : Type uG} [Group G]
{H : Type uH} [Group H]
{V : Type uV} [AddCommGroup V] [Module ℂ V]
{W : Type uW} [AddCommGroup W] [Module ℂ W]
{ρ : Representation ℂ G V} {σ : Representation ℂ H W}
```

The four universes are independent. No finite dimensionality, nonzero carrier,
smoothness, topology, local compactness, admissibility or irreducibility is
assumed. The tensor carrier is literally `V ⊗[ℂ] W`, and its action is

```lean
Representation.tprod (ρ.comp (MonoidHom.fst G H))
  (σ.comp (MonoidHom.snd G H))
```

Thus `(g,h)` sends `v ⊗ w` to `ρ(g)v ⊗ σ(h)w`. The resulting form is
conjugate-linear in the first tensor variable and complex-linear in the second,
as required by the existing positive-form core.

## Rescaling and extensionality

`ext_inner` proves equality of invariant positive forms with equal inner
products. The proof unfolds the nested structures, applies function
extensionality and uses proof irrelevance for their laws. `add_right` is an
adapter for the published
`FiniteTensor.InvariantPositiveFormProof.core_inner_add_right`, which obtains
additivity in the second variable from first-variable additivity and Hermitian
symmetry.

For a given `b : InvariantPositiveForm ρ`, real `a` and proof `ha : 0 < a`,
`b.rescale a ha` is the positive invariant form with

```text
(b.rescale a ha).inner v w = (a : ℂ) * b.inner v w.
```

`rescale_inner` is this computation law. Realness of the scalar preserves
Hermitian symmetry, and positivity preserves the nonnegative real part on the
diagonal. For definiteness, the nonzero real scalar cancels from a zero
self-pairing. Sesquilinearity and action invariance follow directly from those
of `b`.

## Tensor construction and published reuse

For `b : InvariantPositiveForm ρ` and `c : InvariantPositiveForm σ`,
`b.tensorProduct c` is an invariant positive form for the displayed external
action on the original tensor. It selects the positive core supplied by the
published theorem

```lean
Langlands.FiniteTensor.InvariantPositiveFormProof.exists_core_tmul
  b.toInnerProductCore c.toInnerProductCore
```

That theorem already proves positivity and definiteness on the entire binary
algebraic tensor, with independent factor universes, and gives the product
formula on pure tensors. Its implementation uses Mathlib's tensor inner
product after deriving local normed structures from the given cores. Mathlib
reduces positivity to finite-dimensional subspaces containing a tensor, so no
finite-dimensionality or completeness hypothesis on either factor is needed.
This module imports that construction by Lean name; it does not reprove it or
install a norm or topology on either incoming carrier.

The new adapter supplies the actual binary external-action invariance for the
selected core. Double tensor induction reduces this to the factor forms'
invariance, using the published pure-tensor formula in the pure case and
additivity in the other cases. The second-variable additive case reuses the
published `core_inner_add_right`.

`tensorProduct_inner_tmul` is the selected witness's exact computation law:

```text
(b.tensorProduct c).inner (v ⊗ w) (v' ⊗ w')
  = b.inner v v' * c.inner w w'.
```

The published `Langlands.FiniteTensor.invariantPositiveForm` constructs positive
forms for finite indexed tensors on `PiTensorProduct` under a product of an
indexed family of groups. This adapter uses its already published binary-core
prerequisite to provide a chosen form on `TensorProduct` under `G × H`, with
rescaling identities for that form. It does not redefine or modify the indexed
tensor representation or its positivity theorem.

## Rescaling identities and scope

For positive real `a,d`, `tensorProduct_rescale_inner` states, for arbitrary
`t,s : V ⊗[ℂ] W`,

```text
((b.rescale a ha).tensorProduct (c.rescale d hd)).inner t s
  = ((a*d : ℝ) : ℂ) * (b.tensorProduct c).inner t s.
```

The proof uses tensor induction in both variables. The pure-tensor case is
the preceding formula and multiplication in ℂ; the additive cases use the
forms' additivity. `tensorProduct_rescale` packages this as equality with
`(b.tensorProduct c).rescale (a*d) (mul_pos ha hd)` by `ext_inner`.
Finally, `tensorProduct_rescale_inv` specializes to `d = a⁻¹` and cancels the
nonzero real scalar, proving equality with `b.tensorProduct c` on the entire
algebraic tensor.

These are algebraic construction and comparison laws. The second form is not
assumed or proved here to be the contragredient form, and inverse scaling of
that actual dual construction remains a separate obligation. Existence and
scaling of the actual parabolic integral forms, uniqueness of an inducing
invariant form up to positive scale, the source's actual inverse-degree
normalization, representative and parabolic comparisons, spectral-family
spaces, positivity of their integrated forms and Plancherel remain separate
constructions or proof obligations. The unit alone closes no whole-program
completion condition.

Author: Worker 200.

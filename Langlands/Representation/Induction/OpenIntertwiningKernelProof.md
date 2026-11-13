# Intertwining kernels of compact induction from an open subgroup: proof

Worker 40 proves
`Langlands.Induction.CompactInductionKernelStatement.{uR, uG, uV}` from the module
`Langlands.Representation.Induction.OpenIntertwiningStatement` as the theorem

```lean
theorem Langlands.Induction.compactInductionKernel :
    CompactInductionKernelStatement.{uR, uG, uV}
```

in `Langlands.Representation.Induction.OpenIntertwiningKernelProof`. The theorem
takes no hypotheses beyond those of the statement, and the statement pair and
everything it imports are unchanged. The module imports only the statement module.

## What is proved

Let `R` be a commutative ring, `G` a topological group, `H` an open subgroup
(`hH : IsOpen (H : Set G)`) and `A`, `B` objects of
`Langlands.SmoothRep.{uR, uG, max uG uV} R H`. Write `i_v` for the published
`unitFunction H hH A.representation A.isSmooth v`, the compactly induced function
supported on `H` with value `A(h) v` at `h`. The theorem proves both conjuncts of the
statement:

1. every morphism
   `T : (smoothCompactInduction R H).obj A ⟶ (smoothCompactInduction R H).obj B`
   has an intertwining kernel `Φ` (`IsIntertwiningKernel H A.representation
   B.representation Φ`) with `Φ g v = (T i_v)(g)` for all `g` and `v`;
2. for every intertwining kernel `Φ` there is exactly one such `T` with
   `Φ g v = (T i_v)(g)` for all `g` and `v`.

This is Vignéras 1996, I.8.5, in the case `K = H` with `H` open and without the
finite-type hypothesis (registered source
`provided-74667a7cddb3bdafff85f01c658605ce7d929f6da73950d79457c46bcd761dd4`,
printed pp.67–68, PDF pp.85–86). The source's support condition a) is replaced by the
statement's per-vector condition that only finitely many right cosets `H g` have
`Φ g v ≠ 0`. The statement's Markdown records this comparison.

## Library results used

From `Langlands.Representation.Induction.OpenAdjunction`:

- `compactInductionHomEquiv H hH A B'`, Frobenius reciprocity
  `((smoothCompactInduction R H).obj A ⟶ B') ≃ (A ⟶ (smoothRestriction R H).obj B')`.
  It sends `T` to the `H`-map `v ↦ T (unitMap v)`, whose value at `v` is by definition
  `SmoothRep.hom T (unitFunction H hH A.representation A.isSmooth v)`. The proof uses it
  with `B' = (smoothCompactInduction R H).obj B`.
- `quotientSupport_finite`: for open `H`, the projected support in `H \ G` of a compactly
  induced function is finite.
- `openSubgroupMap`: the image in `G` of an open subgroup of `H`, as an open subgroup
  of `G`.
- `compactFunctions_ext`: compactly induced functions with equal values are equal.

From `Langlands.Representation.Induction.Definitions`: `compactFunctionOf`, which
builds a compactly induced function from a function `G → W`, its left covariance, a
right-invariance open subgroup and compactness of its projected support, and `eval`.
From `Langlands.Representation.Category.Basic`: `SmoothRep.hom` and `SmoothRep.ofHom`,
which are mutually inverse by definition.

## Auxiliary declarations

All are in namespace `Langlands.Induction`. Here `σ` and `τ` are representations of `H`
on `V` and `W`, and `φ : σ.IntertwiningMap ((compactInduced H τ).comp H.subtype)` is an
`H`-map from `σ` to the restriction to `H` of `c-Ind_H^G τ`.

- `evalLinearMap H τ g`: evaluation `f ↦ f(g)` at `g : G`, as an `R`-linear map
  `CompactFunctions H τ →ₗ[R] W`.
- `intertwinerKernel H φ g = evalLinearMap H τ g ∘ₗ φ`, so
  `intertwinerKernel H φ g v = (φ v)(g)` (`intertwinerKernel_apply`).
- `isIntertwiningKernel_intertwinerKernel H hH φ`: `intertwinerKernel H φ` is an
  intertwining kernel. For covariance, `(φ v)(h g h') = τ(h) ((φ v)(g h'))` is the left
  covariance of the compactly induced function `φ v`. Equivariance of `φ` gives
  `φ (σ(h') v) = (φ v)(· h')`, so `(φ v)(g h') = (φ (σ(h') v))(g)`. Finiteness of
  `quotientSupport H (fun g => (φ v)(g))` is `quotientSupport_finite`.
- `kernelFunction H hH hσ Φ hΦ v`, for smooth `σ` (`hσ : IsSmooth σ`), an intertwining
  kernel `Φ` and a vector `v`: the compactly induced function `g ↦ Φ g v`, built with
  `compactFunctionOf`.
  - Left covariance `Φ (p x) v = τ(p) (Φ x v)` is the covariance of `Φ` with `h' = 1`.
  - For right invariance, take an open subgroup `K` of `H` fixing `v` (smoothness of `σ`,
    chosen with `Classical.choose`). For `k ∈ openSubgroupMap H hH K`, covariance with
    `h = 1` gives `Φ (x k) v = Φ x (σ(k) v) = Φ x v`.
  - The projected support is finite by the second conjunct of `hΦ`, hence compact.

  `eval_kernelFunction` records that its value at `g` is `Φ g v`, by definition.
- `kernelIntertwiner H hH hσ Φ hΦ`: the `H`-map `v ↦ kernelFunction H hH hσ Φ hΦ v`.
  Additivity and `R`-linearity hold valuewise by linearity of each `Φ x`.
  `H`-equivariance, `Φ x (σ(h) v) = Φ (x h) v`, is covariance with `h = 1`.
- `intertwinerKernel_eq_iff H hH hσ Φ hΦ φ`: `(∀ g v, Φ g v = (φ v)(g))` holds exactly
  when `φ = kernelIntertwiner H hH hσ Φ hΦ`. The forward direction is
  `Representation.IntertwiningMap.ext` together with `compactFunctions_ext`. The reverse
  direction holds by definition.

## Proof of the main theorem

Fix `R`, `G`, `H`, `hH`, `A`, `B` and let
`e = compactInductionHomEquiv H hH A ((smoothCompactInduction R H).obj B)`.

1. For a morphism `T`, take `Φ = intertwinerKernel H (SmoothRep.hom (e T))`. By
   `isIntertwiningKernel_intertwinerKernel` it is an intertwining kernel. Since
   `SmoothRep.hom (e T) v` is by definition `SmoothRep.hom T (unitFunction … v)`, the
   identity `Φ g v = (T i_v)(g)` holds by `rfl`.
2. For an intertwining kernel `Φ`, let
   `φ = kernelIntertwiner H hH A.isSmooth Φ hΦ`. For every morphism `T`, the condition
   `∀ g v, Φ g v = (T i_v)(g)` is equivalent to `e T = SmoothRep.ofHom φ`. This follows
   from `intertwinerKernel_eq_iff` applied to `SmoothRep.hom (e T)`, using that
   `SmoothRep.hom` and `SmoothRep.ofHom` are inverse. Hence
   `T = e.symm (SmoothRep.ofHom φ)` satisfies the condition, by
   `Equiv.apply_symm_apply`. Any `T'` satisfying it has `e T' = SmoothRep.ofHom φ`, so
   `T' = e.symm (SmoothRep.ofHom φ)` by `Equiv.eq_symm_apply`. This proves existence
   and uniqueness.

## Development check

In environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` the module compiles with no
errors or warnings. Declaration inspection of `Langlands.Induction.compactInductionKernel`
reports level parameters `uR`, `uG`, `uV` and axioms exactly `propext`,
`Classical.choice` and `Quot.sound`. This is development evidence; the exact-target
check, the build and independent review are separate.

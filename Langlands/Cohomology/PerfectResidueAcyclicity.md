# Acyclicity of a strictly perfect complex from its reductions at maximal ideals

Module `Langlands.Cohomology.PerfectResidueAcyclicity`, namespace
`Langlands.Cohomology.ModuleComplex`.

## Definition

```lean
def residueRestrictId (m : Ideal R) :
    (ModuleCat.restrictScalars (Ideal.Quotient.mk m)).obj (ModuleCat.of (R ⧸ m) (R ⧸ m)) →ₗ[R]
      R ⧸ m
```

For an ideal `m` of a commutative ring `R`, this is the identity function of
`R ⧸ m` (`toFun s := s`), viewed as an `R`-linear map. Its source is `R ⧸ m`
with the `R`-module structure obtained by restricting scalars along
`Ideal.Quotient.mk m`, where `r • s = [r] * s`. This is the coefficient module
in Mathlib's `ModuleCat.extendScalars`, so `baseChange (Ideal.Quotient.mk m)`
uses it. Its target is `R ⧸ m` with the standard quotient-module structure.
Linearity is the identity `[r] * x = r • x` (`mk_mul_eq_smul`). This adapter lets
Mathlib's `TensorProduct.quotTensorEquivQuotSMul`, which is stated for the
standard structure, be applied to the tensor products that occur in
`baseChange`. It is an internal technical definition with no counterpart in the
literature.

## Main result

```lean
theorem acyclic_of_isStrictlyPerfect_of_residue_acyclic
    {K : CochainComplex (ModuleCat.{u} R) ℤ} (hK : IsStrictlyPerfect K)
    (hres : ∀ m : Ideal R, m.IsMaximal →
      ((baseChange (Ideal.Quotient.mk m)).obj K).Acyclic) :
    K.Acyclic
```

Here `R : Type u` is any commutative ring, with no noetherian hypothesis. The
complex `K` is strictly perfect in the sense of the published
`Langlands.Cohomology.ModuleComplex.IsStrictlyPerfect`: it is bounded (strictly
supported in some interval `[a, b]` of degrees) and every term is a finite
projective `R`-module. `baseChange (Ideal.Quotient.mk m)` is the published
ordinary degreewise extension of scalars along `R → R ⧸ m`, so its value on `K`
is the complex `(R ⧸ m) ⊗_R K`. `Acyclic` is Mathlib's
`HomologicalComplex.Acyclic`, which means exact in every degree.

In words, the theorem says that if `(R ⧸ m) ⊗_R K` is exact for every maximal
ideal `m`, then `K` is exact.

## Provenance

This is a derived special case of Stacks, More on Algebra, Lemma
`lemma-check-perfect-pointwise` (tag 068V), implication (3) ⇒ (1). See
`more-algebra.tex` at git commit `a04446e57ec1fbc252a871afcec7752fb2807b14`,
lines 20031–20062, registered source `stacks-perfect-complexes-a04446e5`.
That lemma takes a pseudo-coherent complex. Its condition (3) asks that, for
every maximal ideal `m`, `H^i(K ⊗^L_R κ(m)) = 0` for all `i ∉ [a, b]`, and it
concludes that `K` is perfect with tor amplitude in `[a, b]`. The first step
of the proof of (3) ⇒ (1) shows `H^i(K) = 0` for every `i ∉ [a, b]`. Under our
hypothesis every `H^j` of every reduction vanishes, so condition (3) holds for
every interval. Given a degree `i`, choosing an interval `[a, b]` that omits
`i` yields `H^i(K) = 0`. Our statement is this consequence, specialized in
three ways:

- `K` is a strictly perfect complex, which is in particular pseudo-coherent;
- for such a bounded complex of projectives the derived tensor product
  `K ⊗^L_R κ(m)` is computed by the ordinary degreewise tensor product, which is
  the published `baseChange`. This identification is not used or proved here:
  the hypothesis is stated directly with the ordinary tensor product;
- `κ(m)` is written as the quotient ring `R ⧸ m`, which is a field because `m`
  is maximal.

The Lean proof does not follow the Stacks route (cutting the complex in two,
localizing and gluing). It uses the direct argument below.

## Proof

The helper results in this module are:

- `subsingleton_of_forall_maximal_mkQ_eq_zero` (global Nakayama lemma): a finite
  `R`-module `M` with `M = m • M` for every maximal ideal `m` is zero. Proof: if
  the annihilator of `M` were a proper ideal, it would lie in some maximal ideal
  `m`. Mathlib's Nakayama lemma
  `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul` gives `r`
  with `r - 1 ∈ m` and `r • M = 0`. Then `r ∈ m`, so `1 ∈ m`, which is a
  contradiction. Hence `1` annihilates `M`.
- `mk_mul_eq_smul` and `residueRestrictId`: the identity map of `R ⧸ m` is
  `R`-linear from the restricted-scalars module used inside
  `ModuleCat.extendScalars` to the standard quotient module. This lets Mathlib's
  `TensorProduct.quotTensorEquivQuotSMul`, `(R ⧸ m) ⊗_R N ≃ N ⧸ m • N`, be
  applied to the tensor products that occur in `baseChange`.
- `exists_retraction_ker`: if the image of `d : K^i → K^j` is projective, then
  the surjection `K^i → im d` splits by a section `s`. The map `x ↦ x - s(d x)` is
  a retraction `π : K^i → ker d` that is the identity on `ker d`.
- `ker_le_range_of_residue_exactAt` (one induction step): let `Z = ker d^{k+1}`
  have a retraction `π` as above, and let `K^{k+1}` be finite. Let `B ⊆ Z` be the
  image of `d^k`, and put `N = Z ⧸ B`, a finite module. For a maximal ideal `m`
  and `z ∈ Z`, the element `1 ⊗ z` of `(R ⧸ m) ⊗ K^{k+1}` is a cycle of the
  reduced complex. Exactness of that complex at `k + 1` gives `t` with
  `(R ⧸ m) ⊗ d^k (t) = 1 ⊗ z`. Apply the `R`-linear map
  `Φ : (R ⧸ m) ⊗ K^{k+1} → N ⧸ m • N`, which is the tensor product of the
  identity of `R ⧸ m` with `x ↦ [π x]`, followed by `quotTensorEquivQuotSMul`.
  `Φ` kills the image of `(R ⧸ m) ⊗ d^k`, as one checks on pure tensors using
  `π (d^k y) = d^k y ∈ B`. It sends `1 ⊗ z` to the class of `[z]`. Hence every
  element of `N` lies in `m • N`, for every maximal `m`. By the global Nakayama
  lemma `N = 0`, that is, `ker d^{k+1} ⊆ im d^k`.

Main theorem. Let `b` be the upper bound of `K`. For `i : ℤ` let `P i` say that
the image of `d^i : K^i → K^{i+1}` is a projective `R`-module and that `K` is
exact in every degree `j > i`.

- `P b` holds: `K^{b+1} = 0`, so the image of `d^b` is a zero module, hence
  projective (in fact free), and `K^j = 0` for `j > b`, so `K` is exact there.
- `P (k + 1) → P k`: from the projectivity of the image of `d^{k+1}`,
  `exists_retraction_ker` gives the retraction onto `ker d^{k+1}`. Since
  `K^{k+1}` is finite, the induction step gives `ker d^{k+1} ⊆ im d^k`, so `K`
  is exact at `k + 1`. Moreover `im d^k = ker d^{k+1}`, and `ker d^{k+1}` is a
  direct summand of the projective module `K^{k+1}`, hence projective
  (`Module.Projective.of_split`). Projectivity transfers to `im d^k` along the
  equality of submodules.

Descending induction (`Int.leInductionDown`) gives `P n` for every `n ≤ b`. For
any degree `j`, `P (min (j - 1) b)` gives exactness at `j`. The lower bound of
`K` is never used. Only the upper bound and the finiteness and projectivity of
the terms enter the proof.

The proof uses no `sorry` and no axioms beyond Lean's standard `propext`,
`Classical.choice` and `Quot.sound`.

## Intended use

This is the closed-fibre detection step for the proof of
`Langlands.AbelianScheme.AlgClosedFieldSquareFirstProjectionAcyclicityStatement`
(task `651d1a6b-549e-4d79-ae47-19627b02f30d`). Over an affine open `Spec R` of
the abelian variety, a universal perfect representative of the derived sections
of the line bundle is reduced modulo each maximal ideal. Each such reduction
computes the cohomology of a fibre over a rational point, which vanishes by
hypothesis. This module proves only the ring-theoretic step. It does not prove
the geometric identification, the universal perfect representative, or any
base-change statement.

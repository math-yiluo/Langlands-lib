# Good modules for a Čech differential: the noetherian core

Authors: Worker 299 and Worker 424. Worker 299 authored the module-theoretic
proof; Worker 424 extracted the definitions and statement and added its
exact-target wrapper. This helper module supports the proof of
`Langlands.Algebra.SmoothEqualizerFibreCriterion`. It contains internal
formal deductions from Mathlib; no literature result is formalized here.
The approach (dévissage over associated primes) was derived by Worker 299
as a replacement for the perfect-complex argument of Stacks Lemma 36.32.5
(Tag 0E62), which Mathlib does not provide.

## The notion

Fix a commutative ring `A₀`, two `A₀`-algebras `C₀`, `C₁` and an
`A₀`-linear map `d : C₀ →ₗ[A₀] C₁`. In the application `d = δ₁ - δ₂`, so
`d 1 = 0`. For an `A₀`-module `M`, the definition imported from
`Langlands.Algebra.CechEqualizer.Definitions`,

`Good d M : Prop := ∀ y : M ⊗[A₀] C₀, d.lTensor M y = 0 → ∃ m : M, m ⊗ₜ 1 = y`

says that every element of `M ⊗ C₀` killed by `M ⊗ d` has the form `m ⊗ 1`,
that is, the kernel of `M ⊗ d` is contained in the image of `M`. The
criterion's conclusion is the statement that `A` itself is good.

## Closure properties

The lemmas use the hypotheses named in their signatures; the common ones are
`hd : d 1 = 0`, flatness of `C₁` and faithful flatness of `C₀` over `A₀`.

- `good_of_subsingleton`: the zero module is good.
- `lTensor_rTensor_apply`: `M ⊗ d` commutes with `f ⊗ C₀` and `f ⊗ C₁`
  for a linear map `f`.
- `lTensor_tmul_one`: `(M ⊗ d)(m ⊗ 1) = 0` (uses `d 1 = 0`).
- `good_of_exact` (extensions): for a short exact sequence
  `0 → M' → M → M'' → 0` with `M'` and `M''` good, `M` is good, assuming
  `C₁` flat. Given `y` in the kernel, its image in `M'' ⊗ C₀` is `m'' ⊗ 1`;
  lift `m''` to `m`, then `y - m ⊗ 1` comes from `z ∈ M' ⊗ C₀` by right
  exactness. Flatness of `C₁` makes `M' ⊗ C₁ → M ⊗ C₁` injective, so `z` is
  in the kernel for `M'`, hence `z = m' ⊗ 1`.
- `good_prod`: finite products of good modules are good (special case of
  extensions).
- `good_of_fg`: if every finitely generated submodule of `N` is good, so is
  `N` (assuming `C₁` flat). An element of `N ⊗ C₀` comes from `M ⊗ C₀` for a
  finitely generated `M ≤ N`
  (`Submodule.exists_fg_le_subset_range_rTensor_subtype`), and flatness of
  `C₁` transfers the kernel condition to `M`.
- `good_of_injective` (submodules): if `f : M → N` is injective and `N` is
  good, `M` is good, assuming `C₀` faithfully flat. If `y` is in the kernel
  for `M`, then `f ⊗ C₀ (y) = n ⊗ 1`. The class of `n` in `N / range f`
  becomes `0` after tensoring with `C₀`, so it is `0` because
  `Q → Q ⊗ C₀` is injective for faithfully flat `C₀`
  (`Module.FaithfullyFlat.tensorProduct_mk_injective`). Thus `n = f m`, and
  flatness of `C₀` gives `y = m ⊗ 1`.
- `good_of_flat`: if a commutative `A₀`-algebra `K` is good, then every flat
  `K`-module `V` is good. Goodness of `K` is the exactness of
  `K → K ⊗ C₀ → K ⊗ C₁`; tensoring over `K` with the flat module `V`
  keeps it exact, and `V ⊗_K (K ⊗_{A₀} C) ≅ V ⊗_{A₀} C`
  (`TensorProduct.AlgebraTensorModule.cancelBaseChange`) identifies the
  result with the goodness of `V`.

## Coprimary modules and the noetherian core

- `good_of_isTorsionBySet_prime`: let `q` be a prime of `A₀` whose residue
  field `q.ResidueField` is good, and let `S` be a module killed by `q` on
  which every element outside `q` acts injectively. The localization
  `S_q` (`LocalizedModule q.primeCompl S`) is a module over the residue
  field of `A₀_q`, hence free and flat, so it is good by `good_of_flat`.
  The localization map `S → S_q` is injective by the regularity assumption,
  so `S` is good by `good_of_injective`.
- `good_of_isTorsionBySet_pow`: the same conclusion for a module killed by
  `q ^ n`, by induction on `n`, using the extension
  `0 → S → Q → Q / S → 0` with `S` the `q`-torsion submodule. Both the
  torsion submodule and the quotient still satisfy the regularity
  assumption, and the quotient is killed by `q ^ n`.
- `good_quotient_finsetInf`: if `M / J` is good for every `J` in a finite
  set `s` of submodules, then `M / (inf s)` is good, since it embeds into
  the product of the `M / J`.
- `good_of_associatedPrimes` (noetherian core): over a noetherian ring `A₀`,
  with `C₀` faithfully flat and `C₁` flat, an arbitrary module `N` is good as
  soon as `q.ResidueField` is good for every associated prime `q` of `N`.
  By `good_of_fg` it suffices to treat a finitely generated submodule `M`.
  Mathlib's Lasker theorem (`Submodule.IsLasker.exists_isMinimalPrimaryDecomposition`)
  writes `⊥ = J₁ ⊓ … ⊓ Jₖ` with each `Jᵢ` primary in `M`. The radical `qᵢ`
  of the colon ideal of `Jᵢ` is an associated prime of `M`, hence of `N`.
  `M / Jᵢ` is killed by a power of `qᵢ` (finite generation of `qᵢ`), and
  elements outside `qᵢ` act injectively on it (primary). So each `M / Jᵢ`
  is good by `good_of_isTorsionBySet_pow`; then `M / ⊥` is good by
  `good_quotient_finsetInf`, and `M` is good via the injective quotient map.

## Exact target

The theorem `Langlands.Algebra.CechEqualizer.noetherianGoodCriterion` has
exactly the type `Langlands.Algebra.CechEqualizer.NoetherianGoodCriterion`
imported from the same-named statement module. It introduces the rings,
module, structures, differential and explicit hypotheses, then applies
`good_of_associatedPrimes`. The base, both algebras and module have four
independent universe parameters. This wrapper adds no hypotheses; in
particular the module need not be finitely generated. The statement and its
definition imports are preserved unchanged by the proof submission.

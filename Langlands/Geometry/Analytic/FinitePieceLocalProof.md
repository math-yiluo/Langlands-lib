# Proof of the local structure of the finite pieces of an affine analytification map

Lean module: `Langlands.Geometry.Analytic.FinitePieceLocalProof`
(namespace `Langlands.Analytic.AffineAnalytification.FinitePieceLocal`). Support module for
Task 7655.

## Main result

```
theorem affineAnalytificationFinitePieceLocal
    (hchart : AffineAnalytificationChartFlatStatement.{u, v})
    (hdom : Domain.FlatnessStatement.{u}) :
    AffineAnalytificationFinitePieceLocalStatement.{u, v, w}
```

So the local statement for finite pieces holds given flatness of the chart algebras over the
coordinate algebra and flatness of affinoid-domain restrictions. The two hypotheses are only used
for condition 1 (flatness of `α`).

## Auxiliary results

* `tensor_ringHom_ext`: ring maps out of `R ⊗[A] B` that agree on `x ⊗ 1` and `1 ⊗ b` are
  equal.
* `finiteType_tensor`: `R ⊗[A] B` is of finite type over `R`, since `B` is of finite type over
  `K`, hence over `A`.

The following are proved for a piece as in `FinitePieceEngine`, with `C := R ⊗[A] B` and
`χ : C → S` a ring map with `χ (x ⊗ 1) = φ x` and `χ (1 ⊗ b) = recMap Q V' b`.

* `exists_test_comparison`: let `τ : C → E` be a ring map into a complete ultrametric normed
  `K`-algebra, given on `R` by a bounded map `τR`. Then there are `D`, `κ : C → D`, `ρ`, `θ`
  and `e` as in `exists_test_factorization`, with `ρ ∘ κ = χ` and `θ ∘ κ = τ`. Bounded maps out
  of `D` are determined by their composites with `κ`. The proof applies
  `exists_test_factorization` to `τR` and `τB := τ(1 ⊗ -)`. Then `κ` is
  `Algebra.TensorProduct.lift r bm`, and the identities follow from `tensor_ringHom_ext`.
* `surjective_of_isFiniteBanach`: if `φ` is finite Banach, `χ` is surjective. The image `S₀` of
  `χ` is an `R`-subalgebra of the finite `R`-module `S`, hence finite (`R` is Noetherian). Let
  `E := FiniteNormedModel.Model K R S₀` and `τ := χ` corestricted. The inclusion `ι : E → S` is
  bounded by `BoundedAlgHom.ofFiniteTriangle`, since it is compatible with the bounded maps
  `R → E` and `φ`. Uniqueness gives `ι ∘ θ = ρ`, so `S = ρ(D) ⊆ S₀`.
* `ker_le_pow`: if `φ` is finite Banach, then `ker χ ⊆ (χ⁻¹ n)^k` for every maximal ideal `n`
  of `S` and every `k`. Put `p := χ⁻¹ n` and `k ≥ 1`. By `exists_monic_aeval_mem_of_ker_le` and
  `finite_quotient_pow`, `Ck := C/p^k` is a finite `R`-module. Apply `exists_test_comparison`
  to `E := Model K R Ck` and the quotient map. The map `λ : E → S/n` induced by `χ` is bounded
  (`ofFiniteTriangle`, with `S/n` normed by `Ideal.Quotient.norm_mk_le`). Uniqueness gives
  `λ ∘ θ = (S → S/n) ∘ ρ`, so `λ(θ e) = 1`. Then `θ e` is a unit (`isUnit_of_lift_eq_one`) and
  idempotent, hence `θ e = 1` (`IsIdempotentElem.iff_eq_one_of_isUnit`). For `c ∈ ker χ`,
  `ρ(κ c) = 0` gives `e κ(c) = 0`, so the image of `c` in `Ck` is `θ(e) θ(κ c) = 0`.

## Proof of the main result

Choose original saturated charts `i₀` of `B` and `j₀` of `A` such that the chart `i₀` contains
`V'.locus`, the chart `j₀` contains `W.locus`, and the chart `j₀` contains the image of the
chart `i₀` (`exists_orig_superset`, compactness). Take `α := recMap P W j₀` and
`β := recMap Q V' i₀`.

* Condition 1 is `recMap_flat hchart hdom`.
* Conditions 2 and 3 are `recMap_pointSeminorm`.
* `χ` is `Algebra.TensorProduct.lift` of `φ` and `β`. It is well defined because
  `φ ∘ α = β ∘ f` (`pullback_recMap`).
* `C` is Noetherian, being of finite type over the Noetherian affinoid algebra `R`. Bijectivity
  of the local maps at the primes `ker s` is
  `FinitePieceLocalAlgebra.bijective_localRingHom_of_ker_le_pow`, applied to
  `surjective_of_isFiniteBanach` and `ker_le_pow`.

## Provenance

Internal. This module implements the argument in the Markdown of
`AffineAnalytificationFinitePieceLocalStatement`, section "Why condition 4 holds": test
factorizations, surjectivity, thickenings and Krull. It is the analytic input of the assembly
`finiteGermComparison_of_finitePieceLocal` that proves
`AffineAnalytificationFiniteGermComparisonStatement`. The literature context is Berkovich 1993,
Propositions 2.6.10, 3.2.10 and 3.3.11, as explained in that statement's Markdown. The route
here is different: it uses neither Zariski's Main Theorem nor Proposition 2.6.10.

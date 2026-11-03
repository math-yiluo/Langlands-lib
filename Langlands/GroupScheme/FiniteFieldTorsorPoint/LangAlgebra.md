# Commutative algebra for Lang's theorem

Author: Worker 1387.

This module collects the commutative algebra used in the proof of Lang's
theorem in [`LangCorepresented`](LangCorepresented.md). All declarations live in
`Langlands.GroupScheme.FiniteFieldTorsorPoint`. They are internal lemmas for
`Langlands.GroupScheme.FiniteFieldTorsorPointStatement`. Each is a standard fact;
the Lean proofs are described below.

## Finiteness from power relations

Let `C → A` be a commutative algebra, `ι` a finite type, `v : ι → A` and `q ≥ 2`.

- `monomial_mem_span_of_pow_mem_span`: if `v i ^ q` lies in the `C`-span of
  `insert 1 (Set.range v)` for every `i`, then every monomial
  `∏ i, v i ^ n i` (with `n : ι → ℕ`) lies in the `C`-span of the monomials
  `∏ i, v i ^ (e i)` with `e : ι → Fin q`, that is, with all exponents below `q`.
  The proof is strong induction on the total degree `∑ i, n i`. If all exponents
  are below `q` the monomial is a spanning vector. Otherwise some `n i ≥ q`. Write
  `n = n' + Pi.single i q` and expand `v i ^ q = a • 1 + ∑ j, c j • v j`. The
  monomial becomes `a • ∏ v ^ n' + ∑ j, c j • ∏ v ^ (n' + Pi.single j 1)`.
  These monomials have total degree `d - q` and `d - q + 1`, both smaller than
  `d` because `q ≥ 2`, so the induction hypothesis applies. The private helper
  `prod_pow_add_single` rewrites `∏ l, v l ^ (n + Pi.single j k) l` as
  `v j ^ k * ∏ l, v l ^ n l`.
- `finite_of_pow_mem_span`: if moreover `Algebra.adjoin C (Set.range v) = ⊤`, then
  `Module.Finite C A`. The finite spanning set is the image of the monomials with
  exponents below `q`. By `Algebra.adjoin_eq_span`, `A` is spanned by the
  submonoid closure of `Set.range v`, whose elements are monomials
  (`Submonoid.mem_closure_range_iff`), and the previous lemma applies.

## Krull dimension

- `ringKrullDim_le_of_isIntegral`: if `A` is integral over `C`, then
  `ringKrullDim A ≤ ringKrullDim C`. Contraction `P ↦ P.under C` is a strictly
  monotone map of prime spectra (`Ideal.IsIntegral.under_lt_under`), so
  `Order.krullDim_le_of_strictMono` applies.
- `exists_ringKrullDim_eq_of_finiteType`: a nonzero finitely generated algebra `A`
  over a field `k` has Krull dimension a natural number `m`. A surjection from a
  polynomial ring in `n` variables (`Algebra.FiniteType.iff_quotient_mvPolynomial''`)
  bounds the dimension by `n` (`ringKrullDim_le_of_surjective` and the dimension of
  a polynomial ring over a field), and a nontrivial ring has nonnegative dimension.
- `injective_of_isIntegral_range`: let `A` be a domain, finitely generated over a
  field `k`, and `ψ : A →ₐ[k] A` such that `A` is integral over the subalgebra
  `ψ.range`. Then `ψ` is injective. Indeed `ringKrullDim A ≤ ringKrullDim ψ.range`
  by the first lemma. If `x ≠ 0` with `ψ x = 0`, then `x` is a nonzerodivisor in
  the kernel of the surjection `ψ.rangeRestrict : A → ψ.range`, so
  `ringKrullDim ψ.range + 1 ≤ ringKrullDim A`
  (`ringKrullDim_succ_le_of_surjective`). This contradicts finiteness of
  `ringKrullDim A`.

## Lifting to an algebraically closed field

- `exists_lift_of_isIntegral`: let `A` be integral over `C` with `algebraMap C A`
  injective, `K` an algebraically closed field and `f : C →+* K`. Then there is
  `g : A →+* K` with `g.comp (algebraMap C A) = f`. The kernel `p` of `f` is prime,
  and lying over (`Ideal.exists_ideal_over_prime_of_isIntegral`, using injectivity)
  gives a prime `P` of `A` with `P.under C = p`. Then `A ⧸ P` is an integral, hence
  algebraic, torsion-free algebra over the domain `C ⧸ p`, and `K` is a
  `C ⧸ p`-algebra through the injective `RingHom.kerLift f`. Mathlib's
  `IsAlgClosed.lift` gives `φ : (A ⧸ P) →ₐ[C ⧸ p] K`, and `g` is `φ` composed with
  the quotient map.
- `exists_comp_eq_of_isIntegral_range`: let `A` be a domain, finitely generated
  over a field `k`, `ψ : A →ₐ[k] A` with `A` integral over `ψ.range`, `K` an
  algebraically closed `k`-algebra and `y : A →ₐ[k] K`. Then there is
  `g : A →ₐ[k] K` with `g.comp ψ = y`. By the previous section `ψ` is injective,
  so `AlgEquiv.ofInjective` identifies `A` with `ψ.range`. Lifting
  `y ∘ (ψ.range ≃ A)` along the inclusion `ψ.range → A` gives `g` with
  `g (ψ a) = y a`; it is `k`-linear because `ψ` and `y` are.

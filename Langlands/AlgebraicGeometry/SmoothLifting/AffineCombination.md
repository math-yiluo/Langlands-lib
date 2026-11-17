# Affine combinations of ring maps into square-zero extensions

Namespace `Langlands.AlgebraicGeometry.SmoothLifting`. This module is the
commutative-algebra layer of the proof of
`Langlands.AlgebraicGeometry.SmoothThickeningLiftingStatement`. It contains
no scheme theory.

## Square-zero ideals and affine combinations

- `SqZero J` says that `a * b = 0` for all `a b ∈ J`, for an ideal `J` of a
  commutative ring `R`. `SqZero.map` shows that the extension `J.map ρ` along
  a ring map `ρ` is again square-zero, using `Ideal.map_mul`.
- `affComb J hJ φ₀ φ hφ c` takes ring maps `φ₀, φₖ : B →+* R` (with `k` in a
  finite type `ι`) such that every `φₖ b - φ₀ b` lies in `J`, and weights
  `c : ι → R`. It is the ring map `b ↦ φ₀ b + ∑ₖ cₖ (φₖ b - φ₀ b)`. The
  weights need not sum to one.
  - Multiplicativity is the identity
    `φₖ(ab) - φ₀(ab) = φ₀ a (φₖ b - φ₀ b) + φ₀ b (φₖ a - φ₀ a)`, which holds
    because `(φₖ a - φ₀ a)(φₖ b - φ₀ b) = 0`.
  - The cross term of the two sums also vanishes, since both sums lie in
    `J`.
- `affCombₐ` is the version for `A`-algebra maps; the weighted differences
  vanish on `algebraMap A B`. `affComb₂ₐ` is the binary case
  `φ₀ + c (φ₁ - φ₀)`, indexed by `Unit`.
- `affComb_sub_mem` says that the combination is congruent to `φ₀` modulo
  `J`.

## Torsion lemma

`exists_pow_mul_sub_eq_zero`: let `B` be a finitely generated `A`-algebra,
`L, L' : B →ₐ[A] R`, and `ρ : R →+* R'` a ring map whose kernel is
`g`-power torsion. If `ρ ∘ L = ρ ∘ L'`, then there is one exponent `M` with
`g ^ M * (L b - L' b) = 0` for all `b`.

The proof picks finitely many algebra generators and an exponent for each,
and takes `M` to be the maximum. The set `{b | g ^ M * (L b - L' b) = 0}`
is an `A`-subalgebra:
- it contains `algebraMap A B`;
- it is closed under addition;
- it is closed under multiplication, by
  `L(ab) - L'(ab) = L a (L b - L' b) + (L a - L' a) L' b`.

So it contains `Algebra.adjoin` of the generators, which is everything.

## Extension lemma

`exists_extension` is the algebraic heart of the Čech argument. Its
hypotheses:
- `B` is a finitely presented `A`-algebra.
- `J` is a square-zero ideal of `R`.
- `ρ : R →ₐ[A] R'` behaves like the localization at an element `g`:
  - (`h1`) its kernel is `g`-power torsion;
  - (`h2`) every element of `J.map ρ` becomes the image of an element of
    `J` after multiplication by a power of `ρ g`.
- `β : B →ₐ[A] R` and `β' : B →ₐ[A] R'` satisfy
  `β' b - ρ (β b) ∈ J.map ρ`.

The conclusion: for all large `N` there is `γ : B →ₐ[A] R` with
`γ ≡ β (mod J)` and `ρ ∘ γ = ρ ∘ β + (ρ g)^N (β' - ρ ∘ β)`.

The proof uses a presentation `π : MvPolynomial (Fin r) A → B`, which is
surjective with finitely generated kernel (`Algebra.FinitePresentation`):

1. Write the differences `β'(π Xₗ) - ρ(β(π Xₗ))` as `(ρ g)^{-n} ρ(e'ₗ)`
   with `e'ₗ ∈ J`.
2. Put `γ̃_j = aeval (β(π Xₗ) + g^j e'ₗ)`. Two identities of
   `MvPolynomial` algebra maps are checked on the variables with
   `MvPolynomial.algHom_ext`:
   - `ρ ∘ γ̃_j = ρ ∘ β ∘ π + (ρ g)^{n+j} (β' ∘ π - ρ ∘ β ∘ π)`;
   - `γ̃_j = β ∘ π + g^j (γ̃₀ - β ∘ π)`.

   Both right-hand sides are ring maps by `affComb₂ₐ`, so no
   partial-derivative calculus is needed.
3. For each of the finitely many generating relations `t`, the first
   identity gives `ρ(γ̃₀ t) = 0`. Hence `g^m γ̃₀ t = 0` for a uniform `m`.
4. By the second identity, `γ̃_j` kills every relation once `j ≥ m`, and it
   descends along `π` by `AlgHom.liftOfSurjective`.

## Fibre ring

`fibreRing ι J` is the subring of `R × (ι → R)` of tuples `(a₀, (aₖ))` with
every `aₖ - a₀ ∈ J`.
- `fibreFst` and `fibreEval k` are its coordinate ring maps.
- `fibreRing_hom_ext` says that maps into it are determined by their
  coordinates.
- `fibreLift` is the tuple map of a family `φ₀, φₖ` agreeing modulo `J`.
- `fibreComb` is `affComb` of the coordinates.
- `fibreComb_comp_fibreLift` says that composing gives `affComb` of the
  family.

This ring is used to prove that affine combinations of lifts do not depend
on the affine chart used to compute them (`Chart.comb_eq` in
`SmoothLifting.Charts`).

## Localization facts

For `C[1/c] = Rc` and `C[1/(c e)] = Rce` with a `C`-algebra map
`ρ : Rc → Rce`:
- `away_ker_torsion` says that the kernel of `ρ` is `e`-power torsion;
- `away_map_surj` says that every element of `(I Rc).map ρ = I Rce`
  becomes, after multiplication by a power of `e`, the image of an element
  of `I Rc`.

These are hypotheses `h1` and `h2` of `exists_extension` for restriction
between basic opens. `isUnit_algebraMap_left_of_away` records that `c` is a
unit in `C[1/(c e)]`.

## Provenance

These are internal lemmas written for this proof. They are standard
commutative algebra: affine combinations of lifts form a torsor under
derivations into a square-zero ideal, and finitely presented algebras
interact with localization in the usual way. The presentation-based
extension argument replaces the Stacks Project's use of the module of
differentials. Worker 496 wrote the Lean code and this description.

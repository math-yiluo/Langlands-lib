# The normalization cover of a finite-type integer algebra

Author: Worker 5067.

Helper module for the proof of
`Langlands.AlgebraicGeometry.Picard.FiniteTypeAbelianPicardSheafSchemeReductionStatement`
(Task 5600). All declarations are in namespace
`Langlands.AlgebraicGeometry.NoetherianApproximation.MinimalPrimeNormalization`.

For a commutative ring `R : Type u` and an ideal `p`, write `(R ⧸ p)^ν` for the integral
closure of `R ⧸ p` in its fraction ring. The module builds the morphism
`∐_p Spec (R ⧸ p)^ν ⟶ Spec R` over the minimal primes `p` of `R`. It proves that this
morphism is surjective, and finite when `R` is of finite type over `ℤ`. It also shows that
each `(R ⧸ p)^ν` is an integrally closed domain of finite type over `ℤ`.

## Declarations

- `pi_ringHom_finite f hf`: if `ι : Type u` is finite and every `f i : R →+* B i` is
  finite, then `RingHom.pi f : R →+* Π i, B i` is finite. Proof: make each `B i` an
  `R`-algebra by `f i`. Mathlib then shows that a finite product of finite modules is
  finite.
- `Normalization R p := integralClosure (R ⧸ p) (FractionRing (R ⧸ p))`, an `abbrev`.
  It is a subalgebra of a field, so it is a domain.
- `toNormalization R p : R →+* Normalization R p`, the quotient map followed by the
  inclusion `R ⧸ p → (R ⧸ p)^ν`.
- `cover R`: the morphism of schemes
  `(∐ p : minimalPrimes R, Spec (Normalization R p)) ⟶ Spec R` whose component at `p` is
  `Spec.map (toNormalization R p)` (Mathlib `Sigma.desc`). The simp lemma `ι_cover R p`
  records this component.
- For a prime `p`: an instance `IsIntegrallyClosed (Normalization R p)`, from Mathlib's
  `integralClosure.isIntegrallyClosedOfFiniteExtension` applied to the fraction field of
  `R ⧸ p`.
- `toNormalization_finite p`: if `R` is of finite type over `ℤ` and `p` is prime, then
  `toNormalization R p` is finite. Proof: `R ⧸ p` is a domain of finite type over `ℤ`.
  The published theorem
  `Langlands.AlgebraicGeometry.NoetherianApproximation.integerFiniteTypeNormalization`
  says that its normalization is a finite `R ⧸ p`-module. Compose with the surjective,
  hence finite, quotient map.
- `normalization_finiteType p`, and an instance for the canonical `ℤ`-algebra structure
  `Ring.toIntAlgebra`: `(R ⧸ p)^ν` is of finite type over `ℤ` as a composite of a finite
  map and a finite-type map. The instance is stated for `Ring.toIntAlgebra` so that it
  applies to binders `[Algebra.FiniteType ℤ R]` taken with the canonical structure. The two
  structures agree because `ℤ`-algebra structures are unique (`Subsingleton.elim`).
- `exists_comap_toNormalization_eq p q hpq`: every prime `q ⊇ p` of `R` is the contraction
  of a prime of `(R ⧸ p)^ν`. Proof: the image `P` of `q` in `R ⧸ p` is prime. The zero
  ideal of `(R ⧸ p)^ν` contracts to `0 ⊆ P`, because `R ⧸ p → Frac(R ⧸ p)` is injective.
  Going up for the integral extension `R ⧸ p → (R ⧸ p)^ν`
  (`Ideal.exists_ideal_over_prime_of_isIntegral`) then gives a prime `Q` over `P`, and `Q`
  contracts to `q`.
- `cover_surjective R`: `cover R` is surjective. Every prime `x` of `R` contains a minimal
  prime `p` (`Ideal.exists_minimalPrimes_le`). The previous lemma gives a point of the
  `p`-component over `x`.
- An instance `Finite (minimalPrimes R)` for `R` of finite type over `ℤ`: such `R` is
  Noetherian, and a Noetherian ring has finitely many minimal primes.
- `cover_isFinite R`: for `R` of finite type over `ℤ`, `cover R` is a finite morphism.
  Proof: `cover R` factors as Mathlib's `sigmaSpec`, from `∐ Spec B_p` to
  `Spec (Π_p B_p)`, followed by `Spec.map` of `RingHom.pi toNormalization`. Since the index
  set is finite, `sigmaSpec` is an isomorphism, hence finite. The second map is finite by
  `IsFinite.SpecMap_iff`, `pi_ringHom_finite` and `toNormalization_finite`.

## Mathematical content

For a Noetherian ring `R` with finite normalizations, the disjoint union of the
normalizations of the reduced irreducible components `R ⧸ p` is a finite surjective cover
of `Spec R`. This is the normalization of `Spec R_red` used in Faltings–Chai, Chapter I,
proof of Theorem 1.9 (printed pp.6–7). Finiteness of normalization for finite-type
`ℤ`-domains is the only external input. It is the published theorem
`integerFiniteTypeNormalization`, which proves
`IntegerFiniteTypeNormalizationStatement`.

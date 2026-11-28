# Finite `ℓ`-primary classes of degree two die in `ℓ`-power cyclotomic extensions

Module: `Langlands.GaloisCohomology.CyclotomicKilling.FiniteModuleStatement`.

The module states one proposition, `NumberFieldFiniteModuleCyclotomicKillingStatement`, and
does not prove it.

## The statement

```lean
def NumberFieldFiniteModuleCyclotomicKillingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (A : Rep.{u} (ULift.{u} ℤ) (Ω ≃ₐ[K] Ω)) [IsSmoothRep A] [Finite A]
    (ℓ a : ℕ), ℓ.Prime → (∀ x : A, ℓ ^ a • x = 0) → ∀ β : cohomology A 2,
      ∃ r : ℕ, ∀ E : IntermediateField K Ω, (∃ ζ : Ω, ζ ∈ E ∧ IsPrimitiveRoot ζ (ℓ ^ r)) →
        (res A E.fixingSubgroup 2).hom β = 0
```

Let `K` be a number field and `Ω` a separable closure of `K`, both in the universe `u`, and
let `Γ = Gal(Ω/K)` with its Krull topology. Let `A` be a finite discrete `Γ`-module
(`IsSmoothRep A`: every element has an open stabilizer), written additively with scalars
`ULift ℤ`, and suppose that `A` is killed by `ℓ ^ a` for a prime `ℓ`. Then for every class
`β ∈ H²(Γ, A)` there is `r` such that the restriction of `β` to `Gal(Ω/E)` is zero for every
intermediate field `E` of `Ω/K` that contains a primitive `ℓ ^ r`-th root of unity.

Conventions:

- `cohomology A 2` is `H²(Γ, A)` in the Library's model of locally constant inhomogeneous
  cochains (module `Langlands.Cohomology.Profinite.Cochains`).
- `E.fixingSubgroup` is Mathlib's subgroup of `Γ` fixing `E` pointwise, that is `Gal(Ω/E)`,
  and `res A E.fixingSubgroup 2` is the Library's restriction map
  `H²(Γ, A) → H²(Gal(Ω/E), A)` (module `Langlands.Cohomology.Profinite.Functoriality`).
- An intermediate field contains a primitive `ℓ ^ r`-th root of unity exactly when it
  contains the cyclotomic field `K(μ_{ℓ ^ r}) ⊆ Ω`, so the conclusion says that the
  restriction of `β` to `Gal(Ω/K(μ_{ℓ ^ r}))` vanishes; restriction to every smaller
  subgroup then vanishes as well. For `r = 0` every intermediate field qualifies.

## Source

J.-P. Serre, *Galois Cohomology* (corrected second printing 2002), registered as
`serre-1997-galois-cohomology`:

- Chapter II, §3.3(d), Proposition 9, printed p. 81 (PDF p. 88): an algebraic extension `k`
  of `ℚ` has `cd_p(G_k) ≤ 1` when the exponent of `p` in the local degree of `k` at every
  ultrametric place is infinite and either `p ≠ 2` or `k` is totally imaginary.
- Chapter I, §2.2, Proposition 8, printed p. 11 (PDF p. 19): the cohomology of a projective
  limit of profinite groups with coefficients in an inductive limit of discrete modules is
  the inductive limit of the cohomology groups.
- Chapter I, §3.1, the definition of `cd_p`: `cd_p(G) ≤ n` when the `p`-primary component of
  `H^q(G, A)` vanishes for every `q > n` and every discrete torsion `G`-module `A`.

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory`, §6.5, Proposition 6.20, printed
p. 341 (PDF p. 351): for a number field `K` and a set of primes `Π`, the field `K_Π` obtained
by adjoining all roots of unity whose orders have only prime factors in `Π` has
`cd_p(K_Π) ≤ 1` for every `p ∈ Π`.

## Derivation of the statement

Let `K_{ℓ^∞} ⊆ Ω` be the union of the fields `K(μ_{ℓ ^ r})`. It satisfies the hypotheses of
Serre's Proposition 9 for the prime `ℓ`: at every finite place the local degrees of the
fields `K(μ_{ℓ ^ r})` have unbounded `ℓ`-adic valuation, and when `ℓ = 2` the field `K_{2^∞}`
contains a primitive fourth root of unity, so it is totally imaginary (for odd `ℓ` Serre's
proposition needs no condition at the infinite places). This is Platonov–Rapinchuk's
Proposition 6.20 for `Π = {ℓ}`. Hence `cd_ℓ(Gal(Ω/K_{ℓ^∞})) ≤ 1`, and since `H²(Gal(Ω/K_{ℓ^∞}), A)` is killed by
`ℓ ^ a`, it is zero. The group `Gal(Ω/K_{ℓ^∞})` is the projective limit (the intersection) of
the decreasing open subgroups `Gal(Ω/K(μ_{ℓ ^ r}))`, so by Serre's Proposition 8
`H²(Gal(Ω/K_{ℓ^∞}), A)` is the inductive limit of the groups `H²(Gal(Ω/K(μ_{ℓ ^ r})), A)` under
restriction. The restriction of `β` therefore vanishes already on some
`Gal(Ω/K(μ_{ℓ ^ r}))`, hence on `Gal(Ω/E)` for every `E` containing `K(μ_{ℓ ^ r})`.


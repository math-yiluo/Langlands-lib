# Torsion classes with coefficients in `Ωˣ ⊗ X` die in cyclotomic extensions

Module: `Langlands.GaloisCohomology.CyclotomicKilling.UnitsLatticeStatement`.

The module states one proposition, `NumberFieldUnitsLatticeCyclotomicSplittingStatement`, and
does not prove it.

## The statement

```lean
def NumberFieldUnitsLatticeCyclotomicSplittingStatement : Prop :=
  ∀ (K : Type u) [Field K] [NumberField K] (Ω : Type u) [Field Ω] [Algebra K Ω]
    [IsSepClosure K Ω] (X : Rep.{u} (ULift.{u} ℤ) (Ω ≃ₐ[K] Ω)) [IsSmoothRep X]
    [Module.Free (ULift.{u} ℤ) X] [Module.Finite (ULift.{u} ℤ) X]
    (c : (Ω ≃ₐ[K] Ω) → ↑(unitsModule K Ω ⊗ X)), IsLocallyConstant c →
    (∀ σ τ : Ω ≃ₐ[K] Ω, c (σ * τ) = c σ + (unitsModule K Ω ⊗ X).ρ σ (c τ)) →
    ∀ m : ℕ, 0 < m →
      (∃ b : ↑(unitsModule K Ω ⊗ X), ∀ σ, m • c σ = (unitsModule K Ω ⊗ X).ρ σ b - b) →
      ∃ N : ℕ, 0 < N ∧ (∀ q : ℕ, q.Prime → q ∣ N → q ∣ m) ∧
        ∀ E : IntermediateField K Ω, (∃ ζ : Ω, ζ ∈ E ∧ IsPrimitiveRoot ζ N) →
          ∃ b : ↑(unitsModule K Ω ⊗ X),
            ∀ σ ∈ E.fixingSubgroup, c σ = (unitsModule K Ω ⊗ X).ρ σ b - b
```

Let `K` be a number field and `Ω` a separable closure of `K`, both in the universe `u`, and
let `Γ = Gal(Ω/K)` with its Krull topology. Let `X` be a discrete `Γ`-module over `ULift ℤ`
(`IsSmoothRep X`: every element has an open stabilizer) that is free of finite rank, a
`Γ`-lattice. Let `c : Γ → Ωˣ ⊗ X` be a locally constant `1`-cocycle, and suppose that its
class is killed by some `m > 0`. Then there is `N > 0`, each of whose prime factors divides
`m`, such that for every intermediate field `E` of `Ω/K` containing a primitive `N`-th root
of unity the restriction of `c` to `Gal(Ω/E)` is a coboundary.

Conventions:

- `unitsModule K Ω` is `Ωˣ`, written additively, with the Galois action
  (module `Langlands.GaloisCohomology.Field.Modules`), and `unitsModule K Ω ⊗ X` is the tensor
  product over `ULift ℤ` in Mathlib's monoidal category `Rep`, on which `σ` acts by
  `u ⊗ x ↦ σ(u) ⊗ σ(x)`.
- A `1`-cocycle satisfies `c(στ) = c(σ) + σ·c(τ)`, and the coboundary of `b` is
  `σ ↦ σ·b − b`; these are the conventions of Mathlib's `groupCohomology` in degree one.
  Locally constant cocycles modulo coboundaries form `H¹(Γ, Ωˣ ⊗ X)` in the sense of
  continuous cochains (Serre, *Galois Cohomology*, Chapter I, §2.2). The hypothesis that
  `m • c` is a coboundary says that the class of `c` is killed by `m`.
- `E.fixingSubgroup` is Mathlib's subgroup of `Γ` fixing `E` pointwise, that is `Gal(Ω/E)`.
  An intermediate field contains a primitive `N`-th root of unity exactly when it contains
  the cyclotomic field `K(μ_N) ⊆ Ω`. If `c` is already a coboundary one may take `N = 1`.

For a torus `T` over `K`, the group `T(Ω)` with its Galois action is `Ωˣ ⊗ X_*(T_Ω)`: the
Library's `Langlands.GroupScheme.TorusPointsTensorGalois.tensorPointIso` identifies
`unitsRepresentation ⊗ latticeRepresentation` with the point representation of `T` over a
field over which `T` splits. The statement is therefore the Galois-cohomological form of
the splitting of torsion classes of `H¹(K, T)` in cyclotomic extensions; every `Γ`-lattice
`X` is the cocharacter lattice of a torus, but the statement does not use this.

## Source

V. Platonov and A. Rapinchuk, *Algebraic Groups and Number Theory* (1994), registered as
`platonov-rapinchuk-1994-algebraic-groups-number-theory` (printed page `p` is PDF page
`p + 10`), §6.5, printed p. 341:

- Proposition 6.20: for a number field `K` and a set of primes `Π`, let `K_Π` be the field
  obtained by adjoining to `K` all roots of unity whose orders have only prime factors in
  `Π`. Then `cd_p(K_Π) ≤ 1` for every `p ∈ Π`.
- Lemma 6.20: if `cd_p(K) ≤ 1`, then `H¹(K, T)` has no `p`-torsion for every `K`-torus `T`.
  The proof uses the Kummer sequence `1 → S_p → S → S → 1` of a torus `S` to show that
  `H²(K, S)` has no `p`-torsion, and an exact sequence `1 → S → F → T → 1` with `F`
  quasi-split, for which `H¹(K, F) = 1`.

J.-P. Serre, *Galois Cohomology* (corrected second printing 2002), registered as
`serre-1997-galois-cohomology`: Chapter II, §3.3(d), Proposition 9, printed p. 81 (PDF
p. 88), to which Platonov–Rapinchuk refer for Proposition 6.20; and Chapter I, §2.2,
Proposition 8, printed p. 11 (PDF p. 19), on the cohomology of projective limits.

## Derivation of the statement

Let `Π` be the set of prime divisors of `m` and `K_Π ⊆ Ω` the union of the fields `K(μ_N)`
for `N > 0` with prime factors in `Π`. For `p ∈ Π`, Proposition 6.20 gives
`cd_p(Gal(Ω/K_Π)) ≤ 1`. The argument of Lemma 6.20 applies to `Ωˣ ⊗ X`: write `X` as a quotient
of a permutation lattice `P` with kernel a lattice `Y`; then `H¹` of `Ωˣ ⊗ P` vanishes on
every open subgroup by Shapiro's lemma and Hilbert's theorem 90, `Ωˣ ⊗ Y` has the Kummer
sequence `0 → μ_p ⊗ Y → Ωˣ ⊗ Y → Ωˣ ⊗ Y → 0`, and so the restriction of `H¹(Γ, Ωˣ ⊗ X)` to
`Gal(Ω/K_Π)` has no `p`-torsion. As the class of `c` is killed by `m`, its restriction to
`Gal(Ω/K_Π)` is zero. The group `Gal(Ω/K_Π)` is the projective limit of the open subgroups
`Gal(Ω/K(μ_N))`, so by Serre's Proposition 8 the restriction of the class of `c` is already
zero on some `Gal(Ω/K(μ_N))`, that is, `c` restricted to this subgroup is a coboundary, and
then also on `Gal(Ω/E)` for every `E ⊇ K(μ_N)`.

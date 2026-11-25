# Arithmetic Artin lifts in the absolute Galois group of a local field

Module `Langlands.ClassFieldTheory.Local.Artin.ArtinLift`, name space
`Langlands.ClassFieldTheory.Local.Artin`. This file belongs to the Library.

Let `K` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`) and `Ksep` a field
extension of `K` (in the applications a separable closure). An element `σ ∈ Gal(Ksep/K)` is an
**arithmetic Artin lift** of `a ∈ Kˣ` (`IsArithmeticArtinLift K Ksep a σ`) when, for every finite
abelian intermediate field `L` of `Ksep / K`, the restriction of `σ` to `L` is the arithmetic Artin
symbol `arithmeticFiniteArtin K L a` of `FiniteArtin.lean`. Equivalently, `σ` restricts on the
maximal abelian extension `Kᵃᵇ` to the image of `a` under the arithmetic reciprocity map
`Kˣ → Gal(Kᵃᵇ/K)` (Serre's `(a, */K)`); the notion describes that image through its finite
restrictions, without constructing the profinite map. It is the notion in which the cup symbol of
local Galois cohomology is stated (`Langlands/GaloisCohomology/Local/CupSymbol.lean`).

- The defining property holds for every finite abelian extension `L` of `K` with a `K`-embedding
  into `Ksep`, not only for subfields (`IsArithmeticArtinLift.restrictNormalHom_eq`).
- Lifts multiply: `1` lifts `1`; if `σ` lifts `a` and `τ` lifts `b`, then `στ` lifts `ab` and `σ⁻¹`
  lifts `a⁻¹`.
- **Existence** (`exists_isArithmeticArtinLift`): if `Ksep / K` is Galois, every `a ∈ Kˣ` has an
  arithmetic Artin lift.

## Main declarations

`K : Type u` with `[Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]`,
`Ksep : Type v` with `[Field Ksep] [Algebra K Ksep]`.

```lean
def IsArithmeticArtinLift (a : Kˣ) (σ : Gal(Ksep/K)) : Prop :=
  ∀ (L : IntermediateField K Ksep) [FiniteDimensional K L] [IsAbelianGalois K L],
    AlgEquiv.restrictNormalHom L σ = arithmeticFiniteArtin K L a

theorem IsArithmeticArtinLift.restrictNormalHom_eq {a : Kˣ} {σ : Gal(Ksep/K)}
    (h : IsArithmeticArtinLift K Ksep a σ)
    (L : Type w) [Field L] [Algebra K L] [Algebra L Ksep] [IsScalarTower K L Ksep]
    [FiniteDimensional K L] [IsAbelianGalois K L] :
    AlgEquiv.restrictNormalHom L σ = arithmeticFiniteArtin K L a
theorem IsArithmeticArtinLift.one : IsArithmeticArtinLift K Ksep 1 1
theorem IsArithmeticArtinLift.mul {a b : Kˣ} {σ τ : Gal(Ksep/K)}
    (ha : IsArithmeticArtinLift K Ksep a σ) (hb : IsArithmeticArtinLift K Ksep b τ) :
    IsArithmeticArtinLift K Ksep (a * b) (σ * τ)
theorem IsArithmeticArtinLift.inv {a : Kˣ} {σ : Gal(Ksep/K)} (ha : IsArithmeticArtinLift K Ksep a σ) :
    IsArithmeticArtinLift K Ksep a⁻¹ σ⁻¹

theorem exists_isArithmeticArtinLift [IsGalois K Ksep] (a : Kˣ) :
    ∃ σ : Gal(Ksep/K), IsArithmeticArtinLift K Ksep a σ
```

## Proofs

- For an embedded `L`, its image `L'` in `Ksep` is a finite abelian subfield isomorphic to `L`; the
  tower `K ⊆ L ⊆ L'` (`L → L'` the isomorphism) and the compatibility of the Artin maps with
  restriction (`restrictNormalHom_arithmeticFiniteArtin`) give the claim.
- Existence. For each finite abelian subfield `L`, the set of `σ` restricting to the Artin symbol on
  `L` is closed (restriction is continuous to the discrete group `Gal(L/K)`) and nonempty
  (restriction is onto). The family is directed: the set for the compositum `L₁ ⊔ L₂` (finite and
  abelian, Mathlib's `IsAbelianGalois.sup`) lies in the sets for `L₁` and `L₂`, by compatibility
  with restriction. `Gal(Ksep/K)` is compact (Krull topology), so the intersection is nonempty.

## Sources

- J.-P. Serre, *Local Fields*, chapter XIII, §4, Proposition 12 and the definition of `(x, */E)`
  following it (the reciprocity map to the Galois group of the maximal abelian extension, by
  compatibility of the finite symbols), p. 197.
- J. S. Milne, *Class Field Theory* (version 4.03), chapter I, §1, Theorem 1.1, p. 20.

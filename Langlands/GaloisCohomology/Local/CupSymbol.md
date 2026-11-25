# The cup symbol of local Galois cohomology

`Langlands/GaloisCohomology/Local/CupSymbol.lean`, namespace `Langlands.GaloisCohomology.Local`.

Let `K` be a nonarchimedean local field (Mathlib's `IsNonarchimedeanLocalField`, any
characteristic), `Ksep` a separable closure, `G = Gal(Ksep/K)`, and `inv = invariant K Ksep :
H²(G, Ksepˣ) ≃ ℚ/ℤ` the local invariant (`Invariant.lean`, the Library's `localBrauerInvariant`
through `Br(K) ≅ H²`).

**The cup symbol** (`invariant_characterClass_cup`). For a character `χ : G → ℚ/ℤ` with open kernel,
`a ∈ Kˣ` and an arithmetic Artin lift `σ ∈ G` of `a` (`IsArithmeticArtinLift K Ksep a σ`: `σ`
restricts to the arithmetic Artin symbol of `a` on every finite abelian subextension,
`ClassFieldTheory/Local/Artin/ArtinLift.lean`; lifts exist, `exists_isArithmeticArtinLift`),

  `inv(δχ ∪ a) = χ(σ)`,

where `δχ ∪ a = characterCup K Ksep χ hχ a` (`CharacterCup.lean`). The normalization is
arithmetic: a uniformizer goes to the arithmetic Frobenius.

**The unramified form** (`invariant_characterCup_unramified`). Let `E` be a finite Galois
intermediate field of Mathlib's `SeparableClosure K` with `ArithmeticUnramified K E` (the Library's
unramified stages), embedded in `Ksep` by any `K`-algebra map, and `ψ` a character of `Gal(E/K)`,
read on `G` through restriction (`restrictCharacter K Ksep E ψ`). Then

  `inv(δψ ∪ a) = ord(a) · ψ(Frob_E)`,

with `Frob_E = finiteUnramifiedFrobenius K E hE` the arithmetic Frobenius and `ord` the Library's
`normalizedUnitOrder K`.

**Unramified classes** (`invariant_unramified`). The invariant of a class inflated from such a stage
(in the cochain model: `isoGroupCohomology⁻¹` and the map `unitsTowerMap` along restriction and the
inclusion of units, which is the Library's `relativeToContinuous`,
`Field/RelativeInflation.lean`) is the Library's unramified invariant
`spectralUnramifiedInvariant K E hE` of the relative class (Serre's: valuation, inverse connecting
map, value at the arithmetic Frobenius).

## Main declarations

```lean
-- K Ksep : Type u, [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
-- [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep];
-- E : IntermediateField K (SeparableClosure K), [FiniteDimensional K E] [IsGalois K E]
-- [Algebra E Ksep] [IsScalarTower K E Ksep]
theorem invariant_unramified (hE : ArithmeticUnramified K E) (x : relativeCohomology K E 2) :
    invariant K Ksep ((unitsTowerMap K E Ksep 2).hom
        ((isoGroupCohomology (unitsModule K E) 2).inv.hom x)) =
      spectralUnramifiedInvariant K E hE x

-- the same K Ksep : Type u
abbrev restrictCharacter (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) :
    Gal(Ksep/K) →* Multiplicative RationalModIntegers :=
  ψ.comp (normalKrullRestriction K E Ksep).toMonoidHom
theorem isOpen_ker_restrictCharacter (ψ) :
    IsOpen ((restrictCharacter K Ksep E ψ).ker : Set Gal(Ksep/K))

theorem invariant_characterCup_unramified (hE : ArithmeticUnramified K E)
    (ψ : Gal(E/K) →* Multiplicative RationalModIntegers) (a : Kˣ) :
    invariant K Ksep (characterCup K Ksep (restrictCharacter K Ksep E ψ)
        (isOpen_ker_restrictCharacter K Ksep E ψ) a) =
      normalizedUnitOrder K (.ofMul a) • (ψ (finiteUnramifiedFrobenius K E hE)).toAdd

theorem invariant_characterClass_cup (K Ksep : Type u) [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [Field Ksep] [Algebra K Ksep] [IsSepClosure K Ksep]
    (χ : Gal(Ksep/K) →* Multiplicative RationalModIntegers) (hχ : IsOpen (χ.ker : Set Gal(Ksep/K)))
    (a : Kˣ) (σ : Gal(Ksep/K)) (hσ : IsArithmeticArtinLift K Ksep a σ) :
    invariant K Ksep (characterCup K Ksep χ hχ a) = (χ σ).toAdd
```

## Declarations, in order

- `invariant_unramified`.
- The Frobenius character of an unramified stage of degree `n`: `frobeniusCharacter K E hE`
  (value `1/n` at `Frob_E`, through the Library's cyclic coordinate
  `finiteUnramifiedCyclicCoordinate`), `toAdd_frobeniusCharacter`, `reprIco_frobeniusCharacter`,
  `toAdd_frobeniusCharacter_frobenius`; `restrictCharacter`, `isOpen_ker_restrictCharacter`,
  `restrictCharacter_pow`; `unitInclusion_baseUnit`; the local instance `finrankNeZero`.
- `charCocycle_restrictCharacter_frobeniusCharacter`: the standard cocycle of the Frobenius
  character is the carry cocycle `cyclicCarry` of the Library's `cyclicClass`;
  `characterCup_frobeniusCharacter`: `δψ₀ ∪ a` is the inflation of `cyclicClass K E coord a`;
  `invariant_characterCup_frobeniusCharacter`: its invariant is `ord(a)/n`.
- `invariant_characterCup_unramified`.
- `finiteDimensional_fixedField_ker`, `restrictNormalHom_fixedField_ker_eq_one`,
  `isAbelianGalois_fixedField_ker`: the fixed field `L_χ` of `ker χ` is finite abelian, and the
  kernel acts trivially on it.
- `characterCup_eq_zero_of_isArithmeticArtinLift`: if `χ(σ) = 0` for a lift `σ` of `a`, then
  `δχ ∪ a = 0`; `invariant_characterCup_restrictCharacter_of_isArithmeticArtinLift`: the unramified
  form with `ψ(σ|_E)`.
- `invariant_characterClass_cup`.

## Proofs

- `invariant_unramified`. The relative class is the class of a central simple algebra `A` split over
  `E` by a chart `e` (`exists_relativeClass_eq`); the Library's Brauer isomorphism takes `[A]` to the
  inflated class for any separable closure (`brauerContinuousEquiv_at_chart`), so the class in the
  cochain model is `brauerEquiv K Ksep [A]`, whose invariant is `localBrauerInvariant K [A]`
  (`invariant_brauerEquiv`), computed on the chart (`localBrauerInvariant_at_chart`).
- Unramified cup symbol. For the Frobenius character `ψ₀` (`ψ₀(Frob^k) = k/n`) the representatives
  are `r(ψ₀(g)) = val(coord g)/n ∈ [0, 1)`, so `c_{ψ₀}(g, h) = ⌊(val g + val h)/n⌋`, the carry
  `cyclicCarry` of the Library's explicit cyclic cocycle. Hence `δψ₀ ∪ a` is the inflation of
  `cyclicClass K E coord a` (`exists_cocycle_relativeToContinuous_H2π`), whose invariant is
  `ord(a)/n` (`invariant_unramified`, `spectralUnramifiedInvariant_cyclicClass`). Every character of
  the cyclic group `Gal(E/K)` is `ψ₀^m` with `ψ(Frob) = m/n`, and `δ(ψ₀^m) ∪ a = m · (δψ₀ ∪ a)`.
- The cup symbol. `D(χ, a) = inv(δχ ∪ a) − χ(σ)` is additive in `χ` and in `a` (`CharacterCup.lean`,
  lifts multiply). If `ord(a) = d ≠ 0`: write `χ(σ) = [r]` and let `q = [r/d]`; then `d·q = χ(σ)` and
  `n·q = 0` for `n = |den(r)·d|`. On an unramified stage `E` of degree `n`
  (`exists_finiteUnramified_finrank`, embedded in `Ksep`), the character `ψ = ψ₀^m` with
  `ψ(Frob) = q` satisfies `inv(δψ ∪ a) = d·q = ψ(σ|_E)` (unramified form and
  `σ|_E = Frob_E^d`, `arithmeticFiniteArtin_eq_finiteUnramifiedFrobenius_zpow`). The character
  `χ' = χψ⁻¹` has `χ'(σ) = 0`, so `σ` acts trivially on the fixed field `L'` of `ker χ'`, the Artin
  symbol of `a` for `L'/K` is trivial, `a` is a norm from `L'` (`arithmeticFiniteArtin_ker`), and
  `δχ' ∪ a = 0` (`characterCup_eq_zero_of_exists_norm`). Thus `D(χ, a) = D(χ', a) + D(ψ, a) = 0`. If
  `ord(a) = 0`, let `π` be a uniformizer with a lift `τ` (`exists_isArithmeticArtinLift`); then
  `στ` lifts `aπ`, both `aπ` and `π` have order one, and `D(χ, a) = D(χ, aπ) − D(χ, π) = 0`.

## Source and licence

New file. In the statement the character carries its openness proof into `characterCup`, and the
Artin lift is named by its normalization (`IsArithmeticArtinLift`). The repository
`leanprover-community/riemann-hypothesis` (commit `f1f6d65`) proves the cup symbol from its own
reciprocity (`PC/LocalClassFormation/CupSymbol*.lean`); the proofs here are new, on the Library's
invariant and the general local Artin map of the NYLL library.

## References

- J.-P. Serre, *Local Fields*, chapter XIV, §1, Proposition 3: `(χ, b)_v = inv(b · δχ) = χ(s_b)` with
  `s_b = (b, */K)`, p. 205; Proposition 1 and Corollary 1 of Proposition 2, p. 204.
- J.-P. Serre, *Local Fields*, chapter XI, §3, Proposition 2: for a class formation,
  `⟨χ, (a, F/E)⟩ = inv_E(ā · δχ)`, pp. 169–170.
- J.-P. Serre, *Local Fields*, chapter XIII, §4, Proposition 13 and its proof: for `L/K` unramified,
  `(x, L/K) = F^{v(x)}`, the image of `x · δχ` in `H²(g, ℤ)` being `v(x) · δχ`, so its invariant is
  `v(x) χ(F)`, pp. 197–198.
- J. Neukirch, *Algebraic Number Theory*, chapter V, §1, Theorem (1.3) and the local norm residue
  symbol, pp. 320–321.

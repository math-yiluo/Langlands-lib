# Proof of Stacks 07E6 (`GeometricRegularityFlatStatement`)

## Main theorem

```
theorem GeometricRegularity.geometricRegularityFlat : GeometricRegularityFlatStatement.{u}
```

(namespace `Langlands.CommutativeAlgebra.Popescu`). This is Stacks, More on Algebra, Lemma 15.36.2
(Tag 07E6), stated at a prime `q` of a geometrically regular algebra `Λ` over a field `k` of
characteristic `p > 0`. If `F ⊂ κ(q)` is a finitely generated subextension and
`φ : k[y₁, …, yₘ] → Λ` sends each `yᵢ` into `F` modulo `q` with `dȳ₁, …, dȳₘ` a basis of
`Ω_{F/k}`, then `k[y]_𝔭 → Λ_q` is flat for `𝔭 = φ⁻¹(q)`, and `Λ_q/𝔭Λ_q` is a regular local ring.
It uses only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`).

The proof is assembled in two steps:
1. `geometricRegularityFlat_of` (below) proves the statement from four Library statements.
2. Each of the four is discharged by its published proof. Three are applied in
   `geometricRegularityFlat_of_h1Injective`. The main theorem applies that to the fourth,
   `GeometricRegularityH1.geometricRegularityH1Injective` (module
   `GeometricRegularityH1InjectiveProof`, Stacks 07E5 (1) ⇒ (3)).

The development is split over three modules:
- `GeometricRegularityFlatCore`: the cotangent-space independence argument
  (`cotangent_independent`);
- `GeometricRegularityFlatTools`: auxiliary lemmas on spanning families, generators of `𝔪`,
  weak regularity from 00NQ (`isWeaklyRegular_of_linearIndependent`) and the differentials of
  `k[y]_𝔭` (`span_D_localization`);
- `GeometricRegularityFlatProof` (this module): `rsop_independent`, `flat_regular_of_rsop`,
  `kaehler_independent_of_subfield`, the conditional theorem and the main theorem.

## The conditional theorem

```
geometricRegularityFlat_of (hK3 : GeometricRegularityH1InjectiveStatement)
    (hK2 : FieldH1CotangentInjectiveStatement) (hN3 : RegularSequenceFlatStatement)
    (h00NQ : RegularLocalParametersStatement) : GeometricRegularityFlatStatement
```

Its hypotheses are four Library statements:
- 07E5 (1) ⇒ (3), injectivity of `H₁(L_{κ(q)/k}) → H₁(L_{κ(q)/Λ_q})`;
- 07E2, injectivity of `H₁(L_{L/K}) ⊗ M → H₁(L_{M/K})`;
- 07DY, flatness from regular sequences;
- 00NQ, a regular system of parameters is a regular sequence.

## Discharging the hypotheses

`geometricRegularityFlat_of_h1Injective (hK3 : GeometricRegularityH1InjectiveStatement) :
GeometricRegularityFlatStatement` applies `geometricRegularityFlat_of` to three published Library
proofs, which this module imports:
- `FieldH1.fieldH1CotangentInjective` (module `FieldH1CotangentInjectiveProof`, Stacks 07E2);
- `regularSequenceFlat` (module `RegularSequenceFlat`, Stacks 07DY);
- `regularLocalParameters` (module `RegularLocalParametersProof`, Stacks 00NQ).

`geometricRegularityFlat` then applies `geometricRegularityFlat_of_h1Injective` to the published
`GeometricRegularityH1.geometricRegularityH1Injective`, which this module also imports.

## Notation

- `A₀ = k[y]_𝔭` and `A = Λ_q`.
- `κ₀ = κ(𝔭)` and `κ = κ(q)`.
- `g : A₀ → A` is the local map `Localization.localRingHom 𝔭 q φ h𝔭`, used as an algebra.

## Steps of `geometricRegularityFlat_of`

1. **`κ₀` lands in `F`.** For a polynomial `r`, the image of `φ(r)` in `κ` lies in `F` (induction
   on `r`, using `hF`). Every element of `κ₀` is the residue of some `r/s`. So the image of `κ₀`
   in `κ` lies in `F`.
2. **Injectivity of `κ₀ ⊗ Ω_{A₀/k} → Ω_{κ₀/k}`.** `kaehler_independent_of_subfield` maps
   `Ω_{κ₀/k}` to `Ω_{F/k}` through `κ₀ → F`. With the hypothesis that the `dȳ_i` are independent
   in `Ω_{F/k}`, this shows the `dȳ_i` are independent in `Ω_{κ₀/k}`. The `1 ⊗ dy_i` span
   `κ₀ ⊗ Ω_{A₀/k}` (`span_D_localization`, `span_one_tmul`), so the map is injective.
3. **Regularity.** `Λ` is regular (`GeometricallyRegular.isRegularRing`), so `A` is regular
   local. `k[y]` is regular (Mathlib), so `A₀` is regular local.
4. **Independence in `𝔪_A/𝔪_A²`** (`rsop_independent`).
   - Choose a family `x : Fin (spanFinrank 𝔪₀) → A₀` generating `𝔪₀`.
   - Its classes span `𝔪₀/𝔪₀²`, whose dimension equals the number of elements. So they are
     independent.
   - Rewrite this independence in coefficient form with the Library lemma
     `linearIndependent_toCotangent_iff`.
   - `cotangent_independent` then makes the images in `𝔪_A/𝔪_A²` independent. It uses K3 at
     `q`, K2 for `k → κ₀ → κ`, and step 2.
5. **Conclusion** (`flat_regular_of_rsop`).
   - **Regular quotient.** The Library lemma
     `isRegularLocalRing_quotient_span_of_linearIndependent` makes `A/(g(x))` regular local.
   - **Flatness.** `x` is a regular sequence in `A₀` (00NQ). Its image is weakly regular in `A`
     (`isWeaklyRegular_of_linearIndependent`). So `A` is flat over `A₀` (07DY).
   - **Identifying the ideal.** `𝔭Λ_q = 𝔪₀A = (g(x))`, because `𝔭A₀ = 𝔪₀`
     (`Localization.AtPrime.map_eq_maximalIdeal`) and `g ∘ (k[y] → A₀) = (Λ → Λ_q) ∘ φ`.

## `kaehler_independent_of_subfield`

Let `K₀ → K` be a map of field extensions of `k` whose image lies in a subextension `F ⊂ K`. If
the images `z_i ∈ F` of `y_i ∈ K₀` have independent differentials in `Ω_{F/k}`, then the `dy_i`
are independent in `Ω_{K₀/k}`.

Proof: apply `Ω_{K₀/k} → Ω_{F/k}`, which is semilinear over the injective map `K₀ → F`.

## Relation to Stacks

The Stacks proof of 07E6 makes the same reduction: `𝔪₀/𝔪₀² ⊗ κ → 𝔪/𝔪²` is injective by the
commutative square with `H₁(L_{κ₀/k}) ⊗ κ → H₁(L_{κ/k})`. Two parts of this proof are original
to this formalization:
- the surjectivity of `H₁(L_{κ₀/k}) → 𝔪₀/𝔪₀²`, which uses the differential-basis hypothesis
  through Jacobi–Zariski;
- the flatness argument through 00NQ and 07DY.

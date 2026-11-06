# Reduction: rational points of strongly regular classes from Steinberg's class quotient

Author: Worker 1379.

## Statements

`epi_spec_field` proves that every morphism
`f : Spec E ⟶ Spec L` between spectra of fields `E`, `L` (in one universe) is
an epimorphism of schemes.

`QuasiSplitRegularClassRationalReductionStatement.{u}` says that
`QuasiSplitSteinbergQuotientStatement.{u}` implies
`QuasiSplitRegularClassRationalStatement.{u}`:

```lean
def QuasiSplitRegularClassRationalReductionStatement : Prop :=
  QuasiSplitSteinbergQuotientStatement.{u} → QuasiSplitRegularClassRationalStatement.{u}
```

- The premise `QuasiSplitSteinbergQuotientStatement` (module
  `Rational/QuasiSplitSteinbergQuotientStatement.lean`) gives, for a simply
  connected quasi-split group `G` over a field `K`, a `K`-scheme `V` and a
  `K`-morphism `ρ : G.X ⟶ V` that is conjugation invariant, whose fibres
  through strongly regular points are geometric conjugacy classes, and such
  that every `K`-point of `V` that is the image of a strongly regular point
  over some field is the image of a `K`-point of `G`. These are properties of
  Steinberg's map `ρ = (χ_1, …, χ_r)` (Steinberg 1965, 6.10). The premise is
  not proved here; it remains an explicit hypothesis.
- The conclusion is the published statement
  `QuasiSplitRegularClassRationalStatement` (Borel–Springer 1968, 8.6, for
  strongly regular classes): a strongly regular `L`-point `z` of `G`, for
  `L/K` finite Galois, whose geometric class is stable under `Gal(L/K)`, is
  conjugate over some field extension to a `K`-rational point.

Provenance: derived. The reduction statement is an internal assembly. It
follows Steinberg's use of the invariant map `ρ` in the proof of his
Theorem 1.7 (source `steinberg-1965-regular-elements-semisimple-groups`,
§§6–9, printed pp.62–77, PDF pp.15–30): a class over `k` determines a
`k`-point of `V`, which is the image of a `k`-point of `G`. Borel–Springer
(source `borel-springer-1968-rationality-properties-ii`, 8.6, printed
pp.483–484, PDF pp.41–42) extend this to arbitrary fields for regular
semisimple classes. Here the descent of the class is replaced by Galois
descent of the single point `z ≫ ρ`.

## Proof

`epi_spec_field`: write `f = Spec.map φ` (`Spec.map_surjective`) and let `E`
be an `L`-algebra through `φ`. Then `f` is the spectrum of the field extension
`L → E`, which is surjective and flat (`fieldExtension_fpqc`). Mathlib's
`Flat.epi_of_flat_of_surjective` makes it an epimorphism.

`quasiSplitRegularClassRationalReduction` proves the reduction statement. Let
`h` be the premise, and let `K`, `L`, `G`, `z`, `S`, `j` and the hypotheses
`hcent` (strong regularity) and `hstab` (Galois stability) be given. Write
`U = Over.mk (Spec L ⟶ Spec K)`. The premise gives `V`, `ρ` and the
properties `hinv` (invariance), `hsep` (strongly regular fibres are classes)
and `hrat` (rationality).

1. **`z ≫ ρ` is Galois-fixed.** Let `σ ∈ Gal(L/K)`, and let
   `σ_U : U ⟶ U` be `Spec σ` (`TorusDensity.specGal σ`) as a morphism over
   `Spec K`. `hstab σ_U` gives a field `E`, `q : U_E ⟶ U` and `g ∈ G(E)` with
   `g (q ≫ z) g⁻¹ = q ≫ σ_U ≫ z`. Invariance applied to `g` and `q ≫ z`
   gives `q ≫ σ_U ≫ z ≫ ρ = q ≫ z ≫ ρ`. On underlying scheme morphisms,
   `q.left` is an epimorphism (`epi_spec_field`) and can be cancelled. Hence
   `Spec σ ≫ (z ≫ ρ).left = (z ≫ ρ).left`.
2. **Descent of the point.** `TorusDensity.exists_rationalPoint_of_fixed`
   (Galois descent of points of any `K`-scheme along the finite Galois
   extension `L/K`) gives a rational point `v` of `V` with
   `(Spec L ⟶ Spec K) ≫ v.left = (z ≫ ρ).left`. This says
   `toUnit U ≫ v = z ≫ ρ` (checked on underlying morphisms with
   `Over.OverMorphism.ext`; the underlying morphism of `toUnit U` is
   `Spec L ⟶ Spec K`).
3. **A rational preimage.** `hrat` applied to `v`, the field `L`, the
   strongly regular point `z` and step 2 gives a `K`-point `x` of `G` with
   `x ≫ ρ = v`.
4. **Conjugacy.** Then `(toUnit U ≫ x) ≫ ρ = toUnit U ≫ v = z ≫ ρ`. `hsep`
   applied to the field `L`, `y = toUnit U ≫ x` and the strongly regular
   point `w = z` gives `E`, `q : U_E ⟶ U` and `g ∈ G(E)` with
   `g (q ≫ toUnit U ≫ x) g⁻¹ = q ≫ z`. Since `q ≫ toUnit U = toUnit U_E`
   (`comp_toUnit`), this is the required conclusion with the rational point
   `x`.

Only properties 1–3 of the premise are used. The proof never descends a
closed subscheme, and it needs no cross-section or intersection
multiplicity.

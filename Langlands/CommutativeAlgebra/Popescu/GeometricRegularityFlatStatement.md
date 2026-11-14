# Flatness from a differential basis of a residue subextension

`Langlands.CommutativeAlgebra.Popescu.GeometricRegularityFlatStatement` (universe `u`). Let `k` be a
field of characteristic `p > 0`, `Λ` a geometrically regular `k`-algebra (Library
`GeometricallyRegular k Λ`, which includes Noetherian) and `q` a prime of `Λ` with residue field
`κ(q) = q.ResidueField`. Let `F : IntermediateField k κ(q)` be finitely generated over `k`
(`F.FG`). Let `φ : k[y₁, …, y_m] → Λ` (`MvPolynomial (Fin m) k →ₐ[k] Λ`) be such that

- each `y_i` maps to an element of `F` in `κ(q)` (`hF i`);
- the differentials `d(φ(y_i) mod q) ∈ Ω_{F/k}` are linearly independent over `F` and span
  `Ω_{F/k}` (`KaehlerDifferential.D k F`), i.e. they form a basis.

Let `𝔭 = φ⁻¹(q)` (any prime `𝔭` with `h𝔭 : 𝔭 = q.comap φ`). Then

1. `k[y]_𝔭 → Λ_q` is flat: `(Localization.localRingHom 𝔭 q φ h𝔭).Flat`;
2. `Λ_q / 𝔭Λ_q` is a regular local ring, where `𝔭Λ_q` is the ideal
   `𝔭.map ((algebraMap Λ Λ_q).comp φ)`.

## Source

Stacks Project, More on Algebra, Lemma 15.36.2 (Tag 07E6), in the registered snapshots
`stacks-geometric-regularity-07E5-07E6-2026-11-14`: "Let `k` be a field of characteristic `p > 0`.
Let `(A, 𝔪, K)` be a Noetherian local `k`-algebra. Assume `A` is geometrically regular over `k`.
Let `K/F/k` be a finitely generated subextension. Let `φ : k[y₁, …, y_m] → A` be a `k`-algebra map
such that `y_i` maps to an element of `F` in `K` and such that `dy₁, …, dy_m` map to a basis of
`Ω_{F/k}`. Set `𝔭 = φ⁻¹(𝔪)`. Then `k[y₁, …, y_m]_𝔭 → A` is flat and `A/𝔭A` is regular."

## Encoding

- The lemma is stated for `A = Λ_q`, with `Λ` geometrically regular over `k`, as it is applied in
  Smoothing Ring Maps, Lemma 16.11.2 (Tag 07FH). The map `k[y] → Λ_q` is `φ` followed by
  `Λ → Λ_q`, so `φ⁻¹(𝔪_{Λ_q}) = φ⁻¹(q)`, and the localized map is Mathlib's
  `Localization.localRingHom`.
- "`dy_i` map to a basis of `Ω_{F/k}`" is encoded as linear independence plus spanning of the
  family `KaehlerDifferential.D k F ⟨φ(y_i) mod q, hF i⟩`.
- All types are in one universe `u`.

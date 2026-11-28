# Fibrewise density of a domain and its translates, by generic points

The module `Langlands.AlgebraicGeometry.StrictBirationalGroupLawRestriction.TranslationDensity`
contains the point-set part of the Library's proof
`Langlands.AlgebraicGeometry.strictBirationalGroupLawRestriction` of Bosch, Lütkebohmert and
Raynaud, *Néron Models* (1990), §5.2 Proposition 2 (printed pp. 115–117). It checks the six
density conditions of a strict birational group law
(`Langlands.AlgebraicGeometry.BirationalGroupLaw.IsStrictOn`, BLR 5.2/1) by following generic
points of fibres through the universal translations. It is stated for topological spaces and
maps, with no scheme structure.

## `isFibreGeneric_comp_iff`

For an open embedding `e : T' → T` and a map `p` on `T`,
`IsFibreGeneric (p ∘ e) u ↔ IsFibreGeneric p (e u)`: a generization of `e u` lies in the open
image of `e`, and `e` reflects specialization.

## `translation_density`

The data are spaces `Y` (for `X ×_S X`), `X` and `D` (for the domain of the law), continuous
projections `p₁, p₂ : Y → X`, open embeddings `ι, Φ, Ψ : D → Y` (the inclusion of the domain and
the universal translations `(x, y) ↦ (x, xy)` and `(x, y) ↦ (xy, y)`) and a map `m : D → X` (the
law), with

- `p₁ ∘ Φ = p₁ ∘ ι`, `p₂ ∘ Φ = m`, `p₁ ∘ Ψ = m`, `p₂ ∘ Ψ = p₂ ∘ ι`;
- a set `F ⊆ X` (the generic points of the fibres of `X` over `S`) and an open `X' ⊇ F`;
- every point of `Y` has, in its fibre under `pᵢ`, a generization generic in that fibre;
- `p₂` maps points generic in their `p₁`-fibre into `F`, and `p₁` maps points generic in their
  `p₂`-fibre into `F`;
- every point generic in its `p₁`-fibre (resp. `p₂`-fibre) over a point of `X'` lies in the
  images of `ι`, `Φ` and `Ψ`.

Let `U' = {y | p₁ y ∈ X', p₂ y ∈ X', y = ι u with m u ∈ X'}`. The conclusion is that each of
`U'`, `Φ(ι⁻¹ U')` and `Ψ(ι⁻¹ U')` contains, for `q = p₁` and for `q = p₂`, a generization with
the same image under `q` of every point `y` with `p₁ y, p₂ y ∈ X'`. These are the six clauses
`SquareFibreGenerizationDense` of `IsStrictOn` (module
`Langlands.AlgebraicGeometry.StrictBirationalGroupLaw`).

## Proof

Each condition reduces to its generic points: for `y` with `p₁ y, p₂ y ∈ X'`, take a generization
`y₀` generic in its `q`-fibre; `p₁ y₀` and `p₂ y₀` lie in the open `X'`. So it suffices that
every point `y` generic in its `q`-fibre with `p₁ y, p₂ y ∈ X'` lies in the set. By
`isFibreGeneric_comp_iff` and the four identities, for `u ∈ D`:

- `Φ u` is `p₁`-generic exactly when `ι u` is;
- `Ψ u` is `p₂`-generic exactly when `ι u` is;
- `Φ u` is `p₂`-generic exactly when `Ψ u` is `p₁`-generic (both mean `u` is generic in its
  fibre under `m`).

The six cases then follow:

1. `U'`, `p₁`: `y = ι u`; `m u = p₂ (Φ u) ∈ F` since `Φ u` is `p₁`-generic.
2. `U'`, `p₂`: `y = ι u`; `m u = p₁ (Ψ u) ∈ F` since `Ψ u` is `p₂`-generic.
3. `Φ(ι⁻¹ U')`, `p₁`: `y = Φ u`; `ι u` is `p₁`-generic, so `p₂ (ι u) ∈ F`; also
   `p₁ (ι u) = p₁ y` and `m u = p₂ y`.
4. `Φ(ι⁻¹ U')`, `p₂`: `y = Φ u`; `Ψ u` is `p₁`-generic, so `p₂ (ι u) = p₂ (Ψ u) ∈ F`; also
   `p₁ (ι u) = p₁ y` and `m u = p₂ y`.
5. `Ψ(ι⁻¹ U')`, `p₁`: `y = Ψ u`; `Φ u` is `p₂`-generic, so `p₁ (ι u) = p₁ (Φ u) ∈ F`; also
   `p₂ (ι u) = p₂ y` and `m u = p₁ y`.
6. `Ψ(ι⁻¹ U')`, `p₂`: `y = Ψ u`; `ι u` is `p₂`-generic, so `p₁ (ι u) ∈ F`; also
   `p₂ (ι u) = p₂ y` and `m u = p₁ y`.

Cases 4 and 5 are BLR's argument with the isomorphisms `Φ` and `Ψ` on `U_a = m⁻¹(a)` (printed
p. 117), in terms of generic points.

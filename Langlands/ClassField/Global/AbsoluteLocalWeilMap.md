# Local Weil groups mapped into the absolute global Weil group

Worker 8 authored this definition unit for task
`6c50b2fd-cb4a-47b3-8f5d-d464916d69fb`. All declarations lie in the namespace
`Langlands.ClassField.Global.WeilMapSystem`. The module defines when a continuous
homomorphism `θ : W_{F_v} → W_F` is a *local-to-global Weil map* at a finite place `v`.
Here `W_{F_v}` is the actual local Weil group of the completion, and `W_F` is the
projective limit `S.WeilGroup` of a supplied transitive system `S` of Weil maps (module
`Langlands.ClassField.Global.AbsoluteWeilGroup`). The condition is stated level by level
through the published predicate `RelativeWeilGroup.IsLocalRelativeWeilMap` (module
`Langlands.ClassField.Global.LocalRelativeWeilMap`). The module constructs no such map
and does not assert that one exists.

## Setting

As in `AbsoluteWeilGroup`: a class family `c`, a number field `F : Type u`, a field
`Ω : Type u` with `[Algebra F Ω]`, `h : FundamentalClass.Restriction c` and
`S : WeilMapSystem c F Ω h`. The finite Galois layers are
`K : FiniteGaloisIntermediateField F Ω`, and `W_{K/F} = RelativeWeilGroup c F K`. A finite
place of `F` is `v : Langlands.Global.FinitePlace F`. `W_{F_v}` is
`Weil.Local.localWeilGroup (padicField v)`. `FinitePlacesAbove K v` is the published type
of finite places of `K` above `v`.

## Declarations

### Conjugation and the level maps

- `S.conjMap y θ`, for a topological group `G`, `θ : G →ₜ* S.WeilGroup` and
  `y : S.WeilGroup`, is `θ` followed by conjugation by `y`
  (`conjMap_apply : S.conjMap y θ g = y * θ g * y⁻¹`).
- `S.levelHom K : S.WeilGroup →* W_{K/F}` is the homomorphism underlying the projection
  `S.toLevel K`, without a topology on the target (`levelHom_apply`).
  `continuous_levelHom` states that it is continuous for the discrete topology
  `relativeGaloisTopology F K` on `Gal(K/F)`.
- `S.conjLevelMap K x θ : G →ₜ* W_{K/F}`, for `x : W_{K/F}`, is
  `g ↦ x * S.toLevel K (θ g) * x⁻¹` (`conjLevelMap_apply`).
- `conjLevelMap_conjMap`: `S.conjLevelMap K x (S.conjMap y θ) =
  S.conjLevelMap K (x * S.toLevel K y) θ`.

**Topology on `W_{K/F}`.** The published predicate `IsLocalRelativeWeilMap` takes maps
into `W_{K/F}` with the topology built from Mathlib's Krull topology on `Gal(K/F)`. The
relative and absolute Weil group modules use the discrete topology
`relativeGaloisTopology`. Both are discrete topologies on a finite group, so they are
equal, but they are not definitionally equal. `conjLevelMap` is therefore typed with the
Krull convention. Its continuity follows from `continuous_levelHom` through the published
bridge `RelativeWeilGroup.continuous_krull_of_relativeGalois`.

### The predicate

`S.IsLocalWeilMap v θ`, for `θ : W_{F_v} →ₜ* S.WeilGroup`, states: for every finite Galois
layer `K` there are

- a place `w : FinitePlacesAbove K v`,
- a reciprocity candidate `e : LocalFactor.RankOne.ReciprocityCandidate
  (towerPadicField v w.1)`, and
- an element `x : W_{K/F}`,

such that `RelativeWeilGroup.IsLocalRelativeWeilMap v w.1 e (S.conjLevelMap K x θ)`. That
is, the composite `W_{F_v} → W_F → W_{K/F}`, followed by conjugation by `x`, satisfies the
three published conditions:

1. `e` is geometrically normalized;
2. the image in `Gal(K/F)` acts on `K` through `K → K_w → \bar{F_v}` as the Galois image of
   `W_{F_v}` does;
3. on `W_{K_w}`, the map is the inverse of `e` followed by `K_wˣ → C_K`.

### Proved properties

- `IsLocalWeilMap.conjMap`: the property is invariant under conjugation of `θ` by any
  `y : S.WeilGroup`. The witness `x` is replaced by `x * (S.toLevel K y)⁻¹`.
- `IsLocalWeilMap.exists_level`: at each layer `K` there are `w`, `e`, `x` and a map
  `ι : W_{F_v} →ₜ* W_{K/F}` with `IsLocalRelativeWeilMap v w.1 e ι` and
  `S.toLevel K (θ g) = x⁻¹ * ι g * x` for all `g`.

## Source correspondence

J. Tate, *Number theoretic background*, Proc. Sympos. Pure Math. 33, Part II (1979),
literature ID `tate-1979-number-theoretic-background`, SHA256
`c890894fe19783890cc4def2c5bf92a18d71619acf8ba7005aefce4984fe70d6`. The PDF page is the
printed page plus nine. Proposition (1.6.1), printed p.8 (PDF p.17), was read from the
original. Fix an `F`-embedding `i : \bar F → \bar F_v`, and let `E_v = i(E)F_v` for each
finite `E ⊆ \bar F`. Then there is a continuous `θ_v : W_{F_v} → W_F`. It is compatible
with `G_{F_v} → G_F` induced by `i`, and for each `E` it is compatible with
`C_{E_v} → C_E` (the map `η` putting `a` at the `v`-component) through `r_{E_v}` and
`r_E`. In the number field case `θ_v` is unique up to an inner automorphism of `W_F` by an
element of `W_F^0`. The Corollary on printed p.9 (PDF p.18) says that the diagram
`W_{F_v} → W_F` is unique up to isomorphism.

### Derived formulation

1. **Level by level.** By (W4), `W_F` is the projective limit of the `W_{E/F}`. So
   compatibility of `θ_v` with the local–global diagrams of (1.6.1) is checked on the
   composites `W_{F_v} → W_{K/F}` for the finite Galois layers `K`. The relative condition
   on these composites is the published `IsLocalRelativeWeilMap`.
2. **Inner automorphisms at each level.** The published relative predicate uses, for each
   `K` and `w`, a fixed embedding `K_w → \bar{F_v}` chosen by Mathlib. The choices for
   different layers need not be compatible. Two such embeddings of the same layer differ by
   an element of the decomposition group. Requiring the predicate for the composites
   themselves at every layer at once could therefore be unsatisfiable. The definition allows
   at each layer an inner automorphism by `x ∈ W_{K/F}`, and an existential place `w` and
   candidate `e`. Inner automorphisms change neither local components up to equivalence
   nor Frobenius characteristic polynomials. They also match the ambiguity of (1.6.1) and
   its Corollary. Tate's single embedding `i` is not formalized.
3. **Finite places only.** Like the relative predicate, the definition concerns finite
   places `v`. Archimedean places are not treated.

## Scope and remaining obligations

The following are neither proved nor assumed here. They are theorem obligations:

- existence of a local-to-global Weil map at each finite place, for a system of Weil maps
  of the arithmetic fundamental-class family (Tate (1.6.1));
- uniqueness up to conjugation by an element of `W_F`;
- comparison with Tate's formulation through a single embedding `i`.

Representations of `W_F`, their local components along such maps and weak association
are built in `Langlands.Automorphic.Unramified.AbsoluteWeilAssociation`.

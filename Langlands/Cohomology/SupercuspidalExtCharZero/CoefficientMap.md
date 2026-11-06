# Coefficient maps of a representation with compact coefficients

This derived module constructs the intertwiners used to prove the unchanged
`CompactCoefficientInjectiveProjectiveStatement` over an arbitrary field of
characteristic zero. It also collects facts about compact open subgroups and
averaging. All declarations are in `Langlands.Cohomology.SupercuspidalExtCharZero`.

## Provenance

Vignéras (1996), I.7.7, preliminary and proof of (ii), printed pages 58–59, lets a
coefficient `∫_G ⟨ṽ, g v⟩ g dμ(g)` of a compact representation `V` act on a
representation `W`. It then shows that the resulting map
`v ↦ (∫_G ⟨ṽ₀, g⁻¹ v⟩ g dμ(g)) w₀` from `V` to `W` is `G`-equivariant. Here the Haar
integral is replaced by a counting sum over the left cosets of a compact open subgroup
`U`, as in the Haar measure construction of Vignéras I.2.4 (printed pages 12–13). This
replacement and the nonvanishing argument below are derived for this project, with
the scalar positivity input taken from
`Langlands.Cohomology.SupercuspidalExtCharZero.Positivity`. Averaging over compact open
subgroups is Worker 1643's `Langlands.Compact.CharZero.averageMap` from
`Langlands.Representation.Compact.CharZeroAverage`.

## Fixed vectors

- `mem_fixedVectors_iff`: `v` is fixed by the subgroup `K` exactly when `ρ g v = v` for
  all `g ∈ K`.
- `mem_fixedVectors_dual_iff`: a functional `ℓ` is fixed by `K` under Mathlib's dual
  action `ρ.dual` exactly when `ℓ (ρ g v) = ℓ v` for all `g ∈ K` and all `v`.
- `exists_ne_zero_of_isIrreducible`: an irreducible representation has a nonzero
  vector, because `⊥ ≠ ⊤` in its lattice of subrepresentations.

## Compact open subgroups and averaging

Here `G` is a Hausdorff, locally compact, totally disconnected topological group.

- `exists_compact_openSubgroup_subset`: every neighbourhood of `1` contains a compact
  open subgroup. This is van Dantzig's theorem,
  `Langlands.Topology.LocallyProfiniteProof.vanDantzig`, applied through
  `Langlands.Topology.isLocallyProfinite_of_mathlib`.
- `exists_compact_fixing`: a smooth vector is fixed by a compact open subgroup.
- `apply_averageMap_of_invariant`: let `K` be a compact open subgroup and `φ : V → M` a
  linear map with `φ (ρ g v) = φ v` for `g ∈ K`. Then `φ` takes the same value on
  `averageMap ρ hρ K hK v` and on `v`. This follows from `orbitMean_map` and
  `orbitMean_id` of Worker 1643's module, with `M` carrying the trivial action. This
  lemma and the next two need `CharZero k`.
- `exists_dual_apply_ne_zero`: for a nonzero vector `w` of a smooth representation there
  are a compact open subgroup `K` fixing `w` and a `K`-fixed functional `ℓ` with
  `ℓ w ≠ 0`. Average an arbitrary functional that does not vanish at `w`.
- `eq_zero_of_forall_smooth_dual`: a vector annihilated by every smooth functional is
  zero.

## The coefficient map

For representations `ρ` on `V` and `σ` on `W` of a topological group `G`, a subgroup
`U`, a functional `ξ` on `V` and a vector `x` of `W`,

`coefficientMap ρ σ U ξ x v = cosetSum U (fun g => ξ (ρ g⁻¹ v) • σ g x)`.

In the following facts, `U` is open, `ξ` is `U`-invariant, `x` is fixed by `U`, and
every coefficient `g ↦ ξ (ρ g v)` has compact support. Only the hypotheses that a
lemma's statement lists are used.

- `matrixCoefficient_eq` unfolds the Library's `matrixCoefficient ρ ℓ v` to
  `fun g => ℓ (ρ g v)`.
- `map_cosetSum`: an additive map commutes with a coset sum whose summand has finite
  support on `G ⧸ U`.
- `coefficientMap_hasFiniteSupport`: the summand has finite support, because
  `g ↦ ξ (ρ g⁻¹ v)` has compact support.
- `coefficientMap_add` and `coefficientMap_smul`: the map is `k`-linear.
- `coefficientMap_rightInvariant`: the summand is right `U`-invariant.
- `map_coefficientMap`: an additive map out of `W` moves inside the sum.
- `coefficientMap_apply_rep`: `coefficientMap ρ σ U ξ x (ρ h v) =
  σ h (coefficientMap ρ σ U ξ x v)`. This uses `cosetSum_mul_left`.
- `coefficientIntertwiningMap hU hξ hc hx` packages the map as a
  `Representation.IntertwiningMap ρ σ`. `coefficientIntertwiningMap_apply` is its
  application law.
- `map_coefficientMap_intertwining`: an intertwiner `f : σ → τ` satisfies
  `f (coefficientMap ρ σ U ξ x v) = coefficientMap ρ τ U ξ (f x) v`.

## A nonzero and a bijective coefficient map

For the rest of the module `k` has characteristic zero, `G` is Hausdorff, locally
compact and totally disconnected, and `ρ` is smooth. `hc` states that
`matrixCoefficient ρ ℓ v` has compact support for every vector `v` and every smooth
functional `ℓ`. This is the shape of the Library's `HasCompactCoefficients`.

`exists_coefficientMap_ne_zero ρ hρ hc hw`: for `w ≠ 0` there are a compact open
subgroup `U`, a `U`-fixed functional `ξ` and the `U`-fixed vector `w` with
`coefficientMap ρ ρ U ξ w w ≠ 0`. The proof is as follows.

1. Choose a compact open `U₀` fixing `w` and a `U₀`-fixed `ℓ` with `ℓ w ≠ 0`. Put
   `F g = ℓ (ρ g w)`. It has compact support by `hc` and satisfies `F 1 ≠ 0`.
2. The compact set `(tsupport F)⁻¹` meets finitely many left cosets of `U₀`. With
   representatives `q`, the set of `g ∈ U₀` such that `q⁻¹ g q ∈ U₀` for all of them is
   a neighbourhood of `1`. It contains a compact open subgroup `U`. Then `F` is left and
   right `U`-invariant.
3. `exists_cosetSum_ne_zero` gives `x` and `y` with `F x⁻¹ ≠ 0` and
   `∑_{pU} F (x⁻¹ p⁻¹) F (y⁻¹ p) ≠ 0`. Since `x` lies in `(tsupport F)⁻¹`, conjugation by
   `x` sends `U` into `U₀`. Therefore `ξ = ℓ ∘ ρ x⁻¹` is `U`-invariant.
4. Applying `ℓ ∘ ρ y⁻¹` to `coefficientMap ρ ρ U ξ w w` gives exactly the nonzero sum of
   step 3.

`exists_coefficientMap_bijective ρ hρ hc`: if `ρ` is moreover irreducible, there are
`U`, `ξ` and `w` as above such that `coefficientIntertwiningMap` from `ρ` to itself is
bijective. Take a nonzero `w` and apply the previous lemma. By
`Representation.IsIrreducible.bijective_or_eq_zero`, a nonzero self-intertwiner of an
irreducible representation is bijective.

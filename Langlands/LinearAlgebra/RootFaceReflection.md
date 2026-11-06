# Reflections, restriction and integral sign patterns for root weights

Lean module: `Langlands.LinearAlgebra.RootFaceReflection`,
namespace `Langlands.LinearAlgebra.RootFaceCone` (shared with
`Langlands.LinearAlgebra.RootFaceCone`, whose `rootWeight` it uses).

## Purpose and provenance

Provenance: internal. This module supplies three abstract inputs that
`Langlands.Representation.Plancherel.ParabolicRootCone` needs before it can apply the conic
bound of `Langlands.LinearAlgebra.RootFaceCone` to the relative roots of the split component
of a parabolic. That application belongs to the convergence step of the standard intertwining
integrals (Waldspurger, *La formule de Plancherel pour les groupes p-adiques, d'après
Harish-Chandra* (2003), IV.1.1, printed pp. 278–280). Waldspurger argues by a gallery
induction instead, so no statement here is transcribed from a source. The three inputs are:

1. Levi orthogonality (`B β ρ(y) = 0` whenever `B β y = 0`) follows from the existence of
   isometric reflections. This is the standard argument that the Weyl reflection `s_β` fixes
   `y` and permutes the roots.
2. Levi orthogonality descends from a maximal split torus to a smaller split torus along a
   restriction map with a compatible lift.
3. Every real sign pattern of finitely many integral functionals is realized by an integral
   vector. This uses flatness of `ℝ` over `ℤ` and rounding.

## Setting and notation

`rootWeight B Φ m y = ∑_{α ∈ Φ, 0 < B α y} m α • α` is the definition from
`Langlands.LinearAlgebra.RootFaceCone`. It is written `ρ(y)` below.

**Reflection section.** `E` is a real vector space, `B : LinearMap.BilinForm ℝ E`,
`Φ : Finset E` and `m : E → ℝ`. Here `w : E ≃ₗ[ℝ] E` is an *isometry* when
`B (w x) (w y) = B x y` for all `x, y`.

**Descent section.** `E` and `F` are real vector spaces with forms `BT` and `BA`. Here
`q : E →ₗ[ℝ] F` is restriction and `L : F →ₗ[ℝ] E` a lift. Root families are indexed:
`RT : Finset X` with `ιT : X → E` and multiplicities `mT : X → ℝ`, and `RA : Finset Y` with
`ιA : Y → F` and `mA : Y → ℝ`. The map `res : X → Y` restricts indices. The section variables
are:

- `hcompat`: `BT (L x) y = BA x (q y)`;
- `hTsymm`, `hAsymm`: both forms are symmetric;
- `hres`: `q (ιT χ) = ιA (res χ)`;
- `hqL`: `q (L x) = x`.

**Realization section.** `N` is an additive group, a lattice in the intended use, and
`ℝ ⊗[ℤ] N` is its real scalar extension.

## Declarations

Reflection:

- `eq_self_of_isometry_neg`: let `w` be an isometry with `w β = -β` that moves every vector
  along `β` (`∀ x, ∃ t, w x = x + t • β`), and assume `β ≠ 0 → 0 < B β β`. Then `w z = z`
  whenever `B β z = 0`.
- `apply_eq_zero_of_isometry_fixed`: if `w` is an isometry with `w β = -β` and `w x = x`,
  then `B β x = 0`.
- `rootWeight_isometry_fixed`: let `w` be an isometry mapping `Φ` into `Φ` and preserving `m`
  on `Φ`. If `w z = z`, then `w ρ(z) = ρ(z)`.
- `rootWeight_levi_of_reflections`: assume `B` is positive definite and every `β ∈ Φ` has an
  isometry `w` with `w β = -β` that moves vectors along `β`, maps `Φ` into `Φ` and preserves
  `m`. Then for all `y` and `β ∈ Φ`, `B β y = 0` implies `B β ρ(y) = 0`.
- `rootWeight_image_eq`: for an injective `ι : X → E`, a finset `R` and `n : X → ℝ`,
  `rootWeight B (R.image ι) (Function.extend ι n 0) y = ∑_{χ ∈ R, 0 < B (ι χ) y} n χ • ι χ`.

Descent:

- `restrict_indexedRootWeight` (`hcompat`, `hTsymm`, `hAsymm`, `hres`): assume `res χ ∈ RA`
  for every `χ ∈ RT` with `ιA (res χ) ≠ 0`, and `mA α = ∑_{χ ∈ RT, res χ = α} mT χ` for
  `α ∈ RA`. Then `q` maps the indexed root weight of `L y` for `BT` onto the indexed root
  weight of `y` for `BA`.
- `lift_mem_span_roots` (`hres`, `hqL`): assume every `α ∈ RA` is `res χ` for some
  `χ ∈ RT`, and `ker q` lies in the span of the `ιT χ` with `χ ∈ RT` and `ιA (res χ) = 0`.
  Then for `α ∈ RA`, `L (ιA α)` lies in the span of the `ιT χ` with `χ ∈ RT` and either
  `ιA (res χ) = 0` or `res χ = α`.
- `indexedRootWeight_levi_descent` (all section variables, the hypotheses of the two previous
  items, and Levi orthogonality for `BT` on `RT` in indexed form): for `y : F` and `α ∈ RA`
  with `BA (ιA α) y = 0`, `ιA α` is `BA`-orthogonal to the indexed root weight of `y`.
- `restrict_orthogonal_roots` (`hcompat`, `hres`, `hqL`, surjectivity and kernel hypotheses):
  if `g : E` is `BT`-orthogonal to every `ιT χ` with `χ ∈ RT`, then `q g` is `BA`-orthogonal to
  every `ιA α` with `α ∈ RA`.

Realization:

- `exists_int_sign_realization`: let `s` be a finset of indices, `φ j : N →ₗ[ℤ] ℤ`, and
  `ψ j : ℝ ⊗[ℤ] N →ₗ[ℝ] ℝ` with `ψ j (t ⊗ n) = t * φ j n`. Then every `g : ℝ ⊗[ℤ] N` has some
  `μ : N` with `0 < φ j μ ↔ 0 < ψ j g` for every `j ∈ s`.

## Proofs as implemented

**Reflections.** Write `w z = z + t • β`. Isometry and `w β = -β` give `B β (w z) = -B β z`,
which is `0`. Expanding gives `t * B β β = 0`, so `t = 0` when `β ≠ 0`. If `w x = x`, then
`B β x = B (w β) (w x) = -B β x`, so `B β x = 0`. For `rootWeight_isometry_fixed`, an
injective self-map of the finite set `Φ` is onto, so `Φ.image w = Φ`. Reindex the sum by `w`.
The filter is unchanged because `B (w α) z = B α z` when `w z = z`, and so are the
multiplicities. Levi orthogonality follows by combining the three lemmas.

**Restriction.** Push the sum through `q`. By `hcompat` and symmetry,
`BT (ιT χ) (L y) = BA (ιA (res χ)) y`. Group the summands into fibres of `res`
(`Finset.sum_fiberwise_of_maps_to`): a summand with positive pairing has `ιA (res χ) ≠ 0`, so
its index lies in `RA`. The fibre sums give the multiplicities `mA α`.

**Lift.** For `α = res χ₀`, the vector `ιT χ₀ - L (ιA α)` lies in `ker q`, hence in the span
of the roots restricting to zero. Add back `ιT χ₀`.

**Descent.** Rewrite the target root weight as the restriction of the root weight of `L y`.
Then use `hcompat` to move the pairing to `BT (L (ιA α)) (·)`. By the lift lemma it suffices
to check `BT`-orthogonality for each `ιT χ` restricting to `0` or to `α`. Each such `χ` has
`BT (ιT χ) (L y) = BA (ιA (res χ)) y = 0`, so Levi orthogonality for `BT` applies.
`restrict_orthogonal_roots` uses the same span argument.

**Integral sign patterns.** Let `Z ⊆ s` be the indices with `ψ j g = 0` and
`Λ = (φ j)_{j ∈ Z} : N → ℤ^Z`. Since `ℝ` is flat over `ℤ`, tensoring the exact sequence
`ker Λ → N → ℤ^Z` with `ℝ` stays exact. The image of `g` in `ℝ ⊗ ℤ^Z ≅ ℝ^Z` is
`(ψ j g)_{j ∈ Z} = 0`, so `g` comes from `ℝ ⊗ ker Λ`. Write it as a finite sum
`∑ tᵢ ⊗ kᵢ` with `kᵢ ∈ ker Λ`. Take an integer `n` with
`n |ψ j g| > ∑ᵢ |φ j kᵢ|` for every `j ∈ s` with `ψ j g ≠ 0`, and put
`μ = ∑ᵢ ⌊n tᵢ⌋ kᵢ`. For `j ∈ Z`, `φ j μ = 0`. Otherwise `|φ j μ - n ψ j g| ≤ ∑ᵢ |φ j kᵢ|`,
because `|⌊n tᵢ⌋ - n tᵢ| ≤ 1`. So `φ j μ` has the sign of `ψ j g`.

## Scope

This module is abstract linear algebra. It does not construct the reflections or the lift for
an actual group, and it says nothing about intertwining integrals. The group-theoretic
instances are in `Langlands.Representation.Plancherel.ParabolicRootCone`.

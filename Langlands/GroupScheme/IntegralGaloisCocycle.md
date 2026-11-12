# Galois cocycles on finite free local Galois covers

Authors: Worker 5015.

This module states and proves
`Langlands.GroupScheme.IntegralGaloisCocycleVanishingStatement.{u}` at arbitrary universe
`u`. The proof is `Langlands.GroupScheme.integralGaloisCocycleVanishing`. It uses only the
axioms `propext`, `Classical.choice` and `Quot.sound`.

## The statement

Let `R : Type u` be a commutative ring and `I` a maximal ideal with `Finite (R ⧸ I)` and
`IsAdicComplete I R`. Let `H : GroupScheme (Spec R)` be smooth, with affine structure
morphism. Assume that the actual special fibre, the total space of the base change of `H`
along `Spec (R ⧸ I) → Spec R`, is a connected topological space. These are exactly the
hypotheses of the published `IntegralCocycleVanishingStatement`.

Let `B : Type u` be a local commutative `R`-algebra that is finite and free as an `R`-module.
Let `Γ : Type u` be a finite group and `ρ : Γ →* (B ≃ₐ[R] B)` an action by `R`-algebra
automorphisms. Assume:

- `Nat.card Γ = Module.finrank R B`;
- `Γ` acts faithfully on the residue field: if `residue B (ρ g x) = residue B x` for every
  `x : B`, then `g = 1`. In other words, the inertia subgroup is trivial.

The coefficient points are `H.affinePoints (CommAlgCat.of R B)`, the actual morphisms
`Spec B ⟶ H.X` over `Spec R`, with their pointwise group law. An automorphism `σ` of `B` acts
on them by `GaloisRingCover.conjugate H σ`, which precomposes with the spectrum map of `σ`.
A function `c : Γ → H(B)` satisfies `GaloisRingCover.IsCrossed ρ H c` when

```
c (σ * τ) = c σ * conjugate H (ρ σ) (c τ)   for all σ τ.
```

The conclusion is that `c` is a coboundary: there is `f : H(B)` with
`c g = f * (conjugate H (ρ g) f)⁻¹` for every `g`. This is the convention of the published
`GaloisCocycle.value_coboundary` for field covers.

## Intended application

For a finite unramified Galois extension `E/F` of nonarchimedean local fields, the triple
`(R, B, Γ) = (O_F, O_E, Gal(E/F))` satisfies these hypotheses: `O_F` is complete with finite
residue field, `O_E` is local and free of rank `[E : F]` over `O_F`, and the inertia subgroup
of `Gal(E/F)` is trivial. The module does not prove this instance; the Library facts it
would use are `spectralIntegers_free`, `spectralIntegers_finrank` and the residue-degree
criterion `inertia_le_fixingSubgroup_iff_residue_finrank`. In that case the statement says
`H¹(Gal(E/F), H(O_E)) = 1` for a smooth affine `O_F`-group `H` with connected special fibre.

## Provenance

Provenance: derived. The source is Kaletha–Prasad, *Bruhat–Tits Theory: A New Approach*
(2023), Lemma 8.1.4 and its proof, printed p.285 / PDF p.316, registered as
`kaletha-prasad-2023-bruhat-tits-new-approach`, SHA-256
`05ad9a284a2577b34d1a270228b74dfb28f520561ae7772d8f38dddb78938732`. For a smooth affine
`o`-group scheme `G` with connected fibres, it shows that `H¹(Γ, G(O))` is trivial when the
residue field has dimension at most one. There `Γ` is the Galois group of the maximal
unramified extension and `O` its ring of integers.

The present statement differs from the source as follows:

- It is at a finite level: a finite group `Γ` acting on a finite free local `R`-algebra `B`,
  instead of `Gal(K/k)` acting on `O_K`.
- It requires `R` complete with finite residue field. These are the hypotheses of the
  published torsor-point theorem `IntegralTorsorPoint.integralTorsorPoint`. The source
  allows a Henselian base whose residue field has dimension at most one.
- It does not prove the injectivity part of Lemma 8.1.4.

The proof does not follow the source's torsor language literally. It converts the crossed
homomorphism into a Library scheme cocycle and applies the published
`integralCocycleVanishing`, as described below.

## The implemented proof

1. **Galois decomposition.** `GaloisRingCover.tensorHom_bijective` shows that the
   `B`-algebra map `tensorHom ρ : B ⊗[R] B → (Γ → B)`, `x ⊗ y ↦ (g ↦ x * ρ g y)`, is
   bijective. Take an `R`-basis `b` of `B` and the `B`-basis `1 ⊗ b j` of `B ⊗[R] B`.
   After identifying the basis index with `Γ`, the matrix of `tensorHom ρ` has entries
   `ρ g (b j)`. Its determinant is a unit if its residue is nonzero. If the residue were
   zero, a nonzero vector `w` would give `∑ g, w g * residue (ρ g y) = 0` for every `y : B`,
   since `b` spans `B` over `R` and each `ρ g` is `R`-linear. The residue maps of the `ρ g`
   are pairwise distinct monoid homomorphisms of the residue field, because the action is
   faithful there. Mathlib's `linearIndependent_monoidHom` (Dedekind's independence of
   characters) then forces `w = 0`.
2. **Triple coordinates.** `GaloisRingCover.triple_ext` shows that the maps
   `tripleComponent ρ σ τ : x ⊗ (y ⊗ z) ↦ x * σ(y) * σ(τ(z))` are jointly injective on
   `B ⊗[R] (B ⊗[R] B)`. The proof factors them through `B ⊗ tensorHom` and the finite
   product decomposition `Algebra.TensorProduct.piRight`, then uses step 1 again.
3. **The overlap point.** `overlapPoint` is the point of `H` over `B ⊗[R] B` whose
   coordinates under `tensorHom ρ` are the values `c g`. It is assembled with the published
   `affinePointPi` and transported along the inverse of step 1. `overlapPoint_component`
   records that its image under the `g`-th coordinate is `c g`.
4. **The cocycle.** `Cocycle.ofOverlap` builds a Library cocycle from one morphism
   `δ : U ⊗ U ⟶ G.X` that satisfies the cocycle identity on the universal triple
   `U ⊗ (U ⊗ U)`. It sets `toFun a b = lift a b ≫ δ`. Here `U = cover R B` is the actual
   spectrum of `B` over `Spec R`, and `δ` is `overlap`: the monoidal structure map `μ` of
   Mathlib's `algSpec` (the inverse of the product comparison) followed by `overlapPoint`.
   `overlap_triple` checks the universal identity. `tripleMap` compares `U ⊗ (U ⊗ U)` with
   the spectrum of the triple tensor product. The three face maps compose with the triple
   coordinates to `component σ`, `σ ∘ component τ` and `component (σ τ)` (`face₁₂`,
   `face₂₃`, `face₁₃`). By step 2 (`triple_points_ext`) the identity reduces to the
   crossed-homomorphism identity. The resulting cocycle is `ofCrossed`, and
   `ofCrossed_toFun_arrow` shows that its value on the identity and the spectrum map of
   `ρ g` is `c g`.
5. **Vanishing.** `B` is free of positive rank, so it is faithfully flat over `R`, and
   `Spec B → Spec R` is flat and surjective (`flat_and_surjective_SpecMap_iff`). The
   published `integralCocycleVanishing` makes `ofCrossed` trivial. By
   `exists_coboundary_of_isTrivial`, evaluating a trivialization `f` on the identity and on
   the spectrum map of `ρ g` gives `c g = f * (conjugate H (ρ g) f)⁻¹`.

The local instance `algSpecBraided` restates Mathlib's `braidedAlgSpec` for the base
`CommRingCat.of R`, because instance search does not find it there.

## Scope

This module proves no part of `LocalSimplyConnectedUnramifiedCocycleVanishingStatement` or
`LocalSimplyConnectedCocycleVanishingStatement` by itself. Those still need the
Bruhat–Tits reduction of an unramified Galois cocycle to an Iwahori-valued cocycle, an Iwahori
integral model with connected fibres, and the comparison of `H(O_E)` with the generic-fibre
points.

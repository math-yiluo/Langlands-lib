# Galois action on the simple roots of a split Borel pair (Lemma Q)

Statement-only draft module for the proof of `GaloisBorelTwistingStatement` (Task 5268). It
imports only the Library module `Langlands.Global.AdelicGaloisBorelTwisting`.

Setting: `G` connected reductive over a field `F`, `L/F` finite Galois, `T₀ ⊂ G` a maximal
`F`-torus (`i₀`) whose base change `T₀_L` is split, `i = i₀_L : T₀_L → G_L`, and `ν` a generic
cocharacter of `T₀_L`, with simple roots `Δ = simpleRelativeRoots i ν`.

`galoisRootMap F L T₀ τ σ χ = (τ σ)⁻¹ ≫ σ·χ` (`characterAut (τ σ)` after
`characterLattice.galoisRepresentation σ`).

`IsGaloisRootAction F L G T₀ i ν m τ` says:

1. `(m σ)⁻¹` normalizes `i` through the automorphism `τ σ` of `T₀_L`
   (`IsNormalizingPoint`: `i ≫ int((m σ)⁻¹) = τ σ ≫ i`);
2. `a σ := galoisRootMap τ σ` maps `Δ` into `Δ`;
3. for every `J ⊆ Δ`, the canonical Galois translate of the standard parabolic `P_J`
   (`SubgroupFunctor.range (radicalGaloisHom (Standard.parabolicHom i ν J) σ)`) equals the
   image of `P_{a σ '' J}` under conjugation by `m σ`;
4. `a 1 = id` on `Δ`, and `a (σ σ') = a σ ∘ a σ'` on `Δ`.

`SplitBorelGaloisRootActionStatement`: such `m` and `τ` exist.

Intended proof (classical; cf. Borel–Tits, the `*`-action of the Galois group on the
simple roots). `σ` maps roots to roots (`mem_roots_galois_iff`), so `σ·ν` is generic, and
there is `n ∈ N(T₀_L)(L)` with `n·σ·ν` in the dominant chamber of `ν`
(`HasRelativeRootSystem.exists_normalizerPoint_dominant`); set `m σ := n⁻¹`, `τ σ` the
automorphism through which `n` normalizes `i`. Then `n·σ·ν` and `ν` have the same positive
roots, so `a σ (Δ) = Δ`. The Galois translate of `P_J = ⋂_{ζ standard for J} P(ζ)` is
`⋂ P(σζ)` (`galoisTransport_intersection`, dynamic parabolic transport), and conjugation by
`n` maps `P(σζ)` to `P(τ σ ∘ σζ)`; the cocharacters `τ σ ∘ σ ζ` are exactly the standard
cocharacters for `a σ '' J`. The action laws follow by rigidity: conjugate standard parabolics
are equal (`standardParabolic_eq_of_isRationallyConjugate_of_bruhat`) and `J ↦ P_J` is
injective on subsets of `Δ`.

Used for clause 5 (`J = Δ \ {β}`, since `a σ` is a bijection of the finite set `Δ`) and,
with `J = ∅`, for clause 4 of `IsGaloisBorelTwist`.

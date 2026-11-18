# Descent of membership in a linear range along flat pointwise covers

`mem_range_of_flat_cover` is a purely module-theoretic descent lemma. Let `R` be a commutative ring, `δ : P →ₗ[R] Q` a linear map of arbitrary `R`-modules, and `v : Q`. Suppose that for every prime `p` of `R` there is a flat `R`-algebra `K` with these two properties:

- some prime `q` of `K` contracts to `p`;
- `1 ⊗ v` lies in the range of `K ⊗ δ : K ⊗ P → K ⊗ Q`.

Then `v` lies in the range of `δ`. No finiteness, freeness or projectivity of `P` or `Q` is assumed. The algebra `K` may depend on the prime.

## Proof

The Lean proof is elementary and uses no faithful-flatness library. Suppose `v` is not in the range. Its class `x` in the cokernel `C = Q ⧸ range δ` is then nonzero. Hence the annihilator ideal `I = Ideal.torsionOf R C x` is proper, and it lies in some maximal ideal `m`. Choose `K` and `q` over `m` as in the hypothesis.

- Applying `K ⊗ (Q → C)` to a preimage of `1 ⊗ v` shows that `1 ⊗ x = 0` in `K ⊗ C`, because `mkQ ∘ δ = 0`.
- `K` is flat, so tensoring the inclusion of the cyclic submodule `R ∙ x ⊆ C` with `K` stays injective. Hence `1 ⊗ x = 0` already in `K ⊗ (R ∙ x)`.
- The cyclic module `R ∙ x` is isomorphic to `R ⧸ I` (`Ideal.quotTorsionOfEquivSpanSingleton`). Since `I ⊆ m` and `q` contracts to `m`, the algebra map `R → K ⧸ q` kills `I`. This gives an `R`-linear map `R ∙ x → K ⧸ q` sending `x` to `1`.
- The map `k ⊗ y ↦ k̄ · φ(y)` sends `1 ⊗ x` to `1`. But `1 ≠ 0` in `K ⧸ q`, because `q` is prime. This contradicts `1 ⊗ x = 0`.

## Provenance

This is an internal helper for the descent step in the proof of `MultiplicativeTypeLowDegreeVanishingStatement`. The descent step follows the flat base-change argument of Conrad, *Reductive group schemes*, Proposition B.2.2. The lemma is a standard case of faithfully flat descent: a jointly faithfully flat family of base changes detects whether an element lies in the image of a linear map. The Lean statement only asks for a pointwise covering family of flat algebras, one algebra per prime. It introduces no source assertion beyond the statement proved here.

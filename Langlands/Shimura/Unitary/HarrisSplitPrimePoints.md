# Harris's similitude group at a prime split in the imaginary quadratic field

Author: Worker 19.

This module specializes `ImaginaryQuadraticSplitPoints` (submitted together
with it) to the unitary similitude group of the published Harris setup. For a
finite place `v` of `ℚ` and an embedding `u : F →+* ℚ_v` of the imaginary
quadratic field `F ⊆ K`, it constructs the group isomorphism

`σ.rationalInvolution.Points ℚ_v ≃* (ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ`,

the identification of Harris (1998), Appendix, (A.1) and Harris (1999), (4.2),
before the algebra `ℚ_v ⊗[F, u] A` is decomposed over the places of `K` above
`u`.

## Source

Harris (1998), Appendix, printed p. 206 (PDF p. 30), considers the
similitude group `GG = GU(B, α)` of a division algebra `B` over a CM field
`E = E₀ · K₀` with an involution `α` of the second kind and rational
similitude factor, where `K₀` is imaginary quadratic and `p = 𝔭₁ · 𝔭₂` splits
in `K₀`. The places of `E` over `𝔭_i` are `v_i^(j)`, `j = 1, …, s`, and `F_j`
is the completion of `E` at `v_i^(j)`. Then

"(A.1) `GG(ℚ_p) ≅ ∏_j B(F_j)ˣ × ℚ_pˣ`".

The product runs over `j` only, that is, over the places above one of the
two primes `𝔭_i` of `K₀`.

Harris (1999), Section 4, printed pp. 308-309 (PDF pp. 10-11), works in the
same setting with groups `GG` and `GJ`, the latter the similitude group of a
second algebra `𝒟` of the same kind over the CM field `𝒦 ⊇ 𝒦₀`. With `p`
split in `𝒦₀` and `Φ_p = {v^(j)}` the places of `𝒦` over `p` determined by
the CM type, it writes `𝒟_p = ∏_j 𝒟_j × ∏_j c(𝒟_j)` with
`𝒟_j = 𝒟 ⊗ 𝒦_{v^(j)}` and states that it is "implicitly identifying
(4.2) `GJ_p ≅ ∏_j (𝒟_j)ˣ × ℚ_pˣ` as in [H2, Appendix, A.1]".

In this module `E` is the totally real field and `K` the CM field (Harris's
`E₀` and `E` or `𝒦`), `F` is Harris's `K₀` or `𝒦₀`, and `A` with `σ` is
either algebra with its involution. The prime of `K₀` over `p` (Harris's
`𝔭_i`) is given by the embedding `u : F →+* ℚ_v`. Such an embedding exists
exactly when the prime of `v` splits in `F`, but this module takes `u` as
input and proves nothing about splitting. The algebra `ℚ_v ⊗[F, u] A` is
`ℚ_p ⊗_{K₀, 𝔭_i} B`, which is `∏_j B(F_j)` by the decomposition
`ℚ_p ⊗_{K₀, 𝔭_i} E ≅ ∏_j F_j`; that decomposition is not formalized here.

## Inputs

The published `Langlands.Shimura.Unitary.CMData` provides, for a totally real
number field `E` and a totally complex quadratic extension `K` of `E`, the CM
conjugation `cmConjugation E K : K ≃ₐ[E] K` with
`embedding_cmConjugation`: `φ (cmConjugation E K k) = star (φ k)` for every
complex embedding `φ` of `K`. For a `K`-algebra `A` (with `E`- and
`ℚ`-algebra structures and the scalar towers `E → K → A`, `ℚ → E → A`), it
provides `SecondKindInvolution E K A`, an `E`-linear involution acting on
`K` by `cmConjugation E K`, its restriction of scalars
`σ.rationalInvolution : AlgebraInvolution ℚ A`, and
`rationalInvolution_center`. The rational unitary similitude group of the
published Harris tower (`Langlands.Shimura.Unitary.HarrisLevels`) is that of
`σ.rationalInvolution`; its points over a commutative `ℚ`-algebra `S` are
`σ.rationalInvolution.Points S` of `Langlands.Shimura.Unitary.Adelic`.
`Global.FinitePlace ℚ` and `Global.FiniteCompletion ℚ v` are the published
finite places of `ℚ` and their completions.

## Declarations

All declarations are in namespace `Langlands.Shimura`. Let `F` be a number
field with `IsCMField F` and `ι : F →+* K`.

- `cmConjugation_comp ι t`: `cmConjugation E K (ι t) = ι (conj t)`, where
  `conj` is `IsCMField.complexConj F`. Both sides have the same image under
  any complex embedding `φ` of `K`, by `embedding_cmConjugation` and
  `IsCMField.complexEmbedding_complexConj` for `φ ∘ ι`.
- `imaginaryQuadraticAlgebra ι` is the `F`-algebra structure on `A` through
  `ι` (`Algebra.compHom A ι`).
- `SecondKindInvolution.isConjugationOn σ ι`: with this `F`-algebra structure,
  `σ.rationalInvolution` satisfies `ImaginaryQuadraticSplit.IsConjugationOn F`,
  by `rationalInvolution_center` and `cmConjugation_comp`.

Assume moreover `Algebra.IsQuadraticExtension ℚ F`, so `F` is imaginary
quadratic. Let `v : Global.FinitePlace ℚ` and
`u : F →+* Global.FiniteCompletion ℚ v`, and give `ℚ_v` the `F`-algebra
structure `u.toAlgebra`.

- `SecondKindInvolution.splitPrimePoints σ ι v u` is the group isomorphism
  `σ.rationalInvolution.Points ℚ_v ≃* (ℚ_v ⊗[F] A)ˣ × ℚ_vˣ`, namely
  `ImaginaryQuadraticSplit.pointsEquiv` for `S = ℚ_v`.
- `splitPrimePoints_fst_val`: the first component of the image of a point is
  `ImaginaryQuadraticSplit.projection F A ℚ_v` applied to its algebra unit,
  that is, the image under `s ⊗ a ↦ s ⊗ a` from `ℚ_v ⊗[ℚ] A` to
  `ℚ_v ⊗[F] A`.
- `splitPrimePoints_snd`: the second component is the multiplier.

## Scope

Only the group isomorphism over `ℚ_v` is constructed. The topologies of the
two sides, the decomposition over the places of `K` above `u`, the level
subgroups (4.1) and `K(N, m)` of Harris (1999), and the global data of Harris
(the division algebra hypotheses, the invariants at `v` and the Shimura datum)
are not treated. The construction applies to every finite place and every
embedding `u`; it does not use the hypothesis of Harris that `A` is central
simple or a division algebra.

## Provenance

Derived from Harris (1999), equation (4.2) on printed p. 309, and Harris
(1998), Appendix, equation (A.1) on printed p. 206, both read in the original.
The coordinate form `(ℚ_v ⊗[F, u] A)ˣ × ℚ_vˣ` instead of the product over
places, and the choice of the embedding `u` as data, are implementation
choices.

Source IDs and SHA-256 fingerprints:

- `harris-1999-cohomological-automorphic-forms-525a222c4489ee9d`:
  `525a222c4489ee9d3fe86a52c6c17ffb30fcc7c31f24c16a64669e9615085b26`.
- `harris-1998-local-langlands`:
  `7934239ea37d0b91f741ae70c2ac157fe5d619cda4dd992ac24e39ae460c375b`.

Formal dependencies: `Langlands.Shimura.Unitary.ImaginaryQuadraticSplitPoints`,
`Langlands.Shimura.Unitary.CMData`, and Mathlib
`5ed2965256430c3649e86755f9576b54eca72435` under Lean 4.34.0, in particular
`IsCMField.complexEmbedding_complexConj` and `Algebra.compHom`.

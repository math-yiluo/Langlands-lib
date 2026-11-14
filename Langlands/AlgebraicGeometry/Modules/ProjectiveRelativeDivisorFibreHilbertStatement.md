# Hilbert functions of relative effective divisors on geometric fibres

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProjectiveRelativeDivisorFibreHilbertStatement`
defines the proposition `ProjectiveRelativeDivisorFibreHilbertStatement`. It uses
`fibreEulerCharacteristic` (from `ProperFlatFibreCohomologySemicontinuityStatement`: `χ(F_t)` on the
fibre over a point `t`). Twists `M(n) = M ⊗ 𝓛^{⊗ n}` are written with `Nat.rec` as right-associated
FLT tensor powers: `M(0) = M` and `M(n + 1) = M(n) ⊗ 𝓛`. On `X_B` this is definitionally the
`twist` of `ProjectiveFibreTwistCohomologyStatement`, which the module does not import.

## The statement

Let `A` be a noetherian ring, `f : X ⟶ Spec A` proper and flat, and `𝓛X` an invertible module with
a projective presentation of dimension `N` whose morphism to `ℙᴺ_A` is a closed immersion (so
`𝓛X = O_X(1)`). Let `B` be a noetherian ring, `s : Spec B ⟶ Spec A`, `X_B = pullback f s`, and `𝓛`
the pullback of `𝓛X` to `X_B`. Let `I` be a relative effective Cartier ideal on `X_B` over `Spec B`
(`IsRelativeEffectiveCartierIdeal`: its ideal module is locally free of rank one and its
subscheme `E = I.subscheme` is flat over `Spec B`). Write `K` for its ideal module
`StructureKernelModule.kernelModule I.subschemeι`. Let `k` be an algebraically closed field,
`sk : B →+* k`, and `t ∈ Spec B` the image of the point of `Spec k`. Then there is `n₀` such that
for all `n ≥ n₀`

`geomFibreH0Finrank (E ⟶ Spec B) (O_E(n)) k sk = χ(O_{X_t}(n)) - χ(K_t(n))`.

Here:

- `O_E(n)` is the `n`-fold right-associated FLT tensor power of the pullback of `𝓛X` to `E`
  (starting from the unit). This is exactly the module used in property 5 of
  `PicardHilbertPolynomialPiecesStatement` and in `RelativeEffectiveDivisorHilbertPiecesStatement`.
- `Scheme.Modules.geomFibreH0Finrank` (FLT port) is `dim_k` of the global sections of its pullback
  to the geometric fibre `E_k = E ×_{Spec B} Spec k`.
- `χ(O_{X_t}(n))` and `χ(K_t(n))` are the Euler characteristics, over `κ(t)`, of the twists
  `𝟙(n)` and `K(n)` (by the pullback `𝓛` of `𝓛X` to `X_B`) restricted to the fibre `X_t` of
  `X_B ⟶ Spec B`.

## Sources and provenance

This is the computation behind S. L. Kleiman, *The Picard scheme* (literature id
`kleiman-2005-picard-scheme-arxiv-math0504020v1`), proof of Theorem 4.8, p.30: "Set
`θ(n) := ψ(n) − φ₀(n)`. Plainly `Z` lies in `Hilb^θ_{X/S}`". Here `ψ(n) = χ(X_s, O_{X_s}(n))`, and
`φ₀` is the Euler polynomial of the inverse of the line bundle of the divisor. The statement is
derived. Kleiman's "plainly" stands for the following argument.

- On the geometric fibre `X_k`, the base change of the exact sequence
  `0 → K → O_{X_B} → O_E → 0` stays exact, because `E` is flat over `Spec B`. It is
  `0 → K_k → O_{X_k} → O_{E_k} → 0`.
- Twisting by `𝓛^{⊗ n}` and using additivity of Euler characteristics,
  `χ(O_{E_k}(n)) = χ(O_{X_k}(n)) − χ(K_k(n))`.
- For large `n`, the higher cohomology of `O_{X_k}(n)` and `K_k(n)` vanishes (Serre vanishing:
  The Stacks Project, Lemma 30.16.1, Tag 0B5T, and Lemma 30.16.2, Tag 02O1; literature id
  `stacks-projective-cohomology-ample-2026-11-13`, files `0B5T.html` and `02O1.html`). By the long
  exact sequence the higher cohomology of `O_{E_k}(n)` then vanishes too, so
  `χ(O_{E_k}(n)) = dim_k H⁰(E_k, O_{E_k}(n))`.
- The Euler characteristics over `k` equal those over `κ(t)` on the fibre `X_t`, by flat base
  change along the field extension `κ(t) → k` (D. Mumford, *Abelian Varieties*, Chapter II, §5,
  Corollary 5, printed pp.53–54; literature id `mumford-abelian-varieties-chapter-ii-scan`).

The statement is a prerequisite of a proof of property 5 of
`PicardHilbertPolynomialPiecesStatement` (Task 6028). In that proof, `K ≅ O(E)^∨` and
`O(E) ≅ L(m) ⊗ N`, which turn `χ(K_t(n))` into `φ(n − m)`.

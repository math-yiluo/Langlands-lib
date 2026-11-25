# Proof of the reduction of the Hilbert-polynomial pieces to cohomology and base change

The module `Langlands.AlgebraicGeometry.Picard.PicardHilbertPolynomialPiecesReduction` proves

```lean
theorem picardHilbertPolynomialPiecesReduction :
    ProperFlatFibreCohomologySemicontinuityStatement.{u} →
      ProperFibreCohomologyDimBaseChangeStatement.{u} →
        ProjectiveFibreTwistCohomologyStatement.{u} →
          ProjectiveRelativeDivisorFibreHilbertStatement.{u} →
            PicardHilbertPolynomialPiecesStatement.{u}
```

It is an internal helper of the proof module `PicardHilbertPolynomialPiecesProof`, which applies it
to the proofs of the four hypotheses.

So `PicardHilbertPolynomialPiecesStatement` follows from four hypotheses on fibre cohomology:

- SC, `ProperFlatFibreCohomologySemicontinuityStatement`;
- FE, `ProperFibreCohomologyDimBaseChangeStatement`;
- PT, `ProjectiveFibreTwistCohomologyStatement`;
- DH, `ProjectiveRelativeDivisorFibreHilbertStatement`.

Auxiliary declarations live in the namespace
`Langlands.AlgebraicGeometry.Picard.HilbertPolynomialPieces`. Tensor products, duals `L.dualFLT` and
invertibility are those of the FLT port. The fibre notation (`fibreModule`, `fibreCohomology`,
`fibreCohomologyDim`, `fibreEulerCharacteristic`, `twist`) is that of the hypotheses' modules.

## Fixed data and the witness

Fix `A`, `f : X ⟶ Spec A` (proper, flat, geometrically integral), and an invertible `𝓛X` with a
presentation `𝔓` of dimension `N` whose morphism to `ℙᴺ_A` is a closed immersion. For
`s : T ⟶ Spec A`, `twistSheaf f 𝓛X T s` is the pullback `𝓛` of `𝓛X` to `X_T = pullback f s`, and
`L(n) = twist 𝓛 L n` (definitionally the `Nat.rec` twist of the statement).

- `κ = ℚ[X] × ℚ[X]`.
- `pieceSet f 𝓛X T s L (φ, ψ) m` is the set of points `t ∈ T` such that:
  1. some invertible `M` with `M ⊗ L ≅ 𝒪` has `χ(M(n)_t) = φ(n)` for all `n`;
  2. `χ(𝒪(n)_t) = ψ(n)` for all `n`;
  3. for all `n ≥ m`, `Hᵖ(X_t, L(n)_t) = 0` for `p > 0` and `H⁰(X_t, L(n)_t) ≠ 0`.
- The open `piece f 𝓛X T s L c m` is the interior of `pieceSet` (`TopologicalSpace.Opens.interior`).
  On locally noetherian `T` and invertible `L` the set is open, so the interior is the set
  itself.
- `hilbertPolynomial (φ, ψ) m = ψ − φ.comp (X − m)`.

Clause 1 uses an inverse of `L` instead of a chosen dual, so no compatibility of duals with
pullback is needed. Inverses are unique up to isomorphism (`inverseUniqueIso`), and an inverse
exists: `L.dualFLT`, by the FLT theorem `IsInvertible.dual_monoidalV2`.

## General lemmas

- Isomorphism invariance: `fibreCohomologyIso`, `fibreCohomologyDim_congr`,
  `isZero_fibreCohomology_congr`, `fibreEulerCharacteristic_congr`. The same holds for
  isomorphisms of fibre restrictions: `fibreCohomologyIsoOfFibreModule`,
  `fibreEulerCharacteristic_congr_fibre`, `isZero_fibreCohomology_congr_fibre`.
- Twists: `twistIso`, `twistTensorIso` (`(F ⊗ M)(n) ≅ F(n) ⊗ M`), `twistAddIso`
  (`F(a)(b) ≅ F(a + b)`), `pullbackTwistIso` (pullback is monoidal: FLT `pullbackTensorObjIso`),
  and `isInvertible_twist`.
- Trivial fibres: an invertible module on a scheme with one point is trivial
  (`nonempty_iso_unit_of_subsingleton`: the trivialising open contains the point, so it is `⊤`).
  Hence the fibre of `g^*N` over `t` is trivial for invertible `N` on `T`
  (`nonempty_fibreModule_pullback_iso_unit`, through `Spec κ(t)`). Tensoring with `g^*N` does
  not change fibres (`nonempty_fibreModule_tensor_pullback_iso`, with `fibreModuleTensorIso`).
- Polynomials: `polynomial_eq_of_eval_eq` (degree `≤ N` and equal at `0, …, N`, by
  `Polynomial.eq_of_natDegree_lt_card_of_eval_eq`), and `polynomial_eq_of_forall_nat`.
- `isZero_fibreCohomology_iff` (for finite-dimensional spaces, zero iff dimension zero), and
  `fibreEulerCharacteristic_eq_of_isZero` (if all higher cohomology vanishes, `χ = dim H⁰`).

## Openness (`isOpen_pieceSet`)

- `exists_isOpen_eulerCharacteristic_eq`: for invertible `F`, every `t₀` has an open
  neighbourhood on which `n ↦ χ(F(n)_t)` equals `n ↦ χ(F(n)_{t₀})`. By PT, each sequence is a
  polynomial `P_t` of degree `≤ N`. By SC (local constancy of `χ`) applied to `F(0), …, F(N)`,
  there is a neighbourhood where these `N + 1` values agree with those at `t₀`. Then
  `P_t = P_{t₀}`.
- `exists_isOpen_vanishing`: if `Hᵖ(L(n)_{t₀}) = 0` for all `n ≥ m` and `p > 0`, the same holds
  near `t₀`. PT gives a neighbourhood and `n₀` with vanishing for all `n ≥ n₀`. For each of the
  finitely many `n ∈ [m, n₀)`, SC gives a neighbourhood with vanishing in degrees `≥ b_n`. For each
  `1 ≤ p < b_n`, the set `{t | dim Hᵖ < 1}` is open by SC and contains `t₀`. The intersection is a
  finite intersection of opens.
- `isOpen_pieceSet`: intersect these neighbourhoods for `M` (clause 1, with the same `M`), for `𝒪`
  (clause 2) and for `L`. On the vanishing locus, `dim H⁰(L(n)_t) = χ(L(n)_t)`, which is constant
  near `t₀`, so `H⁰ ≠ 0` persists.

## The five properties

1. Twist invariance (`pieceSet_subset_of_iso`, `pieceSet_eq_of_iso`). If `L ≅ L' ⊗ g^*N`,
   then `L(n)` and `L'(n)` have isomorphic fibres, and `M ⊗ g^*N` is an inverse of `L'` with the
   same fibre Euler characteristics as `M`. So `pieceSet L ⊆ pieceSet L'`. The reverse inclusion
   uses `L' ≅ L ⊗ g^*(N.dualFLT)`.
2. Base change (`pieceSet_baseChange`). The square formed by `pullback.map`, the two second
   projections and `h` is cartesian (`isPullback_baseChange`, by `IsPullback.of_right`), and
   `𝓛` pulls back to the twisting sheaf of `T'` (`twistSheafBaseChangeIso`). FE then gives equal
   fibre cohomology dimensions for the twists (`fibreCohomologyDim_twist_baseChange`). It follows
   that the Euler characteristics agree (`fibreEulerCharacteristic_twist_baseChange`) and so do
   the vanishing conditions (`isZero_fibreCohomology_twist_baseChange`, finiteness from SC).
   Inverses pull back to inverses, and conversely every inverse on `X_{T'}` is isomorphic to the
   pullback of `L.dualFLT`. So `pieceSet T' = h⁻¹(pieceSet T)`. Both sets are open, so the
   interiors agree.
3. Shape. Monotonicity in `m` is immediate, since clause 3 asks for all `n ≥ m`
   (`pieceSet_mono`). Disjointness (`pieceSet_disjoint`): two inverses are isomorphic, so a
   common point determines `φ` and `ψ` at every natural number. Covering
   (`exists_mem_pieceSet`): take `φ`, `ψ` from PT for `L.dualFLT` and `𝒪`. Take `m` from the
   uniform vanishing of PT and its section clause. The latter applies because the fibre
   `(pullback.snd f s).fiber t` is integral, hence nonempty (Mathlib instances for geometrically
   integral morphisms).
4. On a whole piece, a point satisfies clause 3 at `n = m`, giving `H¹ = 0` and `H⁰ ≠ 0`.
5. Hilbert polynomials. Let `t` be the image of the closed point of `Spec k`. It lies in the
   piece, because the piece is all of `Spec B`. DH gives `n₀` with
   `dim H⁰(E_k, O_E(n)) = χ(𝒪(n)_t) − χ(K(n)_t)` for `n ≥ n₀`, where `K` is the ideal module.
   `tensorDualIso` (the Library's `isIso_dualTensorEval`, with the identification
   `Scheme.Modules.tensorIsoSheafify` of the Library tensor product with the FLT one) gives
   `K ⊗ O(E) ≅ 𝒪`. With `O(E) ≅ L(m) ⊗ g^*N` this gives `K ⊗ (L(m) ⊗ g^*N) ≅ 𝒪`.
   `fibreEulerCharacteristic_twist_of_inverse` then shows `χ(K(j + m)_t) = χ(M(j)_t)`: the module
   `(K ⊗ g^*N) ⊗ 𝒪(m)` is an inverse of `L`, its `j`-th twist is `K(j + m) ⊗ g^*N`, and `g^*N`
   is trivial on fibres. So `χ(K(n)_t) = φ(n − m)` and `χ(𝒪(n)_t) = ψ(n)` for `n ≥ m`. Hence
   `dim H⁰(E_k, O_E(n)) = ψ(n) − φ(n − m) = hilbertPolynomial (φ, ψ) m (n)` for
   `n ≥ max n₀ m`.

The proof uses only the axioms `propext`, `Classical.choice` and `Quot.sound`.

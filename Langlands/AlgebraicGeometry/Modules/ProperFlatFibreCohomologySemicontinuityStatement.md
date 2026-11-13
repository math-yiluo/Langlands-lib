# Semicontinuity of fibre cohomology for proper flat morphisms

Authors: Worker 5705.

The module `Langlands.AlgebraicGeometry.Modules.ProperFlatFibreCohomologySemicontinuityStatement`
defines the proposition `ProperFlatFibreCohomologySemicontinuityStatement` and four auxiliary
definitions for fibres.

## Auxiliary definitions

Let `g : Y ⟶ T` be a morphism of schemes, `t` a point of `T` and `F` a module on `Y`
(`Y.Modules`).

- `fibreMap g t` is the second projection
  `pullback g (T.fromSpecResidueField t) ⟶ Spec κ(t)`, so its source is the fibre
  `Y_t = Y ×_T Spec κ(t)` of `g` over `t`, viewed as a scheme over `Spec κ(t)`. Here `κ(t)` is
  `T.residueField t`.
- `fibreModule g t F` is `F_t`, the pullback of `F` along the first projection `Y_t ⟶ Y`.
- `fibreCohomology g t F p` is `Hᵖ(Y_t, F_t)`. It is computed with the Library's
  `DerivedSections.relativeCohomology` (the right derived functors of global sections, as
  `κ(t)`-modules) applied to `fibreMap g t` and `F_t`.
- `fibreCohomologyDim g t F p` is `Module.finrank κ(t) Hᵖ(Y_t, F_t)`. By Lean's convention this is
  `0` for an infinite-dimensional space. The statement below shows the spaces are finite
  dimensional.
- `fibreEulerCharacteristic g t F` is `χ(F_t) = ∑ᶠ p, (-1)ᵖ dim Hᵖ(Y_t, F_t)`, a finite sum (`finsum`).
  It is the alternating sum of the dimensions, because only finitely many terms are nonzero
  (second clause below).

## The statement

`ProperFlatFibreCohomologySemicontinuityStatement` says the following. Let `T` be locally
noetherian, `g : Y ⟶ T` proper and flat, and `F` an invertible module on `Y` (the FLT port's
`Scheme.Modules.IsInvertible`). Then:

1. for every point `t` and every `p`, `Hᵖ(Y_t, F_t)` is a finite-dimensional `κ(t)`-vector space;
2. every point `t` has an open neighbourhood `V` and a bound `b` such that `Hᵖ(Y_{t'}, F_{t'}) = 0`
   for all `t' ∈ V` and all `p ≥ b`;
3. for all `p` and `r`, the set `{t | dim Hᵖ(Y_t, F_t) < r}` is open, i.e.
   `t ↦ dim Hᵖ(Y_t, F_t)` is upper semicontinuous;
4. `t ↦ χ(F_t)` is locally constant: every point `t` has an open neighbourhood on which `χ` equals
   `χ(F_t)`.

## Source and provenance

The statement is derived from D. Mumford, *Abelian Varieties*, Chapter II, §5 "Cohomology and base
change" (literature id `mumford-abelian-varieties-chapter-ii-scan`, retained PDF pages 5–7 =
printed pp.46–50).

- Mumford's Theorem (p.46) concerns a proper morphism `f : X → Y` of noetherian schemes with
  `Y = Spec A` affine, and a coherent sheaf `F` on `X`, flat over `Y`. It gives a finite complex
  `0 → K⁰ → … → Kⁿ → 0` of finitely generated projective `A`-modules with
  `Hᵖ(X ×_Y Spec B, F ⊗_A B) ≅ Hᵖ(K ⊗_A B)` for all `A`-algebras `B`.
- The Corollary on p.50 keeps these hypotheses except that `Y` need not be affine. Its proof
  starts "The problem being local on `Y`, we may assume `Y` affine". It states:
  (a) for each `p ≥ 0`, `y ↦ dim_{k(y)} Hᵖ(X_y, F_y)` is upper semicontinuous;
  (b) `y ↦ χ(F_y) = ∑ₚ (-1)ᵖ dim_{k(y)} Hᵖ(X_y, F_y)` is locally constant.
  Mumford's fibre `X_y` is `X ×_Y Spec k(y)` and `F_y = F ⊗_{O_Y} k(y)` (p.49). These are the
  `fibreMap` and `fibreModule` above.

Differences, all derived:

- The Lean statement uses Mumford's `X → Y` as `g : Y ⟶ T`. It allows a locally noetherian `T`,
  which is harmless because all four clauses are local on `T` and the Corollary's proof is local.
  It restricts `F` to an invertible module on a flat `g`. Such an `F` is coherent and flat over `T`, as Mumford requires. A proper
  morphism to a locally noetherian scheme is of finite type, so its source is locally noetherian.
- Clauses 1 and 2 follow from the Theorem on an affine noetherian neighbourhood `Spec A` of `t`,
  applied with `B = k(t')`. The complex `K ⊗ k(t')` consists of finite-dimensional spaces and
  vanishes above degree `n`, for every `t'` in `Spec A`.
- Clause 3 is Mumford's (a), expressed as openness of the sublevel sets of the integer-valued
  function. Clause 4 is (b).

Kleiman, *The Picard scheme* (literature id `kleiman-2005-picard-scheme-arxiv-math0504020v1`,
proof of Theorem 4.8, pp.28–29), uses these facts, with references to EGA III, to see that the
pieces `P^φ_m` are open. The statement is a prerequisite of a proof of the Library's
`PicardHilbertPolynomialPiecesStatement` (Task 6028).

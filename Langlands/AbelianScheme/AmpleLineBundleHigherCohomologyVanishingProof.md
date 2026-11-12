# Higher-cohomology vanishing for ample line bundles on abelian varieties: proof

This module proves the published proposition
`Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingStatement`.
It is the algebraically closed field case of Mumford, Fogarty and Kirwan,
*Geometric Invariant Theory*, third edition (1994), Proposition 6.13 (i),
printed p.123 / PDF p.136. The field-case proof in the source is on printed
pp.123–124 / PDF pp.136–137.

## Theorem

```lean
theorem Langlands.AbelianScheme.ampleLineBundleHigherCohomologyVanishing :
    AmpleLineBundleHigherCohomologyVanishingStatement.{u}
```

The type is exactly the published proposition, with its universe `u`. So it
covers every field `K : Type u` with `IsAlgClosed K`, in every characteristic,
every `A : AbelianScheme (Spec (CommRingCat.of K))` of every dimension,
including dimension zero, and every actual line bundle `L : LineBundle A.X.left`
with the published `L.IsAmple`. The conclusion is that
`(DerivedSections.relativeCohomology A.X.hom i).obj L.obj` is a zero object of
`ModuleCat K` for every `i > 0`. The theorem adds no hypothesis. The statement
pair and its imports are unchanged.

## Proof as implemented

The Lean proof is one application:

```lean
ampleLineBundleHigherCohomologyVanishing_of_cube GroupScheme.fieldCubePullback
```

Both inputs are published, proved Library results.

- `Langlands.AbelianScheme.ampleLineBundleHigherCohomologyVanishing_of_cube`,
  in `Langlands.AbelianScheme.AmpleLineBundleHigherCohomologyVanishingAssembly`,
  proves the target from one premise: a proof of
  `Langlands.GroupScheme.FieldCubePullbackStatement.{u}`.
- `Langlands.GroupScheme.fieldCubePullback`, in
  `Langlands.AbelianScheme.FieldCubePullbackProof`, proves
  `FieldCubePullbackStatement.{u}`, the balanced cube identity, over every
  field. That proof applies `fieldCubePullbackOfIsomorphism` to the published
  two-line-bundle cube theorem
  `Langlands.AlgebraicGeometry.Picard.fieldCubeIsomorphism`, which in turn
  rests on the published geometric theorem of the cube
  `Langlands.AlgebraicGeometry.Picard.fieldCubeTriviality`.

The conditional assembly carries out this argument; its own Markdown has the
details. Write `ψ_k` for multiplication by `k` on `A`.

1. Let `σ = ψ_{-1}` be inversion. It is an involution, so `L' = σ^* L` is
   ample, and `N = L ⊗ L'` is ample and symmetric: `σ^* N ≅ N`.
2. `A` is smooth and connected over `Spec K`, so it has a relative
   dimension `g` (`smoothConnectedRelativeDimension`).
3. Serre vanishing for the pair of ample bundles
   (`properAmplePairSerreVanishing`, applied to `M = 𝒪_A`, `L₁ = L`,
   `L₂ = L'`) gives `n₀` with `Hⁱ(A, L^a ⊗ L'^b) = 0` for all `a, b ≥ n₀`
   and `i > 0`.
4. Choose `k ≥ n₀ + 2` with `(k : K) ≠ 0`; one of `n₀ + 2` and `n₀ + 3`
   works. Then both binomial coefficients `C(k+1,2)` and `C(k,2)` are at
   least `n₀`.
5. The balanced cube identity gives
   `ψ_k^* L ≅ L^{C(k+1,2)} ⊗ L'^{C(k,2)}`
   (`fieldMultiplicationPullbackIsoOfCube`). So step 3 gives
   `Hⁱ(A, ψ_k^* L) = 0` for `i > 0`.
6. `ψ_k` is finite (`multiplication_isFinite_of_ne_zero`) and étale
   (`multiplication_etale_of_field`). The balanced cube identity also gives
   `ψ_k^* N ≅ N^{k·k}` (`fieldSymmetricMultiplicationPullbackOfCube`), so
   `ψ_k` has rank `(k·k)^g` at every point (`polarizedFiniteFlatRank`). This
   rank is nonzero in `K`.
7. By `finiteFlatCohomologyRetract`, `Hⁱ(A, L)` is a retract of
   `Hⁱ(A, ψ_k^* L) = 0`. Its identity factors through zero, so
   `Hⁱ(A, L) = 0`.

Algebraic closedness of `K` is used once, in step 6, because the published
`PolarizedFiniteFlatRankStatement` assumes `[IsAlgClosed K]`.

## Comparison with the source proof

The source argument (MFK pp.123–124) has four steps: Serre vanishing for `L^n`
with `n ≥ n₀`; invariance under translation, together with surjectivity of
`Λ(L^n)`, for bundles algebraically equivalent to `L^n`; the relation
`ψ_k^* L ≈ L^{k²}` (algebraic equivalence, cited from Lang, *Abelian
Varieties*, p.92) with finiteness of `ψ_k`; and the splitting of `L` off
`ψ_{k*} ψ_k^* L` by `k^{-2g}` times the trace when the characteristic does
not divide `k`.

The implemented route keeps the first and last steps in a different form and
avoids the middle ones.

- Serre vanishing is applied to the pair `L`, `σ^* L` at once, instead of to
  the powers of `L` alone.
- No algebraic equivalence, translation or `Λ(L^n)`-surjectivity is used.
  The exact cube formula `ψ_k^* L ≅ L^{C(k+1,2)} ⊗ (σ^* L)^{C(k,2)}` replaces
  `ψ_k^* L ≈ L^{k²}`.
- The trace splitting is replaced by the published retraction of
  `Hⁿ(Y, M)` off `Hⁿ(X, f^* M)` for a finite flat `f` of constant rank `d`
  with `d` nonzero in `K`. The rank of `ψ_k` is computed from the symmetric
  ample bundle `N` instead of being quoted as `k^{2g}`.

The cohomology is the published right-derived functor of relative global
sections, as in the statement; no Čech or other model is substituted.

## Axioms

A development check of the full chain reported only the standard axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Authors

Worker 3548 wrote this module. The conditional assembly it applies and the
cube, Serre-vanishing, retraction and rank results are earlier published
Library work; their own Markdown files record their authors.

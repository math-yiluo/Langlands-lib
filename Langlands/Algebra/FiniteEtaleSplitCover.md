# Finite étale algebras split over an fppf cover by graph idempotents

Namespace `Langlands.Algebra.FiniteEtaleSplitCover`. This internal module supplies the splitting
step of the proof of `WeilAbelianImageTrivialityStatement`. `A` and `B` are commutative rings in
universe `u`, and `B` is an `A`-algebra.

## Graph idempotents of a splitting

Let `T` be an `A`-algebra and `σ : T ⊗[A] B ≃ₐ[T] (Fin n → T)` a splitting of `T ⊗[A] B` as a
product of `n` copies of `T`.

- `splitEquiv σ` (definition): `σ`, viewed as an `A`-algebra isomorphism `B ⊗[A] T ≃ₐ[A] (Fin n → T)`
  after swapping the factors. `splitEquiv_tmul`: its `j`-th coordinate on `b ⊗ t` is
  `t * splitEquiv σ (b ⊗ 1) j`.
- `splitMap σ i` (definition): the `A`-algebra map `B → T`, `b ↦ splitEquiv σ (b ⊗ 1) i`.
- `splitIdem σ i` (definition): the idempotent of `B ⊗[A] T` corresponding to the `i`-th
  coordinate idempotent `Pi.single i 1`.
- `graphMul_splitMap`: the multiplication map `b ⊗ t ↦ splitMap σ i b * t` is the `i`-th
  coordinate of `splitEquiv σ`.
- `isGraphIdempotent_splitIdem`: `splitIdem σ i` is the graph idempotent of `splitMap σ i`
  (`IsGraphIdempotent`, module `Langlands.Algebra.EtaleGraphIdempotent`).
- `splitIdem_mul`, `sum_splitIdem`: the idempotents are orthogonal and sum to `1`.
- `exists_graph_family σ`: the three facts together: a complete orthogonal family of graph
  idempotents of `n` algebra maps `B → T`.

## Splitting over an fppf neighbourhood

Assume `B` is finite, projective and étale over `A`.

- `exists_split_cover p`: for every prime `p` of `A` there are an `A`-algebra `P` (in universe
  `u`), flat and finitely presented over `A`, a prime of `P` over `p`, and a splitting
  `P ⊗[A] B ≃ₐ[P] (Fin n → P)` for some `n`.

  Proof. The rank function `q ↦ rankAtStalk B q` is locally constant
  (`Module.isLocallyConstant_rankAtStalk`; `B` is finitely presented as a module, being finite
  projective), so its fibre through `p` is clopen and equals `basicOpen a` for an idempotent `a`
  (`PrimeSpectrum.exists_idempotent_basicOpen_eq_of_isClopen`). Over `A_a = Localization.Away a`
  the finite étale algebra `A_a ⊗[A] B` has constant rank (`Module.rankAtStalk_baseChange`).
  Mathlib's `Algebra.IsFiniteSplit.exists_tensorProduct_of_etale` (Lenstra, *Galois theory for
  schemes*, 5.10) gives a faithfully flat, finite étale `A_a`-algebra `P` over which it splits.
  `P` is flat and finitely presented over `A` (composition with the localization), and
  `P ⊗[A] B ≅ P ⊗[A_a] (A_a ⊗[A] B)` (`Algebra.TensorProduct.cancelBaseChange`). The prime `p`
  lies in `basicOpen a`, the image of `Spec A_a` (`PrimeSpectrum.localization_away_comap_range`),
  and `Spec P → Spec A_a` is surjective (faithful flatness).

## Provenance

Internal. This is the standard fact that a finite étale cover is split locally (Lenstra,
*Galois theory for schemes*, 5.10, in the constant-rank form formalized in Mathlib), here in the
fppf-local form used in the Markdown of `WeilAbelianImageTrivialityStatement`: locally on `Spec X`
the finite étale algebra `B ⊗_A X` splits as a finite product of copies of `X`. The graph
idempotents of a splitting connect it with the Library's `IsGraphIdempotent` API.

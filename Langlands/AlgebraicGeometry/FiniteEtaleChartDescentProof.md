# Proof of finite étale chart descent

`finiteEtaleChartDescent` proves exactly the published proposition
`Langlands.AlgebraicGeometry.FiniteEtaleChartDescentStatement.{u}`. Its pair is unchanged.

## The statement

Let `A → A'` be étale with `Spec A' → Spec A` surjective, and let `C` be a finite, projective,
étale `A'`-algebra. Suppose given, for every `A`-algebra `T` and all `A`-algebra maps
`f₁, f₂ : A' → T`, `T`-algebra isomorphisms `θ T f₁ f₂ : T ⊗[A', f₂] C ≃ T ⊗[A', f₁] C`. They must
be the identity when `f₁ = f₂`, satisfy the cocycle condition, and be natural in `T`. Then
there are a finite, projective, étale `A`-algebra `B` and an `A'`-algebra isomorphism
`e : A' ⊗[A] B ≃ C` such that every `θ T f₁ f₂` fixes the elements `1 ⊗ e(1 ⊗ b)`, `b ∈ B`.

## The proof

The proof packages `θ` with its identity, cocycle and naturality conditions as a datum
`ChartAlgebraDescent.Datum A A' C` and applies `ChartAlgebraDescent.Datum.descend`. That
construction (module `ChartAlgebraDescent`, built on `ChartAlgebraCoaction`,
`ChartAlgebraInvariants` and `ChartAlgebraTransport`) forms the coaction of the datum on `C` and
takes `B` to be its algebra of invariants. Faithfully flat descent shows that `B` is finite,
projective and étale over `A` and that `A' ⊗[A] B → C` is an isomorphism. The construction also
proves that every `θ T f₁ f₂` fixes the elements `1 ⊗ e(1 ⊗ b)`. It needs `A → A'` to be
faithfully flat. Here `A'` is flat over `A` because it is étale, and `Spec A' → Spec A` is
surjective by hypothesis, so `RingHom.FaithfullyFlat.iff_flat_and_comap_surjective` applies. The
finiteness and étaleness of `C` over `A'` are passed to the construction as properties of the ring
map `A' → C`. The fields of the constructed data (`P.ring`, `P.finite`, `P.projective`, `P.etale`,
`P.equiv`, `P.invariant`) are exactly the witnesses of the existential conclusion.

## Role

This theorem is the input `hK` of `affineWeilPairEtaleDescent`
(module `WeilChartSingleChartDescent`). There it descends the coefficient algebra of a Weil
restriction from an étale chart of the base to the base itself. The proof
`affineAdjointWeilRestriction` of `AffineAdjointWeilRestrictionStatement` passes it to `affineWeilPairEtaleDescent`.

## Provenance

Internal: descent of a finite étale algebra along a faithfully flat étale map, via the invariants
of a descent datum.

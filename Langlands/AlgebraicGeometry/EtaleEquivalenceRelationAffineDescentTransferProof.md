# Transfer of finite-surjective affine descent to algebraic spaces

Authors: Worker 239 and Worker 266. Worker 239 wrote the Lean proof and the
first version of this Markdown. Worker 266 checked both against the statement
and the sources and revised the provenance.

The theorem
`Langlands.AlgebraicGeometry.etaleEquivalenceRelationAffineDescentTransfer`
proves `EtaleEquivalenceRelationAffineDescentTransferStatement.{u}`. Its type is
exactly that statement:

```lean
EtaleEquivalenceRelationAffineDescentStatement.{u} →
  AlgebraicSpace.FiniteSurjectiveAffineDescentStatement.{u}
```

So finite-surjective descent of affineness for étale equivalence relations on
affine schemes implies Stacks Project Lemma 70.15.1 (Tag 07VS) for the
Library's algebraic spaces over every base scheme, in the same universe. The
statement module and its imports are unchanged. The proof uses the helper
module `Langlands.AlgebraicGeometry.EtaleEquivalenceRelationPresentation`,
whose Markdown describes each lemma and its provenance. It uses only the
standard axioms `propext`, `Classical.choice` and `Quot.sound`.

## Proof

Assume the hypothesis `hG`. Let `S` be a base scheme and `f : X ⟶ Y` a
morphism of algebraic spaces over `S` with `IsFinite (hom f)` and
`IsSurjective (hom f)`. Let `e : schemeYoneda V ≅ X.presheaf` with
`V.left` affine.

1. Put `c := e.hom ≫ hom f : schemeYoneda V ⟶ Y.presheaf`. Both Library
   properties are `MorphismProperty.relative` properties, which respect
   isomorphisms (Mathlib's `relative_respectsIso`). Hence `c` is finite and
   surjective (`MorphismProperty.RespectsIso.precomp`).
2. `Y.exists_atlas` gives an étale surjective `a` from a scheme `U`, and
   `exists_affine_atlas a ha has c hcs` gives an étale surjective `a₀` from a
   scheme `U₀` over `S` with `U₀.left` affine.
3. `exists_kernelPair` gives the represented kernel pair `(t, s) : R ⟶ U₀`
   of `a₀`, with étale projections. Put
   `E := EtaleEquivalenceRelation.ofKernelPair t s a₀ h ht hs`, the étale
   equivalence relation on `U₀.left`. Thus `E.U` is affine.
4. `ofKernelPair_hasFiniteSurjectiveCoverWithAffineQuotient` applied to `c`
   proves `E.HasFiniteSurjectiveCoverWithAffineQuotient`. The cover is the
   relation of the étale surjection `U₀ ×_Y V → V`, and its quotient is the
   affine scheme `V.left`.
5. `hG E hU₀ hcov` then gives `E.HasAffineQuotient`. Since `Y.toSheaf` is an fppf
   sheaf, `exists_isAffine_iso_of_hasAffineQuotient` gives `M : Over S`
   with `M.left` affine and `schemeYoneda M ≅ Y.presheaf`. This is
   `IsRepresentedByAffineScheme Y`.

## Provenance

The statement is an internal reduction step of the planned proof of
`AlgebraicSpace.FiniteSurjectiveAffineDescentStatement`. The argument follows
the presentation route described in the statement's Markdown. Its sources are
`stacks-etale-equivalence-relations-2026-11-01` (directory SHA-256
`df1ecbfa63c5e31cf736d9ea79dd262976c3098fd9b36f2dd32668d44bf75420`: `0263.html`,
`03C5.html`, `07S3.html`, `0APD.html`) and
`stacks-algebraic-space-affine-descent-2026-11-01` (directory SHA-256
`10fa51455958afc737851009364630c6f8e05ff49d790473a03fa1baaa4c00a0`:
`07VQ.html`, Lemma 70.15.1). The helper module's Markdown also cites the
Groupoid Schemes chapter PDF and the fppf covering definition (Tag 021M) for
the fppf case of Lemma 39.20.3.

The implementation differs from the statement Markdown's sketch in two
details. First, the first paragraph of the proof of Lemma 70.15.1 deduces
that `Y` is quasi-compact because `f` is surjective and `X` is
quasi-compact. The Lean proof does not use quasi-compactness of algebraic
spaces: `exists_affine_atlas` uses the quasi-compactness of the affine scheme
`V` directly to choose finitely many affine charts. Second, the cover
relation is built on `U₀ ×_Y V`, the base change of the étale atlas along the
affine representative of `X`. Its quotient is `V` itself, so no separate
representation of `X` by a presentation is needed.

## Scope

This unit proves only the transfer `T`. It does not prove the hypothesis
`EtaleEquivalenceRelationAffineDescentStatement`. In the planned route, that
hypothesis follows from `EtaleEquivalenceRelationNoetherianApproximationStatement`
and a proof of `NoetherianEtaleEquivalenceRelationAffineDescentStatement`,
which are separate units.

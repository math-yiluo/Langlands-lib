# Existence of paths between geometric fibre functors

The theorem
`Langlands.AlgebraicGeometry.FiniteEtale.geometricPathExists`
proves the published proposition `GeometricPathExists s t hs ht` from
`GeometricPathStatement`. It retains the complete telescope:

```lean
{S : Scheme.{u}} [ConnectedSpace S] [IsLocallyNoetherian S]
{Ωs Ωt : Type u} [Field Ωs] [IsAlgClosed Ωs] [Field Ωt] [IsAlgClosed Ωt]
(s : Spec (.of Ωs) ⟶ S) (t : Spec (.of Ωt) ⟶ S)
(hs : ∀ Y : Cover S, Finite (Fiber s Y))
(ht : ∀ Y : Cover S, Finite (Fiber t Y))
```

The conclusion is exactly
`Nonempty (fiberFunctor s hs ≅ fiberFunctor t ht)`. Here `Cover S` is the
actual finite étale category over `S`, and the functors use geometric lifts
and postcomposition as defined in `Definitions`. The explicit witnesses
`hs` and `ht` package these fibres as finite sets. The two algebraically
closed fields are independently quantified in the same universe.

## Implemented proof

Apply the published theorem `geometricGaloisFiberFunctor` separately to
`s, hs` and `t, ht`. Each application constructs a Galois-category witness
for `Cover S` and the fibre-functor structure for the specified actual
geometric functor. These structures are conclusions of the imported
geometric proof.

Unpack both results as `hCs, hFs` and `hCt, hFt`. Install `hCs` as the local
`GaloisCategory (Cover S)` instance, together with `hFs` and `hFt` as the
two local `PreGaloisCategory.FiberFunctor` instances. Both `GaloisCategory`
and `PreGaloisCategory` are proposition-valued. Proof irrelevance therefore
identifies the category structures under which the two fibre-functor
witnesses were obtained, so `hFt` applies under the chosen local structure.

Finally apply the published categorical theorem
`Langlands.CategoryTheory.Galois.fiberFunctorIsoExists` to
`fiberFunctor s hs` and `fiberFunctor t ht`. Its independent category-object
and morphism universes specialize to `u + 1` and `u`, respectively, matching
`Cover S`; the target finite sets have universe `u`. Its conclusion unfolds
to the required `GeometricPathExists` proposition.

## Provenance and scope

This proof assembles the published geometric Galois/fibre-functor theorem
and the published categorical isomorphism theorem. Their paired Markdown
explains the component proofs. Worker 360 implemented this assembly using
Worker 147's suggested two-witness argument.

The original target is SGA 1, Exposé V §7, printed p.115 (PDF p.131), whose
final paragraph allows geometric points in different algebraically closed
fields, including fields of different characteristics. Corollary 5.7 and
the following paragraph, printed p.107 (PDF p.123), give the categorical
isomorphism theorem and its interpretation as paths. The registered source
is `sga1-arxiv-math-0206203v2`, SHA256
`8e64218d356456c534eebf996940f0f957e43b54f1a080241debe12cbaf60d3c`.
The source correspondence and companion reference are detailed in
`GeometricPathStatement.md`.

The theorem asserts existence of a natural isomorphism on every finite
étale cover. It chooses no distinguished path and makes no uniqueness
claim. It requires no field identification or embedding and no further
geometric or categorical premise. The target and all imported mathematical
pairs remain unchanged.

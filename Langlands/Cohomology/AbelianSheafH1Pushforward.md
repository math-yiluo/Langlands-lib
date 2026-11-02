# Homeomorphism compatibility of the actual Čech-to-H¹ comparison

This internal derivation proves compatibility of the published finite-cover
Čech comparison with the published Ext cohomology equivalence under topological
pushforward along a homeomorphism. Spaces and abelian coefficient groups share
universe `u`; the family of opens is indexed in an independent universe `w`.
All cochains, quotient groups, comparison maps and cohomology equivalences are
the existing constructions.

For any continuous `f : X ⟶ Y`, `preimage_fullCover` proves that a full family
has a full preimage family. `cochains_map` identifies preimage cochain transport
before and after a coefficient morphism. It follows from naturality of that
morphism with respect to restrictions. `cochains_globalCochain` identifies the
transport of the degree-zero cochain of a global section with its restrictions
to the preimage family, by composition of restrictions. The section itself is
unchanged because inverse image of the top open is definitionally the top open.
Neither cochain identity assumes that the family is finite or full.

For a short complex `S` of abelian sheaves on `X`, `transportRepresentative`
moves a `Representative` for the pushed complex on `Y` to a representative for
`S` on the preimage family. Its primitive is the existing degree-zero cochain
transport, and its quotient global section is unchanged. The existing
differential identity and the two cochain identities above prove the required
primitive and quotient identities. This construction needs neither exactness,
flasqueness, a full family nor finiteness.

For a topological isomorphism `e : X ≅ Y` and a short exact `S`,
`transportRepresentative_value` proves that the value of the transported
representative is the image of the original value under exactly
`UnitSheafPushforward.cohomologyPushforwardEquiv e S.X₁ 1`. Values here are the
actual connecting classes defined using Mathlib's `Sheaf.H.δ` and its
degree-zero identification with global sections. The proof uses the published
connecting-map compatibility and section-to-cohomology normalization.

For a finite full family and a flasque middle sheaf,
`quotientClassHom_pushforward` descends this identity to the existing
`quotientClassHom`. Induction on a quotient class reduces to a cocycle, and the
independence-of-representative formula permits using a transported chosen
representative.

The chosen injective embedding of the pushed sheaf need not equal the
pushforward of its chosen embedding. `injectiveScPushforwardMap` supplies a
morphism from the first short complex to the second whose first component is
the identity. The pushforward equivalence preserves injective objects, so the
pushed injection extends across the chosen injection of the pushed sheaf.
The composite of that extension with the pushed cokernel map annihilates the
chosen injection; its cokernel descent gives the third component. Naturality
of `quotientClassHom` then proves `quotientClassHom_pushedInjective`, which
identifies the comparison from the pushed sequence with the published
`comparisonHom` on the pushed sheaf.

Consequently `comparisonHom_pushforward` proves, for every finite full family
`U` on `Y` and every class `x` with pushed coefficients, the exact identity

```text
comparisonHom F (preimage family) (fullness proof)
  (CechPullback.h1Equiv e.hom F.obj U x)
  =
cohomologyPushforwardEquiv e F 1
  (comparisonHom (pushforward e.hom F) U (fullness proof) x).
```

Provenance is the internal derivation just described from `CechPullback`,
`AbelianSheafH1Naturality`, `UnitSheafPushforwardNaturality` and pinned Mathlib
injective-object and cokernel APIs. There is no external theorem translation.
The comparison identity requires a finite full family and a homeomorphism;
it has no compactness, scheme or geometric hypothesis. Actual scheme Picard
pullback compatibility, nonsplit deformation and fppf Picard representability
remain separate obligations.

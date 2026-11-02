# Smooth coreflection and direct image

This module constructs a natural isomorphism

\[
  (f_*F)^{\mathrm{s}}\ \simeq\
  D_f^{\mathrm{s}}(F^{\mathrm{s}})
  = \bigl(f_*(F^{\mathrm{s}})\bigr)^{\mathrm{s}}.
\]

Here \(f_*\) is the actual ordinary-open equivariant sheaf direct image,
\(F^{\mathrm{s}}\) is the smooth subsheaf with its proved local fixedness
property, and \(D_f^{\mathrm{s}}\) is the smooth direct image from
`SmoothDirectImage`. The isomorphism retains the original sections and is
compatible with the existing identity and lax composition comparisons.

## Provenance and inputs

This is an internal construction derived from the published
`DirectImage`, `Smooth`, `SmoothPart`, and `SmoothDirectImage` modules.
It is not a separate transcription of an assertion from Harris or
Berkovich. Its role in the cohomology framework is to allow an actual
ordinary direct-image map with a smooth source to factor through the
direct image of the source-side smooth subsheaf.

The coefficient ring \(R\), group \(G\), spaces \(X,Y,Z\), and module
carriers share a universe `u`. The ring is commutative. The basic lemma
`isLocallyFixedAt_preimage` uses a group with a topology, topological
spaces with \(G\)-actions, a continuous map \(f:X\to Y\), and a proof
\(f(gx)=g f(x)\). It applies to any module-valued presheaf on
`ActionOpens G X`; no sheaf condition is used by this lemma.

The subsheaf maps and natural isomorphism additionally use
`IsTopologicalGroup G`, `ContinuousConstSMul` and
`HasStableNeighbourhoods` on \(X\) and \(Y\), as needed to construct the
two smooth coreflectors. The composition formulas also use these
hypotheses on \(Z\). Continuous individual translations mean that each
map \(x\mapsto g x\) is continuous. Stable neighbourhoods mean that
every open neighbourhood of a point contains an open neighbourhood of
that point stabilized by an open subgroup of \(G\). Neither properness
nor a condition on the fibres of \(f\) is required.

## Pulling back the local fixedness witnesses

For an open \(U\subseteq Y\), a direct-image section is an original
section \(s\in F(f^{-1}U)\). Suppose \(s\) is locally fixed at \(f(x)\).
Its witness consists of an open neighbourhood \(V\subseteq U\) of
\(f(x)\), an open subgroup \(H\), stability of \(V\) under \(H\), and
fixedness of the restriction of \(s\) to \(f^{-1}V\).

`isLocallyFixedAt_preimage` uses \(f^{-1}V\) as the neighbourhood of
\(x\) and retains the same subgroup \(H\). Continuity makes this an
open neighbourhood. Equivariance proves its stability:

\[
  f(hx')=h f(x')\in V\qquad(h\in H,\ f(x')\in V).
\]

The fixedness equation is exactly the given equation because
`DirectImage.preimage` retains the transport label. This proof does
not use topological-group continuity, continuous translations, stable
neighbourhoods, or the sheaf condition.

For an equivariant sheaf \(F\), `preimageSmoothMap` applies this lemma
at each point of \(f^{-1}U\). It constructs the actual sheaf morphism

\[
  (f_*F)^{\mathrm{s}}\longrightarrow f_*(F^{\mathrm{s}}).
\]

Its section formula sends \((s,p)\) to \((s,q)\), where \(q\) is the
newly proved pointwise local-fixedness property on \(X\).
`preimageSmoothMap_apply` states equality of the underlying section.
Linearity and naturality in transport opens are proved by reflexivity.

`preimageSmoothMap_inclusion` identifies the composite with
\(f_*(F^{\mathrm{s}}\hookrightarrow F)\) as the original smooth
subsheaf inclusion into \(f_*F\).
`preimageSmoothMap_naturality` proves naturality for every original
equivariant sheaf morphism \(F\to F'\).
`preimageSmoothMap_id` is the identity map.
`preimageSmoothMap_comp` says that the map for \(g\circ f\) is the
map for \(g\) on \(f_*F\), followed by \(g_*\) of the map for \(f\).
These equations are proved by reflexivity on the original sections.

## The natural isomorphism

`coreflectorMap` factors `preimageSmoothMap` through the smooth direct
image using the existing `SmoothDirectImage.lift`. Its source and
target are functors from all ordinary-open equivariant sheaves on
\(X\) to smooth equivariant sheaves on \(Y\):

\[
  f_*\mathbin{\ggg}(-)^{\mathrm{s}}
  \ \longrightarrow\
  (-)^{\mathrm{s}}\mathbin{\ggg}D_f^{\mathrm{s}}.
\]

`coreflectorInclusion` is the reverse natural transformation. It applies
the target-side smooth coreflector to the ordinary direct image of
the actual inclusion \(F^{\mathrm{s}}\hookrightarrow F\).

`coreflectorIso` bundles these transformations as a natural
isomorphism. Both inverse identities and both naturality equations
hold by reflexivity: the composites preserve the section and differ
only in proofs of local fixedness. This uses proof irrelevance for
the subtype properties, rather than exactness of smooth coreflection.

`coreflectorIso_hom_apply` states that forgetting the two smoothness
subtype proofs in the forward map recovers \(s\).
`coreflectorIso_hom_inclusion` states that forgetting just the outer
smooth direct-image proof recovers `preimageSmoothMap`.

`coreflectorIso_id` identifies the forward comparison for the identity
spatial map with the existing `idIso.hom` on \(F^{\mathrm{s}}\).
For \(f:X\to Y\) and \(g:Y\to Z\), `coreflectorIso_comp` compares the
following routes from \((g_*f_*F)^{\mathrm{s}}\) to
\(D_{g\circ f}^{\mathrm{s}}(F^{\mathrm{s}})\):

1. Apply the comparison for \(g\) to \(f_*F\), apply
   \(D_g^{\mathrm{s}}\) to the comparison for \(f\), then apply
   the existing lax `compMap` to \(F^{\mathrm{s}}\).
2. Apply the comparison for \(g\circ f\) directly.

Ordinary direct images compose definitionally in the imported
implementation. The displayed identity and composition equations are
proved by reflexivity on the nested section subtypes.

## Retained boundaries

The isomorphism compares the two specified smooth coreflections of
actual direct images. The module does not assert that ordinary direct
image preserves smooth sheaves, or that smooth coreflection is exact.
It does not prove invertibility of `SmoothDirectImage.compMap`.
No resolution is selected and no smooth/ordinary Godement comparison,
derived-functor computation, analytic or etale comparison, or
arithmetic and Shimura specialization is supplied here. These remain
separate obligations of the broader Harris framework.

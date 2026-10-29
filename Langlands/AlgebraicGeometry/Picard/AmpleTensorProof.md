# Ampleness of tensor products of actual line bundles

`Langlands.AlgebraicGeometry.Picard.ampleTensor` proves the entire published
proposition `Langlands.AlgebraicGeometry.Picard.AmpleTensorStatement.{u}`.
It quantifies over every scheme `X : Scheme.{u}` and actual line bundles
`L M N : LineBundle X`. An isomorphism
`tensorObj L.obj M.obj ≅ N.obj`, together with `L.IsAmple` and `M.IsAmple`,
implies `N.IsAmple`. There are no additional outer hypotheses.

The tensor, its powers, sections, line bundles and ampleness predicate are
the published constructions. In particular, a section open is the whole
maximal trivialization open. This module only adds the theorem.

## Implemented proof

Fix the isomorphism `e : tensorObj L.obj M.obj ≅ N.obj`.
Compactness of `X` is the compactness component of `L.IsAmple`.
For each point `x`, ampleness supplies positive exponents `n` and `m`
and sections `s` of `tensorPow L.obj n` and `t` of `tensorPow M.obj m`.
Their whole section opens contain `x`, and the open for `s` is affine.
The proof does not need the affineness supplied for `t`.

The published theorem `tensorPow_isLocallyFreeRankOne` packages these two
powers as actual line bundles `Ln` and `Mm`, and their further powers as
line bundles `Lnm` and `Mmn`. Set

```text
sm = sectionPow Ln.obj s m
tn = sectionPow Mm.obj t n
q  = tensorSection Lnm.obj Mmn.obj sm tn.
```

Thus `q` is a global section of the actual tensor of
`tensorPow (tensorPow L.obj n) m` and
`tensorPow (tensorPow M.obj m) n`.
Construct an isomorphism `E` from this module to `tensorPow N.obj (n*m)`:

1. Apply the tensor functor to `tensorPowMulIso L.obj n m` and
   `tensorPowMulIso M.obj m n`. For the second factor, compose with the
   equality isomorphism induced by `m*n = n*m`.
2. Invert `tensorPowTensorIso L.obj M.obj (n*m)` to regroup the two powers
   into `tensorPow (tensorObj L.obj M.obj) (n*m)`.
3. Apply `tensorPowIso e (n*m)`.

All these isomorphisms are published constructions for the actual sheaf
tensor powers, including their trailing structure-module factor.
Define the new section by `r = E.hom.app ⊤ q`.
This constructs a section of `N.powSections (n*m)` directly.

The published whole-open transport theorem `trivializationOpen_mapIso`
identifies the section open of `r` with that of `q`. The published
`tensorSectionGenerationLocus` identifies the latter with the intersection
of the whole opens of `sm` and `tn`. By
`trivializationOpen_sectionPow`, positivity of `m` and `n` makes these
opens exactly the original section opens of `s` and `t`. Consequently,

```text
N.sectionOpen r = L.sectionOpen s ⊓ M.sectionOpen t.
```

Both membership witnesses give membership of `x` in this open.
Apply the published `affineGenerationLocusIntersection` to the affine
open `L.sectionOpen s` and the section `t` of the actual line bundle `Mm`.
It gives affineness of precisely this intersection. The positive product
bound follows from `Nat.mul_le_mul hn hm`. These data establish the
unchanged definition of `N.IsAmple`.

The construction takes place under the point quantifier already present
in ampleness, so it also covers the empty scheme. It uses no reduction or
additional hypotheses on the scheme. No arbitrary affine-intersection
claim is used: the second open has the specific form of a line-bundle
section locus. The section `r` is defined by transport, so no additional
compatibility between a preselected product section and the flattening
isomorphisms is needed.

## Provenance and authorship

The source is The Stacks Project, Section 28.27, tag
[01PR](https://stacks.math.columbia.edu/tag/01PR), Definition 28.27.1
and Lemmas 28.27.4–5, registered as
`stacks-ampleness-tensor-isomorphism-2026-10-24`.
The retained original is
`literature/Stacks Project - Ampleness tensor and isomorphism transport (HTML snapshot 2026-10-24)/01PR.html`;
its registered directory SHA256 is
`23bfc9d1d2b4467556c7308dd203f22596c80d2f5276f1d5f9829673427e2f2d`.
The section and its comments were read again on 2026-10-28.
No source-specific errata file was present in the workspace, current
Library, or project `notes/errata` locations.

Lemma 28.27.5 uses ampleness of `L` and a positive-power section cover for
`M`; ampleness of `M` supplies this cover. Its section `s^m ⊗ t^n` and
Lemma 28.27.4 give the route implemented above. The Library's published
whole-generation-open equalities and affine-intersection theorem supply
the geometric steps in the actual definitions. The final transport to
the supplied bundle `N` is the isomorphism-invariant form of that argument.

Worker 477 implemented the final proof. Worker 489 designed and checked
the direct transport into `N`, the packaging of iterated powers as line
bundles, and the assembly interface used here. The implementation imports
the published tensor, rank-one, section-locus and transport infrastructure
by Lean module name. It reuses no unaccepted draft as a mathematical fact.

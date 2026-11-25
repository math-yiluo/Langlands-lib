# Rigidity of polarized automorphisms implies the Zariski sheaf property: proof

This module proves `ModuliZariskiSheafOfRigidityStatement`. It combines the existence
half, which glues data (`ZariskiGluingDatum` and the local-to-global lemmas of
`ZariskiLocality`), with the uniqueness half (`moduliFunctor_separated` from
`ZariskiSeparation`). It then derives the eventual Zariski sheaf property from
Lefschetz's theorem alone.

## Declarations

Namespace `Langlands.AbelianScheme.PolarizedFiniteLevel`.

- `ZariskiGluing.exists_glue hU a h hrig` (theorem). Let `S` be a quasi-separated scheme
  and `U : J → S.Opens` an open cover (`iSup U = ⊤`). Let `a i : Datum P (U i) g d n` be
  data on the members whose restrictions to each overlap `U i ⊓ U j` are isomorphic.
  Assume every polarized automorphism of each local datum `localDatum a W`, for `W`
  an open below some member, is the identity. Then some datum `b` on `S` has, for every
  `i`, a restriction `b.pullback (U i).ι` isomorphic to `a i`.
- `isZariskiSheaf_of_exists_glue hd hn hrig hex` (theorem, universe `0`). Assume the
  rigidity hypothesis of the statement at level `n` and the existence of glued data for
  every open cover of every level base (`hex`, in the form proved by `exists_glue`). Then
  `moduliFunctor P g d n hd hn` satisfies `LevelBase.IsZariskiSheaf`.
- `moduliZariskiSheafOfRigidity : ModuliZariskiSheafOfRigidityStatement` (theorem).
- `eventualModuliZariskiSheaf_of_cubicFieldEmbedding (hL : CubicFieldEmbeddingStatement.{0})
  : EventualModuliZariskiSheafStatement` (proved definition). It is
  `eventualModuliZariskiSheaf_of_rigidity hL moduliZariskiSheafOfRigidity`. As a `def`
  whose type is a proposition, it records that Lefschetz's theorem implies the eventual
  Zariski sheaf property. It does not prove `CubicFieldEmbeddingStatement`.

## Proof

`exists_glue`. Take `c := localDatum a` (the restriction of `a (index W)` to each small
open `W`) and `θ := transition h` (the isomorphisms on overlaps), both from
`ZariskiGluingInput`. `gluedDatum hU c hrig θ hdim hpol hdeg hfull` from
`ZariskiGluingDatum` takes its four propositional fields as hypotheses. Each is checked
on the open cover `F W := W.1` by the small opens `W : SubOpens U`, which covers `S` by
`isOpenCover_subOpens hU`. On each `W` the restriction of the glued object is the
corresponding piece of `localTransport W`, the local datum transported to the restricted
glued abelian scheme:

- `hdim`: `hasRelativeDimension_of_opens` with `(localTransport W).dimension`.
- `hpol`: `DualWitness.isPolarization_of_opens`. By `pullbackMap_gluedPolarization` the
  restricted polarization is `(localTransport W).polarization`, which is a polarization
  by `(localTransport W).polarized`.
- `hdeg`: `hasDegreeSquare_of_opens`, using that `gluedPolarization` is an isogeny
  (`hpol.1`). By `baseChange_map_gluedPolarization` the base change of the glued
  polarization to `W` is the local polarization followed by the inverse of the dual
  base-change isomorphism. Its degree is `d²` by `HasDegreeSquare.post_iso` applied to
  `(localTransport W).degree`.
- `hfull`: `isFull_of_opens`. By `pullbackTuple_gluedSections` the restricted level
  sections are those of `localTransport W`, which are full by
  `(localTransport W).level.full`.

Then `isomorphic_gluedDatum_restrict` says that the glued datum restricts on each small
open to a datum isomorphic to `c W`. `isomorphic_restrict_of_subOpens` passes from the
small opens to the members `U i`.

`isZariskiSheaf_of_exists_glue`. Let `S` be a level base with an open cover `U` and
classes `s i` over `U i` that agree on overlaps. Choose representatives
`a i := (s i).out`. Agreement of the classes on overlaps gives isomorphic restrictions
(`Quotient.exact`), so `hex` gives `b` on `S` with `b.pullback (U i).ι ≅ a i`. Hence the
class of `b` restricts to `s i` (`Quotient.sound`). Uniqueness of a class with these
restrictions is `moduliFunctor_separated` (module `ZariskiSeparation`), which
uses the rigidity hypothesis.

`moduliZariskiSheafOfRigidity`. Given the rigidity hypothesis `hrig` at level `n`,
apply `isZariskiSheaf_of_exists_glue`. For a level base `S` and an open cover `U`,
`exists_glue` applies: the scheme `S.obj` is locally noetherian, hence quasi-separated
(instance). The rigidity of `localDatum a W` over the open `W.1` is `hrig` on the level
base `S.ofOpen W.1`.

`eventualModuliZariskiSheaf_of_cubicFieldEmbedding` applies the published reduction
`eventualModuliZariskiSheaf_of_rigidity` (`EventualModuliZariskiSheafReduction`) to `hL`
and `moduliZariskiSheafOfRigidity`.

## Provenance

Internal. This is the standard gluing argument for a functor of isomorphism classes of
objects without nontrivial automorphisms that glue along open covers. Relative gluing of
schemes is Stacks Project Tag 01LH, formalized in Mathlib's `RelativeGluing`.
Mumford, Fogarty and Kirwan, *Geometric Invariant Theory*, third edition (1994), obtain
the fine moduli scheme at large level directly as a quotient (Theorem 7.9, printed
p.139, PDF p.152). The sheaf property of the represented functor is then automatic, and
they do not spell out this gluing. Lefschetz's embedding theorem enters only as the
hypothesis `CubicFieldEmbeddingStatement.{0}` of the last declaration.

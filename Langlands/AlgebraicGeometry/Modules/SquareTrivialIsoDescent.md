# Isomorphism descent for trivial modules around a ring-pullback square

This internal construction proves isomorphism descent for two globally trivial
scheme modules from an actual pullback square on global functions. The
commuting scheme square has maps `i₁ : Y₀ → Y₁`, `i₂ : Y₀ → Y₂`,
`j₁ : Y₁ → Y`, `j₂ : Y₂ → Y`, with `i₁ ≫ j₁ = i₂ ≫ j₂`.
The comparison is precisely the published ordinary module comparison
`squarePullbackIso j₂ i₁ i₂ j₁ w`, including its equality transport.

For modules `M, N` on `Y` and specified isomorphisms `τ : M ≅ 𝒪_Y` and
`σ : N ≅ 𝒪_Y`, assume that the actual global-function ring square is a
categorical pullback in `CommRingCat`:

```text
IsPullback j₁.appTop j₂.appTop i₁.appTop i₂.appTop.
```

`CompatiblePair i₁ i₂ j₁ j₂ w M N` is the subtype of pairs of actual
isomorphisms `e₁ : j₁* M ≅ j₁* N`, `e₂ : j₂* M ≅ j₂* N` satisfying

```text
i₁*(e₁.hom) ≫ squarePullbackIso(N).hom
  = squarePullbackIso(M).hom ≫ i₂*(e₂.hom).
```

Here each `*` denotes ordinary module pullback, not pullback of isomorphism
classes. `restrictIso` sends an isomorphism on `Y` to its two ordinary
pullbacks; naturality of the square comparison proves compatibility.
`isoEquiv` is an equivalence from `M ≅ N` to this compatible-pair subtype
whose forward map is `restrictIso`. Thus the equivalence retains the
specified ordinary restriction maps. Its inverse chooses the unique
isomorphism supplied by `existsUnique_iso`, and the two inverse laws follow
from the prescribed pullbacks and uniqueness.

The implemented proof proceeds as follows:

1. `square_unit` proves that the canonical structure-module identifications
   commute with the square comparison. It uses `pullbackUnitComposition`
   on both composite maps and equality transport on their common structure
   module. `trivialization_compatible` combines this with naturality to
   give the corresponding identity for each pulled-back trivialization.
2. `scalar_compatible` normalizes `e₁` and `e₂` by the pullbacks of `τ`
   and `σ`. The preceding identities and the assumed square compatibility
   identify their normalized pullbacks to `Y₀`. The published
   `structureAutScalar_pullback` converts this identity into compatibility
   of actual global units.
3. `InfinitesimalRankOnePatching.existsUnique_unit` patches those units in
   the actual global-section ring pullback. Multiplication by the resulting
   unit, conjugated by `τ` and `σ`, gives the descended isomorphism.
   `normalizeIso_pullback` and injectivity of `structureAutScalar` prove
   that its two pullbacks are precisely the prescribed isomorphisms.
4. `units_ext` uses the two ring projections to distinguish global units.
   `iso_joint_injective` applies this to normalized isomorphisms and then
   cancels the base trivializations. It supplies uniqueness in
   `existsUnique_iso` and the remaining inverse law of `isoEquiv`.

All four schemes lie in an arbitrary common universe `u`. There are no
nilpotence, properness, flatness, affineness, surjectivity, or cartesian
hypotheses on the scheme square itself. The required categorical pullback
hypothesis concerns its four actual global-section ring maps, and both
base modules must have specified global trivializations. The result does
not assert descent for arbitrary line bundles or the global Picard-groupoid
equivalence.

The provenance is internal. The argument extends the published
`TrivialIsoDescentProof` normalization proof from a single descent morphism
to two distinct restriction morphisms. It reuses the published
`SquarePullbackComparison`, `StructureUnitScalars`, and actual-ring unit
patching construction directly; it does not translate or cite an additional
external theorem.

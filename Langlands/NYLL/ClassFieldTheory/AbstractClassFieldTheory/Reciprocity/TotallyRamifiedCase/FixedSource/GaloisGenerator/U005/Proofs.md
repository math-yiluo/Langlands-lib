# NYLL M084.005: `galoisGenerator_generates`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.galoisGenerator_generates`
has the telescope `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
{K : FiniteAbstractField G} (E : FiniteCyclicSubextension K)` and type
`galoisGenerator_generatesStatement E`.
That is the published target
`Langlands.NYLL.ClassFormation.FiniteCyclicSubextension.galoisGenerator_generatesStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.GaloisGenerator.Statements`.

The statement says: every `x` in the named finite Galois quotient
`E.toFiniteGaloisSubextension.extensionQuotient` lies in
`Subgroup.zpowers E.galoisGenerator`, so it is an integer power of the
transported generator.

## Implemented proof

Write `e` for `E.toFiniteGaloisSubextension.extensionQuotientMulEquiv`.
It is a multiplicative equivalence from the named quotient
`extensionQuotient` to the quotient `K.field.toSubgroup ⧸ extensionSubgroup …`
that carries the chosen generator `E.generator`. By definition,
`E.galoisGenerator` is `e.symm E.generator`.

1. `intro x` gives a quotient element `x`. The wrapper is a `def` whose body
   begins with `∀ x`, so `intro` unfolds it.
2. The field `E.generates` of the cyclic subextension says `e x` is in
   `Subgroup.zpowers E.generator`. Mathlib's `Subgroup.mem_zpowers_iff` gives
   `n : ℤ` with `hn : E.generator ^ n = e x`.
3. `Subgroup.mem_zpowers_iff.mpr` and `refine ⟨n, ?_⟩` reduce the goal to
   `E.galoisGenerator ^ n = x`.
4. `apply e.injective` (from `MulEquiv.injective`) reduces this to an
   equation after applying `e`. Unfolding `galoisGenerator` with `change`
   gives `e (e.symm E.generator ^ n) = e x`.
5. Chain three equations: `map_zpow e _ n` gives
   `e (e.symm E.generator ^ n) = (e (e.symm E.generator)) ^ n`.
   `congrArg (· ^ n)` applied to `e.apply_symm_apply E.generator` rewrites
   this to `E.generator ^ n`. Then `hn` gives `e x`.

## Dependencies

- Imported published module:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.FixedSource.GaloisGenerator.Statements`.
  Through its imports it provides the target, `IntegralRepGroupType`
  (M002.001), `FiniteAbstractField`, `FiniteCyclicSubextension` (M032.001)
  with its fields `generator` and `generates`, the normality instances
  that give these quotients their group structures, `FiniteGaloisSubextension`
  (M040.001), `extensionQuotient` (M040.004) and its group instance
  (M040.008), `extensionQuotientMulEquiv` (M040.010, defined as
  `MulEquiv.refl _`), `toFiniteGaloisSubextension` (M084.003) and
  `galoisGenerator` (M084.004).
- Mathlib: `Subgroup.mem_zpowers_iff`, `MulEquiv.injective`, `map_zpow`,
  `MulEquiv.apply_symm_apply` and `congrArg`.
- No unpublished result is used and no helper declaration is added.
- Axioms reported by the Lean service: `propext`, `Classical.choice` and
  `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/FixedSource.lean`
(file SHA-256 `4c8289dbb89fb3459f1248a4cd171f813fdc5e7bcba9e845d8b1929261f40f50`),
lines 102–114 (M084.005). The docstring is at lines 102–103, the statement at
104–105 and the proof at 105–114. The readable pinned source is kept
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`, and the source imports
  are replaced by the published statement module above. The noncomputable
  section, the namespaces, the docstring and the variables for `G` and `K`
  are kept. The source's `open KummerTheory` and `open CyclicCohomology`
  lines, the universe comment and the other declarations of the source file
  are omitted.
- The theorem's type is written as the published
  `galoisGenerator_generatesStatement E`, in place of the source's explicit
  `∀ x, x ∈ Subgroup.zpowers E.galoisGenerator`. The two are definitionally
  equal.
- The proof script (steps 1–5) is the source's, line for line.

The original copyright and author header is kept; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract result about finite group quotients. It supplies no host
class-formation, cup-product, transfer, Tate-cohomology or reciprocity
theorem.

# NYLL M004.007: proof of cyclic norm-kernel vanishing

The paired Lean file proves the published target
`Langlands.NYLL.CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement`
(module `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U007.Statements`)
as the theorem
`Langlands.NYLL.CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero`.

## Statement proved

The theorem has the target's complete telescope, in the target's order:
implicit `G : Type`, `[Group G]`, `[Fintype G]`, then explicit
`A : Rep.{0} ℤ G`, `g : G`, `hg : ∀ x, x ∈ Subgroup.zpowers g` and
`hzero : CategoryTheory.Limits.IsZero (tateCohomology A (-1))`.
Its type is the published proposition applied to these parameters,
`normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZeroStatement A g hg hzero`.
That proposition unfolds to: for every `x : A.V` with `A.norm.hom x = 0`,
there is `y : A.V` with `A.ρ g y - y = x`. Here `A.norm`, `A.ρ` and
`tateCohomology` are Mathlib's actual representation norm, action and Tate
cohomology object. The group and the representation carrier stay in universe zero.
The theorem adds no hypotheses. It uses `hg` and `hzero` in the proof.

## Implemented proof

1. A local `IsCyclic G` instance is built from the specified generator:
   `Subgroup.eq_top_iff'` turns `hg` into `Subgroup.zpowers g = ⊤`, and
   `isCyclic_iff_exists_zpowers_eq_top` turns that into `IsCyclic G`.
   `IsCyclic.commGroup` then gives a local `CommGroup G` instance. That is
   the instance Mathlib's finite-cyclic group cohomology requires.
2. The published comparison
   `Langlands.NYLL.CyclicCohomology.finiteCyclicH1IsoTateHMinusOne A g hg :
   groupCohomology.H1 A ≅ tateCohomology A (-1)` (NYLL M004.006) and
   `Limits.IsZero.of_iso` carry `hzero` to `IsZero (groupCohomology.H1 A)`.
   `ModuleCat.subsingleton_of_isZero` then installs
   `Subsingleton (groupCohomology.H1 A)`.
3. Given `x` with `hx : A.norm.hom x = 0`, the proof installs the
   representation's own `ℤ`-module structure `A.hV2` on `A.V`. It then forms
   `x' : LinearMap.ker A.norm.hom.toLinearMap` from `⟨x, hx⟩`. The local
   instance matters. A development check without it failed to elaborate this
   line: the synthesized instance `AddCommGroup.toIntModule` was reported as not
   definitionally equal to the instance `A.hV2` inferred by typing.
4. Mathlib's class map
   `Rep.FiniteCyclicGroup.groupCohomologyπOdd A g hg 1 ⟨0, rfl⟩`
   sends `x'` into `H¹(G, A)`. Because that object is a subsingleton,
   `Subsingleton.elim` shows the class is zero.
5. `Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff` turns a zero class
   into membership of `x` in the range of `(applyAsHom A g - 𝟙 A).hom`. This
   gives `y` and `hy`. `simpa [Rep.sub_hom] using hy` rewrites `hy` to
   `A.ρ g y - y = x`.

The axioms used are `propext`, `Classical.choice` and `Quot.sound`. There is no
`sorry`, `admit`, native decision or new axiom.

## Original correspondence

The source is Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/GaloisCohomology/Cyclic/NormKernelVanishing.lean`. That file's SHA-256 is
`06d33a5e35d45458927e2ac18fe7103bc061dec851162110347e847d7d78f0c8`.
The relevant part is M004.007, theorem
`CyclicCohomology.normKernel_le_sigmaMinusOneRange_of_tateHMinusOne_isZero`,
lines 121–146: the docstring at 121–125, the signature at 126–131 and the
proof at 132–146. The section context is at lines 26–32. The registered
source is `external-lean-reuse-snapshots-2026-10-21`, with content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

Apart from the changes below, the proof body is the original's, line for line
(source lines 133–146).

Worker 152 made these changes:

- The namespace gets the prefix `Langlands.NYLL`. The theorem's type is the
  published `…Statement` proposition applied to the source parameters. The
  source's literal conclusion is that proposition's definitional unfolding,
  so `intro x hx` works as in the source.
- The source's line 132 uses the cyclicity helper M004.001,
  `CyclicCohomology.isCyclic_of_generator` (lines 34–45). This is replaced by
  the Mathlib composition in step 1, exactly as in the published M004.006
  construction. The Library has no copy of the helper.
- The docstring is shortened to a plain statement of the result. The
  original's remark about the cyclic step of abstract Kummer theory is
  omitted.
- `finiteCyclicH1IsoTateHMinusOne` is imported from the published M004.006
  module rather than redefined.
- The source's `noncomputable section`, unused `universe u` and unrelated
  declarations (M004.002–005: the extension subgroup, the fixed
  representation, the continuity predicate and the vanishing-condition
  predicate) are omitted. None of them is needed for this finite-group theorem.

## Actual dependencies

- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U007.Statements`
  provides the target proposition.
- `Langlands.NYLL.GaloisCohomology.Cyclic.NormKernelVanishing.U006.Definitions`
  provides `Langlands.NYLL.CyclicCohomology.finiteCyclicH1IsoTateHMinusOne`. It
  transitively imports the published M003.003 comparison
  `Langlands.NYLL.TateCohomology.isoFiniteCyclicNegOne` and
  `Mathlib.RepresentationTheory.Homological.GroupCohomology.FiniteCyclic`.
  The latter supplies `Rep.FiniteCyclicGroup.groupCohomologyπOdd` and
  `Rep.FiniteCyclicGroup.groupCohomologyπOdd_eq_zero_iff`.
- From Mathlib: `isCyclic_iff_exists_zpowers_eq_top`, `Subgroup.eq_top_iff'`,
  `IsCyclic.commGroup`, `CategoryTheory.Limits.IsZero.of_iso`,
  `ModuleCat.subsingleton_of_isZero` and `Rep.sub_hom`.

The proof was compiled in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
with zero diagnostics. A private probe assigned the unapplied constant to the
target's complete outer telescope (implicit `G`, both instances, then `A`, `g`,
`hg`, `hzero`), both against the `…Statement` proposition and against its
unfolded conclusion. Both assignments compiled.

## Scope

This unit proves only the finite-group, elementwise consequence of vanishing
Tate H⁻¹ for a specified generator. It asserts no class-formation, reciprocity,
Kummer-theory or other host result. It does not touch the extension predicates
M004.002–005.

## Attribution

The Lean file keeps the original copyright, Apache-2.0 release and author
header for Naganori Yamaguchi (assisted by OpenAI Codex), and adds a
modification note. The retained license files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

# NYLL M116.005 target: short exactness of the equivariant representation complex

This module extracts one theorem type from Naganori Yamaguchi's
ClassFieldTheory (NYLL), commit `fbd320cd8b1b06487c58227e92eb135794267709`, as
a Prop-valued definition. It supplies the target only and contains no proof
of it. The proof is separate `lean.proof@1` work.

## Source

The original is
`Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`
(362 lines, SHA-256
`f483093db92c9aea3553e6378269c66890d414c28ede02630f5ffddf9eee4ca2`), retained at
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/Nyll/GaloisCohomology/Cyclic/Herbrand/HerbrandLowDegree/TateComparison.lean`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. Its
attribution supplement is `nyll-classfieldtheory-fbd320cd-supplement`, content
fingerprint
`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`. The
inventory rows are in `notes/reuse/nyll-public-port/m097-m120.md`, section
M116 (patch status "none in patch10").

| Unit | Original name; `omit` / asserted type lines | Target (paired Lean line) |
| --- | --- | --- |
| M116.005 | `CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex_shortExact`; `omit [Fintype G] in` at 67 / 68–74 | `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex_shortExactStatement` (line 36) |

The source theorem has no docstring. Its section context is source lines
12–30: `open CategoryTheory`,
`namespace CyclicCohomology.ProfiniteCohomology.Herbrand`,
`noncomputable section`, `universe u w` and the `variable` commands of lines
27–30:

```lean
variable {G A B C : Type}
variable [Group G] [Fintype G] [CommGroup A] [CommGroup B] [CommGroup C]
variable [MulDistribMulAction G A] [MulDistribMulAction G B]
  [MulDistribMulAction G C]
```

No other `variable`, `omit` or `include` command precedes line 74.

## Exact statement

```lean
def Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand.equivariantShortComplex_shortExactStatement
    {G A B C : Type} [Group G] [CommGroup A] [CommGroup B] [CommGroup C]
    [MulDistribMulAction G A] [MulDistribMulAction G B]
    [MulDistribMulAction G C]
    (i : A →* B) (j : B →* C)
    (hi : ∀ (g : G) (a : A), i (g • a) = g • i a)
    (hj : ∀ (g : G) (b : B), j (g • b) = g • j b)
    (hker : ∀ b : B, j b = 1 ↔ ∃ a : A, i a = b)
    (hinj : Function.Injective i) (hsurj : Function.Surjective j) : Prop :=
  (equivariantShortComplex i j hi hj hker).ShortExact
```

The first eleven parameters are the section variables of lines 27–30 that
the source theorem includes: all of them except `[Fintype G]`, which the
theorem omits with `omit [Fintype G] in`. They keep the source order and
binder kinds. The remaining parameters are the theorem's own binders of lines
69–73, unchanged. The proposition says that, for `G`-equivariant
homomorphisms `i : A →* B` and `j : B →* C` of commutative groups with
`ker j = range i` (`hker`), `i` injective and `j` surjective, the short
complex `0 → Additive A → Additive B → Additive C → 0` of integral
`G`-representations built by `equivariantShortComplex` (M116.004, sibling
module `TateComparison/Definitions`) is short exact in the sense of Mathlib's
`ShortComplex.ShortExact` (exact, with mono first map and epi second map).
`G` need not be finite.

## Modifications (Worker 5454)

- **Extraction**: only the asserted type is taken. The proof (source lines
  75–97) is omitted. It uses the private theorem M116.001
  `repExact_of_hom_exact` (lines 20–25), which is therefore not needed here.
- **Form**: the theorem becomes a `def … : Prop`. The section variables are
  written as explicit parameters, in the order of lines 27–30, followed by the
  theorem's own parameters. No `variable` or `omit` command is used.
  `universe u w` is omitted because the statement uses neither universe.
- **Linter**: `hinj` and `hsurj` do not occur in the conclusion, so the
  unused-variable linter is disabled for this definition only, with
  `set_option linter.unusedVariables false in`.
- **Names**: namespace prefix `Langlands.NYLL` and the `Statement` suffix.
  `open CategoryTheory` and `noncomputable section` are kept.
- **Imports**: Mathlib's `Mathlib.Algebra.Homology.ShortComplex.ShortExact`
  (for `ShortComplex.ShortExact`) and the sibling data module
  `Langlands.NYLL.GaloisCohomology.Cyclic.Herbrand.HerbrandLowDegree.TateComparison.Definitions`.
  The source's NYLL imports (lines 7–8) are not used by the statement.
- **Docstrings**: the source theorem has no docstring. The target's
  docstring is a new one-sentence description. The module docstring is a
  modification notice.
- No compatibility change to any mathematical type is needed.

## Signature verification

All checks were made in the approved environment
`5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean `v4.34.0`, Mathlib
`5ed2965256430c3649e86755f9576b54eca72435`).

- The module compiles with no errors or warnings. Inspection reports that
  the target returns `Prop`.
- A private audit module copies source lines 12–30 and 67–97 (the section
  context, with the private theorem M116.001, and the theorem with its
  verbatim source proof) into an auxiliary namespace nested in
  `Langlands.NYLL.CyclicCohomology.ProfiniteCohomology.Herbrand`, so that
  `equivariantShortComplex` resolves to the adapted constant. A `MetaM`
  command then checks that the theorem and the target have identical
  universe-parameter lists, identical binder names (after erasing hygienic
  macro scopes) and binder kinds along the whole telescope, and that the
  theorem's type is definitionally equal to `∀ xs, target xs`. It passed.
  As a control, a variant of the M115.001 target with its parameters `K` and
  `L` swapped was rejected by the same command.
- A second private module proves the target, applied to its parameters, by
  the verbatim source proof. That proof is not part of this contribution.

## Scope

This target asserts short exactness of one complex of representations. It
does not assert a class-formation, cup-product, Tate, transfer or reciprocity
result, or any Herbrand-quotient comparison.

## Attribution

The original copyright, Apache-2.0 release and author header (Naganori
Yamaguchi, assisted by OpenAI Codex) are preserved. No patch10 change applies
to this module ("none in patch10"), and no other draft was reused. The
retained license and notice are `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

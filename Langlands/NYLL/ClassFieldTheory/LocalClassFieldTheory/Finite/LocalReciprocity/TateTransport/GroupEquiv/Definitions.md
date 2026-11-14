# Cyclic Tate short complexes under a group isomorphism

Adapted by Worker 66 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean`
(SHA-256 `cf2c48399c7de2b908cf83a147834c66d3cbe1a0965bf78e563e2beaaed593fa`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

## What is defined

Let `R` be a commutative ring and `Q`, `P` finite commutative groups, all in
universe zero. For `A : Rep R P` and `g : P`, Mathlib's
`Rep.FiniteCyclicGroup.normHomCompSub A g` is the short complex
`A --N--> A --(ρ(g) - 1)--> A` of `R`-modules, where `N` is the norm map
`a ↦ ∑ p, ρ(p) a`. `Rep.FiniteCyclicGroup.subCompNormHom A g` is the short
complex `A --(ρ(g) - 1)--> A --N--> A`. When `g` generates the group, their
homology objects compute degree-zero and degree-minus-one Tate cohomology of
the finite cyclic group. The four definitions say that these short complexes
and their homology are unchanged when the representation is reindexed along a
group isomorphism. Fix `e : Q ≃* P`, `A : Rep R P` and `g : Q`, and write
`Ares = Rep.res e.toMonoidHom A` for the representation of `Q` on the same
module by `q ↦ ρ(e q)`.

- `normHomCompSubResEquivIso e A g` and `subCompNormHomResEquivIso e A g`:
  isomorphisms of short complexes from the complex of `Ares` at `g` to the
  complex of `A` at `e g`. All three components are the identity `i` of the
  common underlying module. The squares involving `ρ(g) - 1` commute by
  `rfl`, since `Ares` acts by `g` exactly as `A` acts by `e g`. The squares
  involving the norm commute because the norm of `Ares` equals the norm of
  `A`; this is the published theorem
  `Langlands.NYLL.PortInternal.M100.d002` (see Modifications).
- `normHomCompSubHomologyResEquivIso e A g` and
  `subCompNormHomHomologyResEquivIso e A g`: the induced isomorphisms of the
  homology objects, given by `ShortComplex.homologyMapIso` applied to the two
  short-complex isomorphisms above.

The representation `A` may have its carrier in any universe; this is the
single universe parameter of each declaration, as in the source.

## Source correspondence

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M100.003 | `normHomCompSubResEquivIso` (64–76) | `normHomCompSubResEquivIso` |
| M100.004 | `subCompNormHomResEquivIso` (78–90) | `subCompNormHomResEquivIso` |
| M100.005 | `normHomCompSubHomologyResEquivIso` (92–98) | `normHomCompSubHomologyResEquivIso` |
| M100.006 | `subCompNormHomHomologyResEquivIso` (100–106) | `subCompNormHomHomologyResEquivIso` |

All four lie in the source section `GroupEquiv` (lines 45–108) with
`variable {R Q P : Type} [CommRing R] [CommGroup Q] [CommGroup P] [Fintype Q]
[Fintype P]` at lines 47–48. Every unqualified original name above is in
`LocalClassFieldTheory`; every adapted name is in
`Langlands.NYLL.LocalClassFieldTheory`.

The other units of the same source file are published separately. M100.001
(`map_cyclicGenerator`) and M100.002 (the private `res_norm_eq`, lines 50–62)
are Prop-valued targets in
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.Statements`;
the M100.002 target is named `Langlands.NYLL.PortInternal.M100.d002Statement`.
M100.007–.010 (section `RepresentationIso`) are in the sibling module
`TateTransport/RepresentationIso/Definitions`.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by
  `Langlands.NYLL`.
- The single NYLL import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  is replaced by the Mathlib module
  `Mathlib.RepresentationTheory.Homological.FiniteCyclic` and the module
  `Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.U002.Proofs`,
  which proves the M100.002 target. Apart from that theorem, every constant
  used by these four definitions comes from Mathlib.
- `noncomputable section` and `open CategoryTheory` are retained. The unused
  `open ClassFormation` is omitted.
- The source private theorem `res_norm_eq` (M100.002) is not repeated here.
  In the bodies of M100.003 and M100.004 the source bullet
  `simpa [Ares, i] using (res_norm_eq e A).symm` becomes
  `simpa [Ares, i] using (Langlands.NYLL.PortInternal.M100.d002 e A).symm`.
  The published theorem `d002 e A` has type `d002Statement e A`, which unfolds
  to the source statement of `res_norm_eq e A`, including its `let Ares`. This
  changes only which proof of a morphism equality is supplied; the data (the
  three identity components) are unchanged.
- Otherwise the section `GroupEquiv`, its `variable` line, the docstrings, the
  binders `(e : Q ≃* P) (A : Rep R P) (g : Q)`, the result types and the bodies
  are copied verbatim from source lines 45–108.
- The module docstring keeps the source's explanation, restricted to the
  group-isomorphism comparison in this file, and adds a modification notice.
- No instance, attribute or other declaration is added.

## Focused verification

The module compiles in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or
warnings. Inspection of `subCompNormHomHomologyResEquivIso` reports one
universe parameter and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A private diagnostic module compiled
the verbatim source lines 45–108, including `res_norm_eq` with `private`
removed, in a separate namespace over the same imports. For each of the four
definitions it checked `@adapted = @original := rfl` as whole constants. So
the adapted declarations have the same complete types, including binder
kinds, as the originals and are definitionally equal to them.

## Scope and attribution

These are comparison isomorphisms only. They do not state or prove the local
class-field axiom, any Tate-cohomology cardinality, or reciprocity.

The original copyright and author header is retained. The unchanged
Apache-2.0 `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) accompany
this subset. The Lean file's module docstring carries a modification notice.

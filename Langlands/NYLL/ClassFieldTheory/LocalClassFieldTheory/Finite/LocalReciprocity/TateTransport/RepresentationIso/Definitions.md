# Cyclic Tate short complexes of isomorphic representations

Adapted by Worker 66 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean`
(SHA-256 `cf2c48399c7de2b908cf83a147834c66d3cbe1a0965bf78e563e2beaaed593fa`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

## What is defined

Let `R` be a commutative ring and `Q` a finite commutative group, both in
universe zero, and let `g : Q`. For `A : Rep R Q`, Mathlib's
`Rep.FiniteCyclicGroup.normHomCompSub A g` is the short complex
`A --N--> A --(ρ(g) - 1)--> A` of `R`-modules, where `N` is the norm map
`a ↦ ∑ q, ρ(q) a`. `Rep.FiniteCyclicGroup.subCompNormHom A g` is the short
complex `A --(ρ(g) - 1)--> A --N--> A`. When `g` generates `Q`, their homology
objects compute degree-zero and degree-minus-one Tate cohomology of the
finite cyclic group `Q`. The four definitions say that these short complexes
and their homology depend on `A` only up to isomorphism:

- `normHomCompSubIsoOfRepIso e g` and `subCompNormHomIsoOfRepIso e g`: for an
  isomorphism `e : M ≅ N` in `Rep R Q`, an isomorphism of short complexes
  from the complex of `M` at `g` to the complex of `N` at `g`. All three
  components are the image `i` of `e` under the forgetful functor
  `forget₂ (Rep R Q) (ModuleCat R)`. The two commuting squares hold because
  the morphism `e.hom` of representations commutes with the norm
  (`Rep.norm_comm`) and with `ρ(g)` (`Rep.applyAsHom_comm`).
- `normHomCompSubHomologyIsoOfRepIso e g` and
  `subCompNormHomHomologyIsoOfRepIso e g`: the induced isomorphisms of the
  homology objects, given by `ShortComplex.homologyMapIso` applied to the two
  short-complex isomorphisms above.

The representations `M` and `N` may have carriers in any universe; this is
the single universe parameter of each declaration, as in the source.

## Source correspondence

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M100.007 | `normHomCompSubIsoOfRepIso` (114–135) | `normHomCompSubIsoOfRepIso` |
| M100.008 | `subCompNormHomIsoOfRepIso` (137–158) | `subCompNormHomIsoOfRepIso` |
| M100.009 | `normHomCompSubHomologyIsoOfRepIso` (160–165) | `normHomCompSubHomologyIsoOfRepIso` |
| M100.010 | `subCompNormHomHomologyIsoOfRepIso` (167–173) | `subCompNormHomHomologyIsoOfRepIso` |

All four lie in the source section `RepresentationIso` (lines 110–175) with
`variable {R Q : Type} [CommRing R] [CommGroup Q] [Fintype Q]` at line 112.
Every unqualified original name above is in `LocalClassFieldTheory`; every
adapted name is in `Langlands.NYLL.LocalClassFieldTheory`.

The other units of the same source file are handled separately. M100.001
(`map_cyclicGenerator`) and M100.002 (the private `res_norm_eq`) are
Prop-valued targets in the sibling module `TateTransport/Initial/Statements`.
M100.003 and M100.004 (section `GroupEquiv`) use the source theorem
`res_norm_eq` in their bodies, and M100.005 and M100.006 are built from
them. These four will be adapted after a proof of the M100.002 target is
published, so that the bodies can call it.

## Modifications

- The source namespace `LocalClassFieldTheory` is prefixed by
  `Langlands.NYLL`.
- The single NYLL import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  is replaced by the Mathlib module
  `Mathlib.RepresentationTheory.Homological.FiniteCyclic`. Every constant
  used by these four definitions comes from Mathlib; no NYLL declaration is
  used.
- `noncomputable section` and `open CategoryTheory` are retained. The unused
  `open ClassFormation` is omitted.
- The section `RepresentationIso`, its `variable` line, the docstrings, the
  binders `{M N : Rep R Q} (e : M ≅ N) (g : Q)`, the result types and the
  bodies are copied verbatim from source lines 110–175.
- The module docstring keeps the source's explanation, restricted to the
  representation-isomorphism comparison in this file, and adds a
  modification notice.
- No instance, attribute or other declaration is added.

## Focused verification

The module compiles in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or
warnings. Inspection of `subCompNormHomHomologyIsoOfRepIso` reports one
universe parameter and only the standard axioms `propext`,
`Classical.choice` and `Quot.sound`. A private diagnostic module compiled
the verbatim source lines 25–177 in a separate namespace over Mathlib
imports. For each of the four definitions it checked
`@adapted = @original := rfl` as whole constants. So the adapted
declarations have the same complete types, including binder kinds, as the
originals and are definitionally equal to them.

## Scope and attribution

These are comparison isomorphisms only. They do not state or prove the local
class-field axiom, any Tate-cohomology cardinality, or reciprocity.

The original copyright and author header is retained. The unchanged
Apache-2.0 `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) accompany
this subset. The Lean file's module docstring carries a modification notice.

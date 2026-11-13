# Cyclic generators and norms under group isomorphisms

Adapted by Worker 66 from Naganori Yamaguchi, ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`, source
`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean`
(SHA-256 `cf2c48399c7de2b908cf83a147834c66d3cbe1a0965bf78e563e2beaaed593fa`).
Registered source: `external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`. The source file is readable under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source`.

## Statements

This module contains two Prop-valued targets. Neither is proved here.

**`map_cyclicGeneratorStatement e g hg`** (M100.001). Let `Q` and `P` be
groups in universe zero, `e : Q ≃* P` a group isomorphism and `g : Q` an
element that generates `Q`, recorded by the hypothesis
`hg : ∀ q : Q, q ∈ Subgroup.zpowers g`. The statement says that every
`p : P` lies in `Subgroup.zpowers (e g)`. In other words, `e g` generates `P`.

**`Langlands.NYLL.PortInternal.M100.d002Statement e A`** (M100.002). Let `R`
be a commutative ring and `Q`, `P` finite commutative groups, all in
universe zero, and let `e : Q ≃* P` be a group isomorphism and `A : Rep R P`
a representation (its carrier may lie in any universe). Write
`Ares := Rep.res e.toMonoidHom A` for `A` viewed as a representation of `Q`
through `e`. The statement says that the norm maps of `Ares` and of `A` are
equal as morphisms of `R`-modules:

```lean
let Ares : Rep R Q :=
  Rep.res e.toMonoidHom A
ModuleCat.ofHom Ares.norm.hom.toLinearMap =
  ModuleCat.ofHom A.norm.hom.toLinearMap
```

Both sides are endomorphisms of the same underlying module, because
restriction does not change the carrier. Mathematically, this is the
reindexing `∑ q : Q, ρ(e q) = ∑ p : P, ρ(p)` of the norm sum along the
bijection `e`.

## Source correspondence

| Unit | Original declaration and source lines | Adapted declaration |
| --- | --- | --- |
| M100.001 | theorem `map_cyclicGenerator` (33–41) | `map_cyclicGeneratorStatement` |
| M100.002 | private theorem `res_norm_eq` (50–62) | `Langlands.NYLL.PortInternal.M100.d002Statement` |

`map_cyclicGenerator` lies in section `CyclicGenerator` (lines 29–43) with
`variable {Q P : Type} [Group Q] [Group P]` at line 31. `res_norm_eq` lies in
section `GroupEquiv` (lines 45–108) with
`variable {R Q P : Type} [CommRing R] [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]`
at lines 47–48. Both original names are in `LocalClassFieldTheory`.
`map_cyclicGeneratorStatement` is in `Langlands.NYLL.LocalClassFieldTheory`.

## Modifications

- The source namespace is prefixed by `Langlands.NYLL`.
- Each theorem becomes a Prop-valued `def` whose body is exactly the source
  conclusion. The source proofs are omitted; each proof is a separate
  `lean.proof@1` obligation.
- M100.001 receives the `Statement` suffix. Its section `variable` line and
  its explicit binders `(e : Q ≃* P) (g : Q) (hg : ∀ q : Q, q ∈ Subgroup.zpowers g)`
  are retained in source order. The generator hypothesis `hg` does not occur
  in the conclusion. It is kept as a binder because it is a source
  hypothesis, so the target has exactly the source telescope.
- M100.002 is a private source theorem, so it has no stable public name. It
  is not in the task's unit table, but the listed source definitions
  `normHomCompSubResEquivIso` and `subCompNormHomResEquivIso` (M100.003,
  M100.004) use it in their bodies. It is therefore ported here as an unlisted
  same-module dependency. It receives the internal target name
  `Langlands.NYLL.PortInternal.M100.d002Statement`, following the port's
  `PortInternal.Mxxx.dyyy` rule for private source commands and the
  `Statement` suffix of the listed private-theorem target
  `Langlands.NYLL.PortInternal.M257.d009Statement`. Its section `variable`
  line and explicit binders `(e : Q ≃* P) (A : Rep R P)` are retained, and
  the body, including the `let Ares` binding, is copied verbatim. M100.003
  and M100.004 will be adapted with bodies that call a published proof of
  this target.
- The single NYLL import
  `Nyll.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.Construction.UnitCohomologyAxiom`
  is replaced by the Mathlib module `Mathlib.RepresentationTheory.Rep.Res`,
  which supplies, directly or through its own imports, `Subgroup.zpowers`, `MulEquiv`, `Rep`, `Rep.res`,
  `Rep.norm` and `ModuleCat.ofHom`. No NYLL declaration is used.
- The enclosing `noncomputable section` is retained. `open ClassFormation`
  and `open CategoryTheory` are unused here and omitted.

## Focused verification

The module compiles in environment `5c94c648-e8dc-4002-a50a-071ebf3f6096`
(Mathlib `5ed2965256430c3649e86755f9576b54eca72435`) with no errors or
warnings. Inspection reports
`statement_returns_prop: true` for both targets.
`map_cyclicGeneratorStatement` has no universe parameters, and `d002Statement`
has one, the carrier universe of `A`, as in the source.

A private diagnostic module compiled the verbatim source lines 25–177 in a
separate namespace over Mathlib imports, with `private` removed from
`res_norm_eq` in that copy only. It checked:

- the source theorem `map_cyclicGenerator`, with its complete telescope
  `∀ {Q P : Type} [Group Q] [Group P] (e : Q ≃* P) (g : Q) (hg : …)`, is
  accepted as a term of `∀ … , map_cyclicGeneratorStatement e g hg`, and
  `map_cyclicGeneratorStatement e g hg = ∀ p : P, p ∈ Subgroup.zpowers (e g)`
  holds by `rfl`;
- the source theorem `res_norm_eq`, with its complete telescope
  `∀ {R Q P : Type} [CommRing R] [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P] (e : Q ≃* P) (A : Rep R P)`,
  is accepted as a term of `∀ … , d002Statement e A`.

So each target is the source proposition.

## Scope and attribution

These are statements only; they assert no proof. They say nothing about
Tate cohomology, the local class-field axiom or reciprocity.

The original copyright and author header is retained. The unchanged
Apache-2.0 `licenses/NYLL/LICENSE` (SHA-256
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`) and
`licenses/NYLL/NOTICE` (SHA-256
`bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`) accompany
this subset. The Lean file's module docstring carries a modification notice.

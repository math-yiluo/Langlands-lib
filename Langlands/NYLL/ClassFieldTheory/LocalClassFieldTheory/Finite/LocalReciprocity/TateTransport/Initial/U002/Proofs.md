# NYLL M100.002: norms under restriction along a group isomorphism

This module proves the published Library proposition
`Langlands.NYLL.PortInternal.M100.d002Statement` by the theorem
`Langlands.NYLL.PortInternal.M100.d002`. The theorem's type is exactly that
proposition applied to its source parameters, `d002Statement e A`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `R Q P : Type`, the instances
`[CommRing R] [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]`, an
explicit group isomorphism `e : Q ≃* P` and an explicit representation
`A : Rep R P`. Like the statement, the theorem has one universe parameter,
the carrier universe of `A`.

Unfolding the published proposition gives

```lean
let Ares : Rep R Q :=
  Rep.res e.toMonoidHom A
ModuleCat.ofHom Ares.norm.hom.toLinearMap =
  ModuleCat.ofHom A.norm.hom.toLinearMap
```

that is, the norm endomorphism of `A` viewed as a `Q`-representation through
`e` equals the norm endomorphism of `A`, both as `R`-linear endomorphisms of
the common underlying module.

## Implemented proof

The complete proof body is

```lean
  let Ares : Rep R Q :=
    Rep.res e.toMonoidHom A
  apply congrArg ModuleCat.ofHom
  change Representation.norm Ares.ρ = Representation.norm A.ρ
  simp only [Representation.norm]
  exact Fintype.sum_equiv e.toEquiv
    (fun q : Q => Ares.ρ q)
    (fun p : P => A.ρ p) (fun _ => rfl)
```

The tactic `let` introduces the local name `Ares` for the restricted
representation. The goal is the published proposition; `apply congrArg
ModuleCat.ofHom` unifies with it up to definitional unfolding of
`d002Statement` and of its `let`, reducing it to the equality of the two
underlying linear maps.
By Mathlib's definition of `Rep.norm`, whose underlying linear map is
`Representation.norm A.ρ`, the `change` step restates the goal as
`Representation.norm Ares.ρ = Representation.norm A.ρ`, and `simp only`
unfolds `Representation.norm ρ = ∑ g, ρ g`. The remaining equality
`∑ q : Q, Ares.ρ q = ∑ p : P, A.ρ p` is the reindexing of a finite sum along
the bijection `e.toEquiv`, given by Mathlib's `Fintype.sum_equiv`; its
pointwise hypothesis `Ares.ρ q = A.ρ (e q)` holds by `rfl`, since the
restricted representation is `A.ρ` composed with `e.toMonoidHom`.

Apart from stating the type as the published proposition, this is the
original proof verbatim; no unfolding step had to be added. No auxiliary
declaration, extra hypothesis, instance or `simp` registration is introduced.
The development check reports no errors or warnings and only the axioms
`propext`, `Classical.choice` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.PortInternal.M100.d002Statement` in
  TateTransport.Initial.Statements.
- Mathlib's `Rep.res` (`Mathlib/RepresentationTheory/Rep/Res.lean`),
  `Rep.norm` (`Mathlib/RepresentationTheory/Rep/Basic.lean`),
  `Representation.norm` (`Mathlib/RepresentationTheory/Basic.lean`),
  `ModuleCat.ofHom` and `Fintype.sum_equiv` (the additive form of
  `Fintype.prod_equiv` in
  `Mathlib/Algebra/BigOperators/Group/Finset/Defs.lean`), all available
  through the Statements module's imports.

No other proof and no host class-formation, Tate or reciprocity theorem is
used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean:50–62`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean#L50-L62).
Lines 50–54 are the signature of the private theorem `res_norm_eq` and
55–62 its proof; it has no docstring. The section `GroupEquiv` declares
`{R Q P : Type} [CommRing R] [CommGroup Q] [CommGroup P] [Fintype Q] [Fintype P]`
at lines 47–48. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m100)
places this proof at M100.002 (source unit lines 50–65), with the internal
name `Langlands.NYLL.PortInternal.M100.d002`. The whole-file SHA-256 is
`cf2c48399c7de2b908cf83a147834c66d3cbe1a0965bf78e563e2beaaed593fa`,
recomputed by Worker 395 on 14 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.PortInternal.M100` |
| --- | --- |
| Asserted type of private `res_norm_eq` (M100.002) | Published `d002Statement` in TateTransport.Initial.Statements |
| Private proof `res_norm_eq` | This public theorem `d002` in TateTransport.Initial.U002.Proofs |

The adaptation renames the private source theorem to the port's internal
public name `d002` in `Langlands.NYLL.PortInternal.M100` (a private theorem
could not be imported by the later M100.003–M100.006 definitions that use it),
adds a docstring naming the source theorem, replaces the original import by
the sole published Statements import, omits the unused `open ClassFormation`,
`open CategoryTheory`, the `noncomputable section` and the section name while
keeping the section variables, and states the theorem's type as the published
proposition applied to `e A`. The proof body is unchanged.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 395's dated modification
record. Worker 395 extracted this proof directly from the pinned original and
the published statement. No unpublished project draft was reused, and there
are no project coauthors.

The unchanged inherited
[LICENSE](../../../../../../../../../licenses/NYLL/LICENSE) and
[NOTICE](../../../../../../../../../licenses/NYLL/NOTICE) are retained, with
SHA-256 values
`b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`
and `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`
respectively.

The approved environment is `5c94c648-e8dc-4002-a50a-071ebf3f6096`:
Lean 4.34.0 and Mathlib `5ed2965256430c3649e86755f9576b54eca72435`.
Development compilation is separate from acceptance. Publication under
`lean.proof@1` requires the Lake build, kernel and exact-target checks,
unchanged statement and dependency checks, independent semantic review and
Integrator publication.

This proof covers only M100.002. The Tate complex transports M100.003–M100.010
and any host class-formation, cup, transfer, Tate or reciprocity target are
separate work.

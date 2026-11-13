# NYLL M100.001: cyclic generators under group isomorphisms

This module proves the published Library proposition
`Langlands.NYLL.LocalClassFieldTheory.map_cyclicGeneratorStatement`
by the theorem `Langlands.NYLL.LocalClassFieldTheory.map_cyclicGenerator`.
The theorem's type is exactly that proposition applied to its source
parameters, `map_cyclicGeneratorStatement e g hg`.

Its sole direct import is
`Langlands.NYLL.ClassFieldTheory.LocalClassFieldTheory.Finite.LocalReciprocity.TateTransport.Initial.Statements`.
That published Lean/Markdown pair and its complete imported chain remain
unchanged.

## Target and parameters

The theorem has, in this order, implicit `Q P : Type`, the instances
`[Group Q] [Group P]`, an explicit group isomorphism `e : Q ≃* P`, an
explicit element `g : Q` and an explicit hypothesis
`hg : ∀ q : Q, q ∈ Subgroup.zpowers g`, saying that `g` generates `Q`. No
commutativity or finiteness is assumed.

Unfolding the published proposition gives

```lean
∀ p : P, p ∈ Subgroup.zpowers (e g)
```

that is, `e g` generates `P`.

## Implemented proof

The complete proof body is

```lean
  intro p
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hg (e.symm p))
  apply Subgroup.mem_zpowers_iff.mpr
  refine ⟨n, ?_⟩
  rw [← map_zpow e, hn, e.apply_symm_apply]
```

`intro p` works directly on the stated type. Since `g` generates `Q`,
`e.symm p ∈ Subgroup.zpowers g`, and Mathlib's `Subgroup.mem_zpowers_iff`
gives an integer `n` with `hn : g ^ n = e.symm p`. By the same lemma it
suffices to show `(e g) ^ n = p` for this `n`. Rewriting right to left with
`map_zpow e` turns `(e g) ^ n` into `e (g ^ n)`, then `hn` turns it into
`e (e.symm p)`, and `MulEquiv.apply_symm_apply` reduces this to `p`.

Apart from stating the type as the published proposition, this is the
original proof verbatim. No auxiliary declaration, extra hypothesis, instance
or `simp` registration is introduced. The development check reports only the
axioms `propext` and `Quot.sound`.

## Actual dependencies

- The published proposition
  `Langlands.NYLL.LocalClassFieldTheory.map_cyclicGeneratorStatement` in
  TateTransport.Initial.Statements.
- Mathlib's `Subgroup.mem_zpowers_iff`
  (`Mathlib/Algebra/Group/Subgroup/ZPowers/Basic.lean`), `map_zpow`
  (`Mathlib/Algebra/Group/Hom/Defs.lean`) and `MulEquiv.apply_symm_apply`,
  all available through the Statements module's imports.

No other proof and no host class-formation, Tate or reciprocity theorem is
used.

## Pinned source and declaration map

The source is Naganori Yamaguchi's
[`n-yamaguchi-0729/ClassFieldTheory`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/tree/fbd320cd8b1b06487c58227e92eb135794267709),
commit `fbd320cd8b1b06487c58227e92eb135794267709`, file
[`Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean:33–41`](https://github.com/n-yamaguchi-0729/ClassFieldTheory/blob/fbd320cd8b1b06487c58227e92eb135794267709/Nyll/ClassFieldTheory/LocalClassFieldTheory/Finite/LocalReciprocity/TateTransport.lean#L33-L41).
Line 33 is the retained docstring, 34–36 the signature and 37–41 the proof.
The section `CyclicGenerator` declares
`{Q P : Type} [Group Q] [Group P]` at line 31. The
[public partition](../../../../../../../../../notes/reuse/nyll-public-port/m097-m120.md#m100)
places this proof at M100.001 (source unit lines 34–49), the first unit of
M100. The whole-file SHA-256 is
`cf2c48399c7de2b908cf83a147834c66d3cbe1a0965bf78e563e2beaaed593fa`,
recomputed by Worker 96 on 13 November 2026 UTC from the retained snapshot.

| Original in `LocalClassFieldTheory` | Adapted in `Langlands.NYLL.LocalClassFieldTheory` |
| --- | --- |
| Asserted type of `map_cyclicGenerator` (M100.001) | Published `map_cyclicGeneratorStatement` in TateTransport.Initial.Statements |
| Proof `map_cyclicGenerator` | This theorem of the same adapted name in TateTransport.Initial.U001.Proofs |

The adaptation prefixes the namespace with `Langlands.NYLL`, replaces the
original import by the sole published Statements import, omits the unused
`open ClassFormation`, `open CategoryTheory`, the `noncomputable section` and
the section name while keeping the section variables, and states the
theorem's type as the published proposition applied to `e g hg`.

The retained source is registered as
`external-lean-reuse-snapshots-2026-10-21`, fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.

## Attribution, environment and scope

The Lean file retains the original 2026 Naganori Yamaguchi copyright,
Apache-2.0 and author header verbatim, including “Naganori Yamaguchi
(assisted by OpenAI Codex)”, followed by Worker 96's dated modification
record. Worker 96 extracted this proof directly from the pinned original and
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

This proof covers only M100.001. The norm comparison M100.002, the Tate
complex transports of M100 and any host class-formation, cup, transfer, Tate
or reciprocity target are separate work.

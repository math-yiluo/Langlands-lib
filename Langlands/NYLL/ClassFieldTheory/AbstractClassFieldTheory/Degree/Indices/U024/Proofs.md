# NYLL M006.024: cardinal kernel index and saturation

This proves the published proposition
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_kernel_eq_saturationStatement`
under the source-adapted theorem name
`Langlands.NYLL.ClassFormation.relativeIndexCardinal_kernel_eq_saturation`.
The theorem's type is exactly the named proposition applied to `d` and `hLK`.

The complete source scope is retained: independent universes `u v`, implicit
`G : Type u` and `D : Type v`, then `[Group G]` and `[Group D]`, explicit
`d : G →* D`, implicit `L K : Subgroup G`, and explicit `hLK : L ≤ K`.
There is no finiteness assumption and no normality assumption on `L` or `K`.
The conclusion has the source equality direction:

```lean
relativeIndexCardinal
  (show L ⊓ d.ker ≤ K ⊓ d.ker from inf_le_inf hLK le_rfl) =
relativeIndexCardinal
  (show L ≤ K ⊓ (L ⊔ d.ker) from fun _ hx ↦
    ⟨hLK hx, (show L ≤ L ⊔ d.ker from le_sup_left) hx⟩)
```

The implemented proof is the source's one-line argument,
`Cardinal.mk_congr (kernelCosetEquivSaturation d hLK)`.
The already published equivalence
`Langlands.NYLL.ClassFormation.kernelCosetEquivSaturation` has endpoints

```lean
(↑(K ⊓ d.ker) ⧸ (L ⊓ d.ker).subgroupOf (K ⊓ d.ker)) ≃
  (↑(K ⊓ (L ⊔ d.ker)) ⧸ L.subgroupOf (K ⊓ (L ⊔ d.ker)))
```

By the definitions of `relativeIndexCardinal` and
`intersectionIndexCardinal`, the two sides of the target are `Cardinal.mk`
of these exact coset types. `Cardinal.mk_congr` therefore proves the target
by definitional reduction. Both cardinalities lie in `Cardinal.{u}`; the
argument adds no lifts and does not identify `u` with `v`. Infinite coset
cardinalities are preserved. These are coset types even when `L` is
nonnormal; the equivalence construction uses the intrinsic normality of
`d.ker`.

The direct project imports are the unchanged published target module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U023.Statements`
and equivalence module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U006.Definitions`.
The former imports the cardinal-index data from `U010.Definitions` and
Mathlib's subgroup kernel module; the latter imports Mathlib's quotient-group
basics. The proof body uses only the published equivalence and Mathlib's
`Cardinal.mk_congr`, with the target and cardinal-index definitions reducing
definitionally. It needs neither the image-coset equivalence M006.022 nor the
image-index theorem M006.023, the quotient-tower equivalence, a tower-index
law, or a finite-index comparison. The inventory's preceding-unit edge is
a scheduling convention; these focused imports give the actual dependencies.

The original is Naganori Yamaguchi's ClassFieldTheory, commit
`fbd320cd8b1b06487c58227e92eb135794267709`, file
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`,
M006.024 at lines 256–265 (signature 258–264), with its section parameters
at lines 23–25. Its SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
The registered source is `external-lean-reuse-snapshots-2026-10-21`, content
fingerprint `26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The relevant source header, section, cardinal definitions, and complete
M006.024 declaration and proof were read. No applicable errata note was found.

Worker 185 made the focused extraction, namespace prefix, explicit published
target type, imports, module documentation and this Markdown. The theorem's
source name, docstring, scope, binder order and proof body are retained after
namespace adaptation. The target and its imported files are unchanged.
The original copyright, Apache-2.0 release and author header are retained.
The existing `licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE` remain the
applicable upstream license and notice.

This is the cardinal kernel-index identity for arbitrary groups and a group
homomorphism; it asserts no class-formation or local reciprocity theorem.

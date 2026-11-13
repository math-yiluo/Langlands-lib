# NYLL M006.023: image index and kernel saturation

Worker 184 adapted Naganori Yamaguchi's ClassFieldTheory, pinned commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Indices.lean`.
The source file SHA-256 is
`da0a361d29cf76e77dd0556ca8384838b7231183333a68643acbd1021c95ad71`.
It is retained under the registered source
`external-lean-reuse-snapshots-2026-10-21`, content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`.
The complete original file and the published target/data pairs were read.

The public theorem
`Langlands.NYLL.ClassFormation.intersectionIndexCardinal_image_eq_saturation`
proves exactly the already published
`Langlands.NYLL.ClassFormation.intersectionIndexCardinal_image_eq_saturationStatement`.
Its parameters retain the source section's independent universes `u v`,
implicit `{G : Type u} {D : Type v}`, `[Group G] [Group D]`,
then explicit `(d : G →* D) (L K : Subgroup G)` in that order.
The conclusion is

```lean
Cardinal.lift.{u} (intersectionIndexCardinal (L.map d) (K.map d)) =
  Cardinal.lift.{v}
    (intersectionIndexCardinal (K ⊓ (L ⊔ d.ker)) K)
```

The indices are cardinalities of actual left coset spaces. The assertion
holds for arbitrary subgroups, including infinite index, without containment,
finiteness or subgroup-normality hypotheses.

## Original correspondence and implemented proof

The closing theorem is source M006.023, lines 247–254 (signature 249–253).
The private helpers are source M006.015–022, lines 176–245, retained as
private declarations in this focused proof module. Their construction is
unchanged:

1. `subgroupMapRestriction` restricts `d` to the surjective homomorphism
   `K →* K.map d`. Surjectivity follows from subgroup-image membership.
2. For any `H : Subgroup D`, the source coset relation for
   `(H.comap d).subgroupOf K` holds exactly when the image elements satisfy
   the coset relation for `H.subgroupOf (K.map d)`. This follows by
   `map_mul` and `map_inv`.
3. `Quotient.map'` descends this restriction to cosets. Quotient induction
   and the relation equivalence prove injectivity; quotient induction and
   surjectivity on representatives prove surjectivity. `Equiv.ofBijective`
   packages these as `relativeCosetComapEquiv`.
4. `Subgroup.comap_map_eq` identifies `(L.map d).comap d` with
   `L ⊔ d.ker`. Within `K`, intersecting again with `K` adds a condition
   already supplied by every representative's subtype property.
   `Subgroup.quotientEquivOfEq` transports across this subgroup equality.
5. Composing gives an equivalence from
   `K ⧸ (K ⊓ (L ⊔ d.ker)).subgroupOf K` to
   `K.map d ⧸ (L.map d).subgroupOf (K.map d)`.
   Its `Equiv.lift_cardinal_eq`, reversed, proves the exact named target,
   preserving the two independent universe lifts.

The changes are the `Langlands.NYLL` namespace prefix, extraction to the
requested focused module, replacement of the broad source import by the
published U023 statement module, file documentation, and replacing the
closing theorem's displayed equation type by the exact named Statement.
The private helpers keep their source names and bodies. No additional public
helper, global instance or assumption is introduced.

## Actual dependencies and scope

The sole direct import is
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Indices.U023.Statements`.
It imports the published U010 cardinal-index definitions and Mathlib's
subgroup-kernel API. The proof uses Mathlib subgroup images, comaps,
`Subgroup.comap_map_eq`, left-coset relations and quotient induction,
`Quotient.map'`, `Equiv.ofBijective`, `Subgroup.quotientEquivOfEq`,
and `Equiv.lift_cardinal_eq`.

Mathlib's `Subgroup.index_comap_of_surjective` proves a natural-valued index
equality using an inline quotient bijection. It does not expose the needed
cross-universe cardinal equivalence; the source's private equivalence is
retained. The original `QuotientTower` import, the kernel-coset equivalence,
cardinal tower theorem and M006.024–025 proofs are not dependencies here.
This result asserts no host class-formation or reciprocity theorem.

## Development validation

The focused proof compiles with zero errors and warnings in approved
environment `5c94c648-e8dc-4002-a50a-071ebf3f6096` (Lean 4.34.0,
Mathlib `5ed2965256430c3649e86755f9576b54eca72435`). A separate private
check assigns the unapplied theorem constant to the complete expected
telescope at independent universes, confirming parameter order and visibility.
Declaration inspection reports only `propext`, `Classical.choice` and
`Quot.sound`. The check does not substitute for independent semantic review
or the submission's exact-target and kernel validation.

The original copyright, author and Apache-2.0 release header is retained.
The unchanged upstream license files remain at `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

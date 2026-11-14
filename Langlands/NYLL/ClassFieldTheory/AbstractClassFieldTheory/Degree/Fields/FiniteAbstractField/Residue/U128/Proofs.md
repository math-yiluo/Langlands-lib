# NYLL M010.128: the base finite abstract field has residue degree one

This file proves
`Langlands.NYLL.ClassFormation.FiniteAbstractField.base_residueDegreeStatement`
with the theorem
`Langlands.NYLL.ClassFormation.FiniteAbstractField.base_residueDegree`.

## Statement

The parameters are implicit `G : Type u` (arbitrary universe `u`) with
`[Group G]` and `[TopologicalSpace G]`, and explicit `D : DegreeData G`. The
declared type is exactly `base_residueDegreeStatement D`, which unfolds to
`(FiniteAbstractField.base G).residueDegree D = 1` in `ℕ+`. There is no
profiniteness or topological-group hypothesis.

In words: the distinguished base field, bundled as a field finite over itself
(`FiniteAbstractField.base G`), has positive absolute residue degree `1` with
respect to the degree datum `D`. That degree is the `Nat.card` of the actual
residue quotient `D.residueQuotient (baseField G)`, the quotient of
`⊤ : Subgroup ZHatMul` by the degree image of the base field.

The source `@[simp]` attribute is kept. Because the declared type is the
named proposition `base_residueDegreeStatement D`, the attribute registers
that proposition itself. A development check confirmed that `simp` proves
`base_residueDegreeStatement D` but does not rewrite the unfolded equation
`(FiniteAbstractField.base G).residueDegree D = 1`. That equation is
obtained by applying the theorem, `FiniteAbstractField.base_residueDegree D`,
which the kernel accepts by unfolding the definition.

## Proof

1. `Subtype.ext` reduces the `ℕ+` equation to equality of the underlying
   naturals. A `change` step then states the goal as
   `Nat.card (D.residueQuotient (baseField G)) = 1`. This holds by unfolding
   definitions: `FiniteAbstractField.residueDegree` (M010.127) is the
   `residueDegree` of `toFiniteResidueAbstractField` (M010.126); its field is
   `(FiniteAbstractField.base G).field = baseField G`; and
   `DegreeData.FiniteResidueAbstractField.residueDegree` is the pair
   `⟨Nat.card (D.residueQuotient K.field), _⟩`. The underlying natural of
   `1 : ℕ+` is `1`.
2. The degree image of the base field is everything:
   `D.fieldImage (baseField G) = ⊤`. Rewrite with the published
   `DegreeData.fieldImage_eq_map` (image of the underlying subgroup under
   `D.degree`) and `baseField_toSubgroup` (the base field's subgroup is `⊤`).
   Then Mathlib's `Subgroup.map_top_of_surjective` applied to
   `D.degree_surjective` closes the goal.
3. The residue quotient is a subsingleton. A `change` step unfolds
   `DegreeData.residueQuotient` to
   `↥(⊤ : Subgroup ZHatMul) ⧸ (D.fieldImage (baseField G)).subgroupOf ⊤`.
   Rewriting with step 2 and Mathlib's `Subgroup.subgroupOf_self` turns it into
   the quotient by `⊤`, and `QuotientGroup.subsingleton_quotient_top` applies.
4. The quotient is nonempty, containing `QuotientGroup.mk 1`. Mathlib's
   `Nat.card_unique` (for a nonempty subsingleton type) then gives
   `Nat.card = 1`.

The proof uses only the actual published residue degree, the actual base
field and the field `degree_surjective` of `D`. It uses no supplied or
replacement degree. The finiteness proof bundled by
`toFiniteResidueAbstractField` is not used, only the definitional value of
the degree.

## Change of route from the source

The source proof (lines 1181–1188) also starts with `Subtype.ext`. It then
casts injectively to `Cardinal`, rewrites with
`FiniteResidueAbstractField.residueDegreeCardinal_eq_coe` (M010.027), and
finishes with the cardinal lemma `DegreeData.residueDegreeCardinal_baseField`
(M010.020, source lines 152–163). The target of M010.020 is published, but its
proof was not in the Library or in staging when this proof was written. Its
proof belongs to another task. This proof therefore makes the same argument as
the source proof of M010.020 directly: surjectivity of the degree, then a
subsingleton quotient by `⊤`. It works with `Nat.card` instead of
`Cardinal.mk`, so the cast to `Cardinal` and M010.027 are not needed. No
M010.020 declaration is introduced or duplicated here.

## Imports and dependencies

The sole direct import is the published target module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Degree.Fields.FiniteAbstractField.Residue.Statements`.
Through it, the published `Residue.Definitions` module supplies
`FiniteAbstractField.base` and `residueDegree`, and its imports supply
`DegreeData.fieldImage_eq_map` (`Degree.Fields.U011.Proofs`) and
`baseField_toSubgroup` (`Degree.Fields.U004.Proofs`). The Mathlib lemmas are
taken at the approved pin `5ed2965256430c3649e86755f9576b54eca72435`:

- `Subgroup.map_top_of_surjective` and `Subgroup.subgroupOf_self` from
  `Mathlib/Algebra/Group/Subgroup/Map.lean`;
- `QuotientGroup.subsingleton_quotient_top` from
  `Mathlib/GroupTheory/QuotientGroup/Basic.lean`;
- `Nat.card_unique` from `Mathlib/SetTheory/Cardinal/Finite.lean`.

The checked axioms are `propext`, `Classical.choice` and `Quot.sound`.

## Provenance and attribution

The original is Naganori Yamaguchi's `n-yamaguchi-0729/ClassFieldTheory`,
commit `fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Degree/Fields.lean`
(file SHA-256 `841b30407b1f9f3eb64a30f6ccfa4f8ec555c791564a7e682b7c8ee23c2d156e`).
M010.128 is at lines 1181–1188, with universe `u` at line 30 and the section
variables at line 46. The readable original is retained under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
The registered source `external-lean-reuse-snapshots-2026-10-21` has fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`;
the attribution supplement `nyll-classfieldtheory-fbd320cd-supplement` has
fingerprint `a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`.

Modifications by Worker 473: the theorem is stated using the published
named target, the namespace is prefixed with `Langlands.NYLL`, the source
imports are replaced by the single focused import above, and the route of the
source proof is changed as described. The source's own proof of M010.020
(Subsingleton quotient by `⊤`) is adapted into this proof. The original
copyright, Apache-2.0 and author header is retained. The unchanged attribution
files are `licenses/NYLL/LICENSE`
(SHA-256 `b40930bbcf80744c86c46a12bc9da056641d722716c378f5659b9e555ef833e1`)
and `licenses/NYLL/NOTICE`
(SHA-256 `bf19eab77be48af60691e32428ed2126785de7d36f975d06f286d28d80f71e22`).

This support theorem supplies no host class-formation, reciprocity or
norm-containment result. Coordination Task 5905 records that it is needed
for the later unramified norm containment of NYLL M302.

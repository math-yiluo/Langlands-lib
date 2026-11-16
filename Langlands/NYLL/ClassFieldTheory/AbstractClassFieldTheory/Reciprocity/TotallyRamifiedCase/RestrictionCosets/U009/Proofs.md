# NYLL M080.009: `relativeCosetAction_eq_of_restriction_eq`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.relativeCosetAction_eq_of_restriction_eq`
has the telescope `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
(A : Rep ℤ G) (E : DegreeData.AbstractExtension G)
(M : FiniteGaloisSubextension E.base) (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
[hEnormal : (extensionSubgroup E.base E.field E.below).Normal]
(a : ambientFixedAddSubgroup A E.field)
(g t : E.base.toSubgroup ⧸ extensionSubgroup E.base M.field M.below)
(hres : abstractReciprocityRestriction E.base E.field M.field hME E.below g =
  abstractReciprocityRestriction E.base E.field M.field hME E.below t)`
and type
`relativeCosetAction_eq_of_restriction_eqStatement A E M hME a g t hres`.
That is the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.relativeCosetAction_eq_of_restriction_eqStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements`.
The instance argument `hEnormal` is inferred.

Write `G_K`, `G_E`, `G_M` for `E.base`, `E.field` and `M.field`, and `res`
for the restriction `G_K ⧸ G_M →* G_K ⧸ G_E`. The target says: for
`a ∈ A^{G_E}`, viewed in `A^{G_M}` through `fixedFieldInclusion`, if
`res g = res t`, then `relativeCosetAction` gives the same element of `A`
at `g` and at `t`. That element is `ρ(k) a` for a representative `k` of the
class.

## Implemented proof

1. `change` unfolds the statement wrapper to the equation
   `relativeCosetAction A E.base M.field M.below (fixedFieldInclusion … a) g =
   relativeCosetAction A E.base M.field M.below (fixedFieldInclusion … a) t`.
2. `refine Quotient.inductionOn₂' g t ?_ hres` reduces to representatives
   `x y : G_K`, with the hypothesis `hxy` that the classes of `x` and `y`
   have equal restrictions.
3. `change A.ρ x.1 a.1 = A.ρ y.1 a.1`. On a class `Quotient.mk'' x`,
   `relativeCosetAction` (M024.001, a `Quotient.liftOn'`) reduces to
   `A.ρ x.1` applied to the underlying element. The underlying element of
   `fixedFieldInclusion A E.field M.field hME a` (M028.001) is `a.1`. Both
   reductions are definitional.
4. `res` is a `QuotientGroup.map`, so `hxy` is definitionally the equality
   of the classes of `x` and `y` in `G_K ⧸ G_E`. Mathlib's
   `QuotientGroup.eq.mp` gives `x⁻¹ * y ∈ extensionSubgroup E.base E.field E.below`.
   Let `e : G_E` be the element `x⁻¹ * y`.
5. `hy : y = x * Subgroup.inclusion E.below e`, by `Subtype.ext` and `simp`.
6. Rewrite with `hy`. A `change` gives `A.ρ x.1 a.1 = A.ρ (x.1 * e.1) a.1`,
   `map_mul` and another `change` give
   `A.ρ x.1 a.1 = A.ρ x.1 (A.ρ e.1 a.1)`, and `rw [a.2 e]` closes the goal,
   since `a` is fixed by `e ∈ G_E`.

## Dependencies

- Imported published module:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements`.
  Through its imports it provides the target, `IntegralRepGroupType`
  (M002.001), `DegreeData.AbstractExtension` (M010.028),
  `FiniteGaloisSubextension` (M040.001) with its normality instance,
  `extensionSubgroup` (M004.002), `abstractReciprocityRestriction` (M075.005),
  `KummerTheory.ambientFixedAddSubgroup` (M023.001), `relativeCosetAction`
  (M024.001) and `fixedFieldInclusion` (M028.001).
- Mathlib: `Quotient.inductionOn₂'`, `QuotientGroup.eq`, `Subtype.ext`,
  `Subgroup.inclusion`, `simp` and `map_mul`.
- No unpublished result is used and no helper declaration is added.
- Axioms reported by the Lean service: `propext`, `Classical.choice` and
  `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
(file SHA-256 `c355b25591d40a48d3cf642a1015ae1f5b49d9a14df8a05516a2128c2b43856f`),
lines 409–441 (M080.009): the docstring at 409–410, the telescope and statement
at 411–427 and the proof at 427–441. The readable pinned source is retained
under
`/home/taskhub/pilot/literature/External Lean project reuse survey- pinned source snapshots, 21 October 2026/n-yamaguchi-0729--ClassFieldTheory/source/`.
Its registered sources are `external-lean-reuse-snapshots-2026-10-21`
(content fingerprint
`26e8c647ade044fe9bd4dd1f9d997d4ca12aaa4766e55ab31cb64ca9f8415e01`) and
`nyll-classfieldtheory-fbd320cd-supplement`
(`a81005c3aceabc51e9193cdc643d4dd81dd9d496dca2a0cf0111ce610d5b0330`).

Modifications by Worker 756, 16 November 2026:

- The namespace is prefixed with `Langlands.NYLL`, and the source import is
  replaced by the published statement module above. The noncomputable
  section, both `open` lines, the comment, the variable line, the namespaces
  and the docstring are kept.
- The theorem's type is written as the published
  `relativeCosetAction_eq_of_restriction_eqStatement A E M hME a g t hres`.
  The proof begins with the `change` of step 1, so that the
  `Quotient.inductionOn₂'` motive is computed from the unfolded equation as
  in the source.
- The source's `simp only [relativeCosetAction_mk, fixedFieldInclusion_coe]`
  (M024.002 and M028.002) is replaced by the definitional `change` of
  step 3. The published theorems of those names are stated through
  `Statement` wrappers, and both hold by `rfl`.
- The rest of the proof (steps 2 and 4–6) is the source's, line for line.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract result about group representations and finite Galois
quotients. It supplies no host class-formation, cup-product, transfer,
Tate-cohomology or reciprocity theorem.

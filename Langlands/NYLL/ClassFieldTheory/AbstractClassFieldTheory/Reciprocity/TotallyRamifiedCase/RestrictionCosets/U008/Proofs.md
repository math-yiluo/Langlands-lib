# NYLL M080.008: `commute_of_same_restriction_of_inertia_le`

## Exact target

The theorem
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.commute_of_same_restriction_of_inertia_le`
has the telescope `{G : IntegralRepGroupType} [Group G] [TopologicalSpace G]
(D : DegreeData G) [IsTopologicalGroup G] (E : DegreeData.AbstractExtension G)
(M : FiniteGaloisSubextension E.base) (hME : M.field.toSubgroup ≤ E.field.toSubgroup)
(hIE : (D.fieldInertia E.field).toSubgroup ≤ M.field.toSubgroup)
[hEnormal : (extensionSubgroup E.base E.field E.below).Normal]
(g t : E.base.toSubgroup ⧸ extensionSubgroup E.base M.field M.below)
(hres : abstractReciprocityRestriction E.base E.field M.field hME E.below g =
  abstractReciprocityRestriction E.base E.field M.field hME E.below t)`
and type
`commute_of_same_restriction_of_inertia_leStatement D E M hME hIE g t hres`.
That is the published target
`Langlands.NYLL.ClassFormation.FiniteGaloisSubextension.commute_of_same_restriction_of_inertia_leStatement`
of module
`Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements`.
The instance argument `hEnormal` is inferred.

Write `G_K`, `G_E`, `G_M` for `E.base`, `E.field` and `M.field`, and
`res` for `abstractReciprocityRestriction E.base E.field M.field hME E.below :
G_K ⧸ G_M →* G_K ⧸ G_E`. The target says: if `G_M ≤ G_E`, `G_E` is normal
in `G_K`, the inertia group `I_E = G_E ⊓ I` lies in `G_M`, and
`res g = res t`, then `Commute g t`.

## Implemented proof

The proof is the source's, after one `change`.

1. `change Commute g t` unfolds the statement wrapper. `rw [Commute]` then
   turns the goal into `SemiconjBy g t t`, which unfolds to
   `g * t = t * g`.
2. Choose representatives `a := Quotient.out g` and `b := Quotient.out t`
   in `G_K`. Then `mk' a = g` and `mk' b = t` in `G_K ⧸ G_M` by
   `Quotient.out_eq'`.
3. `hcosetE`: `a * b` and `b * a` have the same class in `G_K ⧸ G_E`.
   After `map_mul`, the classes of `a` and of `b` in `G_K ⧸ G_E` are
   `res g` and `res t`. Each equality is a two-step `calc`: the class in
   `G_K ⧸ G_E` equals `res` applied to the class in `G_K ⧸ G_M` by `rfl`,
   since `res` is a `QuotientGroup.map`, and then `congrArg res` is applied
   to step 2. Rewriting with these and `hres` closes the goal, because both
   sides become `res t * res t`.
4. Put `z := (a * b)⁻¹ * (b * a)`. Mathlib's `QuotientGroup.eq` turns
   `hcosetE` into `z ∈ extensionSubgroup E.base E.field E.below`.
   `Subgroup.mem_subgroupOf` turns that into `z.1 ∈ G_E`.
5. `hzDegree : D.degree z.1 = 1`. The degree map lands in
   `ZHatMul = Multiplicative ℤ̂`, which is commutative. After `dsimp` and
   `map_mul`/`map_inv`, `Multiplicative.ext` and a `change` reduce the goal
   to the additive identity `-(x + y) + (y + x) = 0` in `ℤ̂`, closed by
   `abel`.
6. Steps 4 and 5 give `z.1 ∈ D.fieldInertia E.field`, which is
   `E.field ⊓ D.inertia` with `D.inertia` the kernel of `D.degree`. So
   `hIE` gives `z.1 ∈ G_M`, and `Subgroup.mem_subgroupOf` gives
   `z ∈ extensionSubgroup E.base M.field M.below`.
7. A final `calc` gives `g * t = mk'(a * b) = mk'(b * a) = t * g` in
   `G_K ⧸ G_M`. The outer equalities use `map_mul` and step 2, and the
   middle one is `QuotientGroup.eq.mpr` applied to step 6.

## Dependencies

- Imported published module:
  `Langlands.NYLL.ClassFieldTheory.AbstractClassFieldTheory.Reciprocity.TotallyRamifiedCase.RestrictionCosets.Statements`.
  Through its imports it provides the target, `IntegralRepGroupType`
  (M002.001), `DegreeData`, `DegreeData.inertia` and
  `DegreeData.fieldInertia` (M010.002, M010.006, M010.012),
  `DegreeData.AbstractExtension` (M010.028), `FiniteGaloisSubextension`
  (M040.001) with its normality instance, `extensionSubgroup` (M004.002) and
  `abstractReciprocityRestriction` (M075.005).
- Mathlib: `Commute`, `Quotient.out`, `Quotient.out_eq'`,
  `QuotientGroup.mk'`, `QuotientGroup.eq`, `Subgroup.mem_subgroupOf`,
  `map_mul`, `map_inv`, `Multiplicative.ext` and the `abel` tactic.
- No unpublished result is used and no helper declaration is added.
- Axioms reported by the Lean service: `propext`, `Classical.choice` and
  `Quot.sound` only.

## Source and modifications

Adapted from Naganori Yamaguchi, `n-yamaguchi-0729/ClassFieldTheory`, commit
`fbd320cd8b1b06487c58227e92eb135794267709`,
`Nyll/ClassFieldTheory/AbstractClassFieldTheory/Reciprocity/TotallyRamifiedCase/RestrictionCosets.lean`
(file SHA-256 `c355b25591d40a48d3cf642a1015ae1f5b49d9a14df8a05516a2128c2b43856f`),
lines 323–407 (M080.008): the docstring at 323–324, the telescope and statement
at 325–339 and the proof at 339–407. The readable pinned source is retained
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
- The theorem's type `Commute g t` is written as the published
  `commute_of_same_restriction_of_inertia_leStatement D E M hME hIE g t hres`.
  The proof begins with `change Commute g t` to unfold it.
- The source cites `KummerTheory.mem_extensionSubgroup_iff` (M022.001) in
  steps 4 and 6. The published theorem of that name is stated through a
  `Statement` wrapper. Mathlib's `Subgroup.mem_subgroupOf` is used in its place: it
  states the same equivalence, because `extensionSubgroup` is an
  abbreviation for `subgroupOf`.
- The rest of the proof is the source's, line for line.

The original copyright and author header is retained; see
`licenses/NYLL/LICENSE` and `licenses/NYLL/NOTICE`. No imported Lean or
Markdown file is modified.

This is an abstract group-theoretic result about degree data and finite
Galois quotients. It supplies no host class-formation, cup-product,
transfer, Tate-cohomology or reciprocity theorem.

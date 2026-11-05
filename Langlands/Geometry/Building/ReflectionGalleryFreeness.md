# Reflection-gallery deletion and chamber freeness

This module proves the published proposition
`Langlands.Geometry.Building.ReflectionGallery.ReflectionGalleryFreenessStatement`
without changing its interface or hypotheses. Its finite-word proof was
developed by Worker 1622 and is reused with credit here; Worker 1632 prepared
the proof contribution and this expanded explanation. This is internal
group-action mathematics derived directly from the five published laws, with
no external theorem or formalization serving as its source.

All declarations belong to
`Langlands.Geometry.Building.ReflectionGallery`. The group `G : Type uG` and
chamber type `X : Type uX` have arbitrary independent universes, with only
`[Group G]` and `[MulAction G X]` as typeclass hypotheses. For `S : Set G`,
`C : X`, and `separates : G → X → X → Prop`,
`IsSeparationSystem S C separates` supplies exactly the existing five laws:
no self-separation, the triangle alternative, covariance by
`g⁻¹ * t * g`, involutivity of every generator, and
`separates t C (s • C) ↔ t = s` for every `s ∈ S` and every label `t : G`.
The exchange induction allows arbitrary separating labels; they need not
belong to `S`.

`IsSeparationSystem.exchange` inducts on a list `L` of elements of `S`.
From `separates t C (L.prod • C)` it produces another list `L'` in `S`
such that `L'.length + 1 = L.length` and
`t * L.prod = L'.prod`. The empty list contradicts no self-separation.
For `L = s :: K`, the triangle law splits at `s • C`. Separation on
the first edge gives `t = s` by adjacency, and `s * s = 1` cancels
the first letter. In the other case covariance transforms the separating
label to `s⁻¹ * t * s`, acting on the tail from `C`. The induction
hypothesis gives `K'`, and the new list is `s :: K'`. The product
identity follows from
`t * (s * K.prod) = s * ((s⁻¹ * t * s) * K.prod)`.

`IsSeparationSystem.prod_eq_one_of_smul_eq` uses strong induction on
list length. If a nonempty word `s :: K` fixes `C`, involutivity gives
`K.prod • C = s • C`. Adjacency therefore gives
`separates s C (K.prod • C)`. Exchange on the tail gives `K'` with
`K'.length + 1 = K.length` and
`s * K.prod = K'.prod`. Thus `K'` represents the original word's
group element, still fixes `C`, and has two fewer letters. Strong
induction makes its product, and hence the original product, equal to `1`.
The empty word has product `1`.

The imported `Langlands.Group.TitsSystem.exists_word_of_mem_closure` expresses each
`w ∈ Subgroup.closure S` as `L.prod` for a list `L` in `S`, assuming
only involutivity of the generators. Subgroup-closure induction uses a
singleton for a generator, the empty list for `1`, and concatenation for
multiplication. For inversion it reverses the list: involutivity gives
`s⁻¹ = s` for each letter, and the noncommutative reverse-product
identity gives `(L.reverse).prod = L.prod⁻¹`. This is algebraic subgroup
closure; no topology is involved.

`IsSeparationSystem.eq_one_of_smul_eq` combines this word representation
with the returning-word result. The final theorem
`reflectionGalleryFreeness : ReflectionGalleryFreenessStatement.{uG, uX}`
introduces all the globally quantified data and applies that lemma.
It proves that every `w ∈ Subgroup.closure S` satisfying `w • C = C`
equals `1` in the original group `G`.

Applying this result to affine Weyl chambers still requires proving all
five separation laws for the actual affine action and proving that the
selected adjacent reflections generate the relevant affine Weyl group.
Chamber transitivity is also a separate obligation. This proof adds no
transitivity, freeness, Coxeter presentation, geometric generation,
faithfulness, finiteness, or stronger separation hypotheses.

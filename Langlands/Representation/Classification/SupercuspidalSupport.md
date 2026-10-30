# Supercuspidal support for `GL_n`

Author: Worker 23.

This module defines Zelevinsky's support of an irreducible representation of
`GL_n(F)`: a finite multiset `{ρ_1, …, ρ_k}` of supercuspidal classes such that the
representation is an irreducible subquotient of `ρ_1 × ⋯ × ρ_k`. The support is
recorded by relations on a given representation `π`. This module does not prove
that a support exists, that it is unique, or that some ordering of it contains
`π` as a subrepresentation. These are the content of Zelevinsky's Proposition
1.10. They are stated separately, for positive rank `n > 0` and irreducible
smooth `π`, in `Classification/SupercuspidalSupportStatement`:

- `GLSupercuspidalEmbeddingStatement` asserts that `π` embeds into a product of
  supercuspidal representatives: `T.IsCuspidalSubrepresentation ρ π` for some
  `ρ : Fin k → CuspidalDatum`. The theorem `glSupercuspidalEmbedding` in
  `Classification/SupercuspidalEmbeddingProof` proves it, with the field and
  supercuspidal-factor universes independent. If `s` is the multiset of
  `List.ofFn ρ`, then `T.IsSupercuspidalEmbeddingSupport π s` holds by
  definition. It follows that `T.IsSupercuspidalSupport π s` by
  `IsSupercuspidalEmbeddingSupport.isSupercuspidalSupport`. So every irreducible
  smooth representation of `GL_n(F)`, `n > 0`, with carrier in
  `Type (max uF uV)` has a support and an embedding ordering. The Library has
  no separately named theorem for this one-step consequence.
- `GLSupercuspidalSupportUniquenessStatement` asserts that any two supports of
  `π` are equal. It is unproved, and so is the conjunction
  `GLSupercuspidalSupportStatement` of the two statements.

Rank zero is outside both statements, and the embedding theorem says nothing
about uniqueness.

## Subquotients in the smooth category

These results are in namespace `Langlands.SmoothRep`, for any commutative ring
`R` and topological group `G`. They concern the published relation
`IsSubquotient B A` of `Category/Subquotients`, which asks for an actual invariant
submodule `S` of `A`, an actual invariant submodule of `S`, and an isomorphism
from `B` to the resulting quotient.

- `hom_hom_injective e` and `hom_hom_surjective e`: the underlying map of an
  isomorphism `e : A ≅ B` in the smooth category is injective and surjective.
- `isSubquotient_iff_exists`: `IsSubquotient B A` holds exactly when some smooth
  representation `C` has an injective morphism `C ⟶ A` and a surjective
  morphism `C ⟶ B`. For the converse direction the proof takes the image of
  `C` in `A` and the kernel of the surjection.
- `IsSubquotient.of_iso_right`, `IsSubquotient.of_iso_left` and
  `isSubquotient_iff_of_iso`: the relation is invariant under isomorphisms of
  either argument.
- `IsSubrepresentation.isSubquotient` and `IsQuotient.isSubquotient`: a
  subrepresentation, or a quotient, is a subquotient.

## Products of supercuspidal representations

These definitions are in namespace `Langlands.PadicField.TopologicalData`, for a
p-adic field `F` and a realization `T : F.TopologicalData`, whose topology is used
throughout. A cuspidal datum `ρ : T.CuspidalDatum` is the published
`Classification/Segments` structure: a rank `r > 0` and an isomorphism class of
supercuspidal representations of `GL_r(F)` with carriers in `Type uV`. Let
`ρ : Fin k → CuspidalDatum` have ranks `r_i`, and let `h` prove
`∑ i, r_i = n`.

- `T.cuspidalShape ρ h` is the block shape `(r_1, …, r_k)` of `n`.
- `T.cuspidalProductInduced ρ h A`, for actual supercuspidal representations
  `A i` of `GL_(r_i)(F)`, is `A_1 × ⋯ × A_k`. It is the published normalized
  product induction `T.normalizedProductInductionFunctor` of
  `Induction/BlockFactors`, from the standard upper block parabolic of this
  shape. Its carrier is in `Type (max uF uV)`.
  `cuspidalProductInduced_representation` unfolds it.
- `T.cuspidalProductInducedIsoOfRepresented h hA hA'` is an isomorphism between
  the products for two families of representatives `A` and `A'` of the same
  data. It applies the induction functor to isomorphisms of the factors.

## Constituents and embeddings

For `π` a smooth representation of `GL_n(F)` with carrier in `Type (max uF uV)`:

- `T.IsCuspidalConstituent ρ π` states that the ranks of `ρ` add up to `n`, and
  that for some representatives `A i` of the classes `ρ_i`, `π` is irreducible
  and is a subquotient of `A_1 × ⋯ × A_k`. This is Zelevinsky's
  `ω ∈ JH(ρ_1 × ⋯ × ρ_k)`: Zelevinsky's `JH` is the set of Jordan–Hölder
  constituents of a representation of finite length, and those are exactly its
  irreducible subquotients. The Lean relation neither uses nor asserts that
  `A_1 × ⋯ × A_k` has finite length.
- `T.IsCuspidalSubrepresentation ρ π` states that the ranks add up to `n`, and
  that for some representatives, `π` is irreducible and embeds into
  `A_1 × ⋯ × A_k` (the published relation
  `Classification.IsIrreducibleSubrepresentation` of `Classification/Segments`).
- `isCuspidalConstituent_iff` and `isCuspidalSubrepresentation_iff`: for any
  given representatives `A` of `ρ`, the relations hold exactly when they hold
  with these representatives.
- `IsCuspidalSubrepresentation.isCuspidalConstituent`: an embedding gives a
  constituent.
- `IsCuspidalConstituent.of_iso` and `IsCuspidalSubrepresentation.of_iso`: both
  relations are invariant under isomorphism of `π`.

The order of `ρ` matters in both relations as stated. The Lean code does not
assert that the constituent relation is independent of the order.

## Supports

For `s` a multiset of cuspidal data:

- `T.IsSupercuspidalSupport π s` states that some list `ρ_1, …, ρ_k` whose multiset
  is `s` (written as `List.ofFn ρ`) satisfies `T.IsCuspidalConstituent ρ π`.
- `T.IsSupercuspidalEmbeddingSupport π s` states that some such ordering
  satisfies `T.IsCuspidalSubrepresentation ρ π`. This is the ordering in the last
  sentence of Zelevinsky's Proposition 1.10.
- `IsSupercuspidalEmbeddingSupport.isSupercuspidalSupport`: an embedding support
  is a support.
- `IsSupercuspidalSupport.of_iso` and `IsSupercuspidalEmbeddingSupport.of_iso`:
  both relations are invariant under isomorphism of `π`.
- `IsSupercuspidalSupport.sum_rank`: the ranks of a support add up to `n`.
- `T.supercuspidalSupport π` is a support of `π` chosen with
  `Classical.choose`, and `0` when `π` has none. It is described only under
  hypotheses:
  - `isSupercuspidalSupport_supercuspidalSupport`: if `π` has a support, then
    `T.supercuspidalSupport π` is one.
  - `IsSupercuspidalSupport.eq_supercuspidalSupport`: if the supports of `π` are
    unique, then every support of `π` equals `T.supercuspidalSupport π`.

Neither hypothesis is proved here. For irreducible `π` of positive rank, the
first one follows from `glSupercuspidalEmbedding`, as explained at the top of
this file. The second one is the unproved
`GLSupercuspidalSupportUniquenessStatement`.

## Sources

A. V. Zelevinsky, *Induced representations of reductive p-adic groups II. On
irreducible representations of GL(n)*, Ann. Sci. ENS (4) 13 (1980), 165–210
(registered source `zelevinsky-1980-induced-ii`, SHA-256
`663c79f2ee236626385d242d83107410c1a3291ba5584d4b8abee9cf8af428ac`). Section 1.10,
printed p. 174 (PDF page 11):

> Denote by 𝒞 the set of equivalence classes of irreducible cuspidal
> representations of groups G_n (n = 1, 2, …).
>
> PROPOSITION. — Let ω ∈ Irr G_n. There exists a partition (n_1, …, n_r) of n and
> cuspidal representations ρ_i ∈ Irr G_{n_i} such that ω ∈ JH(ρ_1 × … × ρ_r). The
> multiset {ρ_1, …, ρ_r} on 𝒞 (cf. list of notations) is determined by ω; it is
> called the support of ω (notation supp ω = {ρ_1, …, ρ_r}). One can choose an
> ordering (ρ_{i_1}, …, ρ_{i_r}) of supp ω such that ω can be embedded into
> ρ_{i_1} × … × ρ_{i_r} (see [I], 2.5, 2.9).

The same section calls a representation cuspidal when it is admissible and its
Jacquet modules `r_{β,α}(ρ)` vanish for all proper standard parabolics `β < α`.
The cuspidal data of `Classification/Segments` are classes of the published
`GeneralLinear.IsSupercuspidal` (`Classification/Supercuspidal`). That predicate
asks for admissibility and vanishing coinvariants for every proper block
parabolic and every conjugate of its unipotent radical. The conjugates of the
standard radicals are included in the predicate rather than obtained by a
reduction theorem. The module does not prove that the two conditions agree. The
product `ρ_1 × ⋯ × ρ_r` is
normalized parabolic induction from the standard upper block parabolic, as in
the published `Induction/BlockFactors.md` (Zelevinsky 1980, sections 1.1–1.7,
pp. 170–173).

| Zelevinsky 1980, 1.10 | Lean |
| --- | --- |
| partition (n_1, …, n_r) of n, cuspidal ρ_i ∈ Irr G_{n_i} | `ρ : Fin k → CuspidalDatum`, `h : ∑ i, (ρ i).rank = n`, `T.cuspidalShape ρ h` |
| ρ_1 × … × ρ_r | `T.cuspidalProductInduced ρ h A` for representatives `A` |
| ω ∈ JH(ρ_1 × … × ρ_r) | `T.IsCuspidalConstituent ρ π` |
| the multiset {ρ_1, …, ρ_r} on 𝒞 | `(List.ofFn ρ : Multiset _)` |
| support of ω | `T.IsSupercuspidalSupport π s`, `T.supercuspidalSupport π` |
| ω embedded into ρ_{i_1} × … × ρ_{i_r} | `T.IsCuspidalSubrepresentation ρ π`, `T.IsSupercuspidalEmbeddingSupport π s` |
| existence, "determined by ω", existence of the ordering | not asserted in this module; stated for `n > 0` in `SupercuspidalSupportStatement` |

G. Henniart, *Une preuve simple des conjectures de Langlands pour GL(n) sur un
corps p-adique*, Invent. Math. 139 (2000), 439–455 (registered source
`henniart-2000-simple-proof`, SHA-256
`be283c3e8187f1eed365537c72379c3e06e7791756954c2ac783c6beea2979de`), section 1.9,
printed p. 443 (PDF page 5), uses the same notion: "À chaque Π_{i,0}, on peut
associer son support supercuspidal [Π_{i,0}], qui est un élément du Z-module libre
R_A(F) de base l'union (disjointe) des A^0_F(n) pour n ≥ 1". A multiset of
supercuspidal classes is such an element with nonnegative coefficients.

The subquotient lemmas of the first section are derived infrastructure; they are
elementary algebra about the published relation and have no literature source.

## Universes and scope

Supercuspidal blocks have carriers in `Type uV`, as in the published cuspidal
data. Their products, and the represented `π`, have carriers in
`Type (max uF uV)`, the universe of the published segment induced
representations. The field `F` is any p-adic field in `PadicField.{uF} p`; all
`n` and all `k`, including `k = 0` (then `n = 0`), are allowed.

Worker 1058 updated the status of the support theorems for the 2026-10-29
documentation audit; the Lean file is unchanged.

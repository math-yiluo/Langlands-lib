# Root data of the centralizers of cocharacters

Author: Worker 712.

This is a derived internal support module for the proof of
`SplitCommonTorusIsomorphismStatement` (the Isomorphism Theorem for two
connected reductive groups sharing a split maximal torus, Milne, *Algebraic
Groups* (2017), Theorem 23.25 and Remark 23.26 in the case where the isomorphism
of root data is the identity of the character lattice). It does two things.

1. It restricts a root pairing to the roots annihilated by a fixed coweight, and
   shows that for a root datum `P` of a split maximal torus `i : T ⟶ G` and a
   cocharacter `ν` of `T`, this restriction is a root datum of `T` in a closed
   representative of the centralizer of `ν`.
2. It uses this to derive the Isomorphism Theorem from the rank-one case
   `SplitRankOneCommonTorusIsomorphismStatement` and the gluing step
   `SplitCommonTorusLeviGluingStatement` alone. The Library's earlier reduction
   `SplitCommonTorusIsomorphism.splitCommonTorusIsomorphismStatement_of_prerequisites`
   (module `Reductive.SplitIsomorphismReduction`) also took the root-datum
   existence statement `RootDatumExistenceStatement` as a hypothesis, only to
   obtain root data of these centralizers. This module builds those root data
   directly.

Throughout, `k : Type u` is a field and all group schemes are over
`Spec (CommRingCat.of k)`. The notation is the Library's:

- `roots i` is the set of nonzero characters of `T` with nonzero weight space on
  the Lie algebra of `G`.
- `latticePairing T` is the pairing between the character and cocharacter
  lattices of `T`.
- `Dynamic.centralizer χ` is the centralizer subgroup functor of a cocharacter
  `χ : 𝔾ₘ ⟶ G`. For a cocharacter `ν` of `T` the cocharacter of `G` is
  `CommGroupScheme.groupHom ν ≫ i`. `F.IsRepresentedBy z` says that the closed
  subgroup `z : Z ⟶ G` is a monomorphism with range `F`.
- `IsRootDatumOf i P` says three things. The pairing of `P` is
  `latticePairing T`. The roots of `P` are `roots i`. Every reflection
  `P.reflection j` is the action `χ ↦ σ⁻¹ ≫ χ` of a rational point of `G`
  normalizing `i` through an automorphism `σ` of `T`.

## Linear algebra

For a root pairing `P : RootPairing ι R M N` over a commutative ring and a
coweight `y : N`:

- `orthogonalIndices P y` is the set of indices `j` with
  `P.toLinearMap (P.root j) y = 0`.
- `reflectionPerm_mem_orthogonalIndices_iff P y hi j`: if `i` lies in
  `orthogonalIndices P y`, then `P.reflectionPerm i j` lies in it exactly when
  `j` does.
- `orthogonalRootPairing P y : RootPairing (orthogonalIndices P y) R M N` keeps
  the pairing of `P`, its roots and coroots indexed by `orthogonalIndices P y`,
  and the restrictions of the reflection permutations `P.reflectionPerm i` for
  `i` in `orthogonalIndices P y`. The simp lemmas
  `orthogonalRootPairing_toLinearMap`, `orthogonalRootPairing_root`,
  `orthogonalRootPairing_coroot` and `orthogonalRootPairing_reflection` say that
  the pairing, the roots, the coroots and the reflections are those of `P`.

## Group schemes

- `IsRootDatumOf.orthogonalRootPairing hP ν z hrep t ht hroots`: let `G` and `Z`
  be affine over `k` and let `P : RootDatum J (characterLattice T)
  (cocharacterLattice T)` satisfy `IsRootDatumOf i P`. Let `ν` be a cocharacter
  of `T`. Let `z : Z ⟶ G` represent `Dynamic.centralizer (groupHom ν ≫ i)` and
  let `t : T ⟶ Z` satisfy `t ≫ z = i`. Suppose that `roots t` is the set of
  roots `α` of `i` with `latticePairing T α ν = 0`. Then
  `IsRootDatumOf t (orthogonalRootPairing P ν)`.
- `splitCommonTorusIsomorphism_of_rankOne_of_leviGluing hA hC`: from
  `hA : SplitRankOneCommonTorusIsomorphismStatement.{u}` and
  `hC : SplitCommonTorusLeviGluingStatement.{u}`, the theorem concludes
  `SplitCommonTorusIsomorphismStatement.{u}`.

No sorry and no new axioms are used; the theorems depend on `propext`,
`Classical.choice` and `Quot.sound` only.

## Proofs

`reflectionPerm_mem_orthogonalIndices_iff` rewrites `P.root (P.reflectionPerm i j)`
as `P.root j - ⟨P.root j, P.coroot i⟩ • P.root i` (Mathlib's
`RootPairing.reflectionPerm_root`). Pairing with `y` and using
`⟨P.root i, y⟩ = 0` leaves `⟨P.root j, y⟩`. Hence the reflection permutations of
orthogonal roots restrict to permutations of `orthogonalIndices P y`, and the
root pairing axioms for `orthogonalRootPairing` are those of `P` at the same
indices.

`IsRootDatumOf.orthogonalRootPairing` checks the three conditions.

- The pairing is that of `P`, hence `latticePairing T`.
- The roots of the restriction are the roots `P.root j` with
  `latticePairing T (P.root j) ν = 0`. Since the roots of `P` are `roots i`,
  this is the set of roots of `i` orthogonal to `ν`, which is `roots t` by
  `hroots`.
- For an orthogonal index `j`, `IsRootDatumOf i P` gives a rational point `n` of
  `G` normalizing `i` through an automorphism `σ` of `T` with
  `P.reflection j` equal to `χ ↦ σ⁻¹ ≫ χ`. Since `⟨P.root j, ν⟩ = 0`, the
  reflection fixes `ν`, so `σ` fixes the cocharacter `ν`
  (`LeviGluing.cocharacter_comp_eq_of_reflection`, module
  `Reductive.SplitLeviGluingSimpleGeneration`). Hence the constant point `n`
  centralizes `groupHom ν ≫ i` (`LeviGluing.constantPoint_mem_centralizer`,
  same module). Since `z` represents this centralizer, `n` is `m ≫ z` for a
  rational point `m` of `Z` (`SubgroupFunctor.mem_range`). As `z` is a
  monomorphism and `t ≫ z = i`, the point `m` normalizes `t` through the same
  `σ` (`IsNormalizingPoint.of_comp`). The reflection of the restriction at `j` is
  `P.reflection j`, so it is realized by `m`.

`splitCommonTorusIsomorphism_of_rankOne_of_leviGluing` applies `hC` to the given
data. For the remaining hypothesis of `hC`, take a cocharacter `ν` such that any
two roots of `i₁` orthogonal to `ν` are linearly dependent, and representatives
`z₁ : Z₁ ⟶ G₁`, `z₂ : Z₂ ⟶ G₂` of the centralizers with `t₁ ≫ z₁ = i₁`,
`t₂ ≫ z₂ = i₂`.

- `Z₁` and `Z₂` are connected reductive by the Library's published
  `dynamicCentralizerReductive`.
- `t₁` and `t₂` are maximal tori by `IsMaximalTorus.of_comp`, since `i₁` and
  `i₂` are.
- The roots of `t₁` and `t₂` are the roots of `i₁` and `i₂` orthogonal to `ν`, by
  the Library's published `dynamicCentralizerRoots`.
- So `orthogonalRootPairing P₁ ν` and `orthogonalRootPairing P₂ ν` are root data
  of `t₁` and `t₂`, by `IsRootDatumOf.orthogonalRootPairing`.
- The reindexing `e : J₁ ≃ J₂` matches the roots, so it preserves
  orthogonality to `ν`. It restricts to `e' : orthogonalIndices P₁ ν ≃
  orthogonalIndices P₂ ν`, which still matches roots and coroots.
- Any two roots of `t₁` are roots of `i₁` orthogonal to `ν`, hence linearly
  dependent.

Then `hA` applied to `Z₁`, `Z₂`, `t₁`, `t₂`, the two restricted root data and
`e'` gives an isomorphism `φ : Z₁ ≅ Z₂` with `t₁ ≫ φ.hom = t₂`, as `hC` requires.

## Provenance

The restriction of a root datum to the roots orthogonal to a cocharacter is the
root datum of the corresponding Levi subgroup. This is Milne, *Algebraic Groups*
(2017), Proposition 21.90(a), printed p.453 (PDF p.469): for a set `I` of simple
roots, `L_I = C_G(T_I)` is split reductive with root datum
`(X(T), Φ_I, α ↦ α^∨)`. The groups `G_α` of semisimple rank one in Milne's proof
of the isogeny theorem (23.16-23.17, printed p.490, PDF p.506; Theorem 21.11,
printed p.428) are the same construction. Here the centralizer is that of an
arbitrary cocharacter `ν` and the roots are those orthogonal to `ν`, as in the
published `SplitCommonTorusLeviGluingStatement`. The realization of the
reflections uses the Weyl representatives provided by `IsRootDatumOf` rather
than Milne's argument with root groups. The official errata to Milne (snapshot
2026-11-02) have no entry for p.453 or for pp.490-493.

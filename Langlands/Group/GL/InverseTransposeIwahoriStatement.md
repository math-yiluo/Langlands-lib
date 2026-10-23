# Inverse-transpose transport of block Iwahori data

Author: Worker 204.

This module states how the published inverse transpose acts on the actual
block Iwahori data of the general linear group. Every new declaration is a
transparent `def` returning `Prop`. The module proves none of these claims.
All names below belong to `Langlands.GeneralLinear.BlockShape`.

## Existing constructions used

No new carrier, map, subgroup or predicate is constructed. The module only
imports and uses:

- `GeneralLinear.inverseTranspose n R` from `Group.GL.Maps`. This is the
  published group automorphism `g ↦ (g⁻¹)ᵀ` of `GL_n(R)`, a `MulEquiv`. Its
  `toMonoidHom` is the underlying group homomorphism.
- `T.generalLinearInverseTranspose n` from the same module. After installing
  the supplied `T.topology` on `F.Carrier`, it is by definition the published
  continuous automorphism `GeneralLinear.inverseTransposeContinuous n F.Carrier`,
  whose underlying multiplicative equivalence is `inverseTranspose n F.Carrier`.
  Its `toMonoidHom` and its `continuous` certificate are passed to Mathlib's
  `OpenSubgroup.comap`.
- The actual subgroups `B.unipotentSubgroup R` (lower blocks vanish, identity
  diagonal blocks), `B.oppositeUnipotentSubgroup R` (upper blocks vanish,
  identity diagonal blocks) and `B.leviSubgroup R` (the range of the block
  diagonal embedding), from `Group.GL.Blocks` and `Group.GL.OppositeBlocks`.
- The block-scalar homomorphism `B.blockScalar R` and the predicate
  `B.HasBlockIwahoriFactorization T`, unchanged, from
  `Group.GL.BlockIwahoriDefinitions`.

## The six clauses

The first four clauses are algebraic and are stated for a block shape
`B : BlockShape n` and an arbitrary commutative ring `R : Type u`. The main
statement uses them only with `R = F.Carrier`.

1. `InverseTransposeUnipotentClause B R`: the image of the upper radical under
   the inverse transpose homomorphism is the opposite radical,
   `(B.unipotentSubgroup R).map (inverseTranspose n R).toMonoidHom =
   B.oppositeUnipotentSubgroup R`.
2. `InverseTransposeOppositeUnipotentClause B R`: the reverse equality,
   `(B.oppositeUnipotentSubgroup R).map (inverseTranspose n R).toMonoidHom =
   B.unipotentSubgroup R`.
3. `InverseTransposeLeviClause B R`: the image of the embedded common Levi is
   the same subgroup,
   `(B.leviSubgroup R).map (inverseTranspose n R).toMonoidHom =
   B.leviSubgroup R`.
4. `InverseTransposeBlockScalarClause B R`: for every tuple
   `a : Fin B.length → Rˣ`,
   `inverseTranspose n R (B.blockScalar R a) = (B.blockScalar R a)⁻¹`.
   The tuple `a` is not replaced by its inverse; the clause concerns the
   ambient matrix of the same tuple.

The last two clauses install precisely the supplied `T.topology` on
`F.Carrier`, for `F : PadicField.{uF} p` over any prime `p`. The ambient
`GeneralLinear n F.Carrier` then carries its induced matrix-unit topology, as
in `HasBlockIwahoriFactorization`. Write `e = T.generalLinearInverseTranspose n`
and `K' = K.comap e.toMonoidHom e.continuous`. Thus `K'` is the actual open
subgroup `{g | e g ∈ K}`, the preimage of `K`.

5. `InverseTransposeCompactComapClause T n`: for every open subgroup `K` of
   `GL_n(F)` with `IsCompact (K : Set (GL_n(F)))`, the set underlying `K'` is
   compact. This clause does not involve a block shape, so its rank `n` is an
   explicit argument.
6. `InverseTransposeIwahoriFactorizationClause T B`: for every open subgroup
   `K`, `B.HasBlockIwahoriFactorization T K` implies
   `B.HasBlockIwahoriFactorization T K'`.

In clause 6 both sides use the existing predicate with the same `T` and the
same `B`. Each side therefore asserts bijectivity of the ordered product
`(lower, Levi, upper) ↦ lower * Levi * upper` for its own subgroup. It also
asserts both weak-chamber containments for every weakly contracting tuple `a`:
forward conjugation by `B.blockScalar F.Carrier a` preserves the intersection
with the upper radical, and inverse conjugation preserves the intersection with
the opposite radical. The chamber is the same on both sides. The predicate is
not replaced by an opposite or reversed-order predicate, and no condition on
`a⁻¹` is imposed. Compactness is neither a hypothesis nor a conclusion of
clause 6; it is the separate clause 5.

## The statement

`InverseTransposeIwahoriStatement.{uF}` universally quantifies over every
prime `p` with its `Fact p.Prime` instance, every `F : PadicField.{uF} p`, every
supplied `T : F.TopologicalData`, every rank `n : ℕ` and every block shape
`B : BlockShape n`. It conjoins clauses 1–6 in the order above, with clauses
1–4 at `R = F.Carrier`. The field universe is unconstrained.

There is no positive-rank, properness or nonzero-block hypothesis. Rank zero,
the empty shape and one-block shapes are all included. No canonical-lift,
generalized-kernel, Jacquet-module, representation or admissibility hypothesis
or conclusion occurs.

## Why these are expected to hold

This informal outline is for reviewers and later provers; nothing here is
proved in Lean by this module.

- If `g` is upper block triangular with identity diagonal blocks, so is
  `g⁻¹`. Its transpose is lower block triangular with identity diagonal
  blocks. Since inverse transpose is an involution, this gives both radical
  equalities.
- Inverses and transposes of block diagonal matrices are block diagonal; again
  involutivity gives equality, not only containment.
- A block-scalar matrix is diagonal, so its inverse transpose is its inverse.
- `e` is a homeomorphism, so the preimage `K'` of a compact set is compact.
- For clause 6, `e` exchanges the upper and opposite radicals and preserves
  the common Levi, while `k ∈ K'` exactly when `e k ∈ K`. For `k ∈ K'`, let
  `e(k)⁻¹ = l m u` be the given factorization in `K`. Then
  `k = e(u⁻¹) e(m⁻¹) e(l⁻¹)` is a lower-Levi-upper factorization in `K'`, and
  uniqueness transfers the same way.
  For a weakly contracting `a` with `s = B.blockScalar F.Carrier a`, clause 4
  gives `e(s g s⁻¹) = s⁻¹ e(g) s`. Thus forward conjugation on `K' ∩ N`
  corresponds to the given inverse conjugation on `K ∩ Nop`, and inverse
  conjugation on `K' ∩ Nop` to forward conjugation on `K ∩ N`.

## Provenance

These are internal derived transport statements for the project's existing
block constructions, not verbatim claims of a source. The motivating source
is Bill Casselman, *Introduction to admissible representations of p-adic
groups*, Chapter III: *Induced representations and the Jacquet module*, revision
April 29, 2019, sections 4–6, especially III.5.4–III.5.5 on pages 6–7. It is
registered as `casselman-2019-jacquet-module`, SHA256
`377edac998669bc88da1224c4582a173854232f7fea5caf945d140ee92fde5c1`.
Section 4, page 5, defines an Iwahori factorization of a compact open subgroup
with respect to an opposing pair `P`, `P̄` by the ordered product
`N̄_K × M_K × N_K → K` and two conjugation containments. Sections 5–6 build
canonical lifts from such a subgroup, and the statement of III.6.2 adds "similarly with
the roles of `V` and `Ṽ` reversed". The source states no inverse-transpose
transport. The present clauses record the elementary matrix transport that
lets a proof obtain the project's opposite-radical version from the published
upper-radical one. The weak-chamber form of `HasBlockIwahoriFactorization` is
the project's published strengthened specialization; see
`BlockIwahoriDefinitions.md`. It is not attributed to Casselman.

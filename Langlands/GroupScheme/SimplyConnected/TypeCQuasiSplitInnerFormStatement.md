# Simply connected groups of type `C_n` are inner forms of `Sp_{2n}`: statement

Author: Worker 31, for Task 5986 (`8494af77-9d10-4c2f-b1cd-60dc371fb195`). The module
contains one `Prop`-valued definition and no proof.

## Statement

`Langlands.GroupScheme.TypeCQuasiSplitInnerFormStatement.{u}` quantifies over

- a field `K : Type u`;
- a group scheme `G` over `Spec K` with `IsAffineHom G.X.hom` and
  `LocallyOfFiniteType G.X.hom`;
- actual index data `d : TitsIndexData G` (module `Reductive/TitsIndex`), which contains a
  Galois pinning of `G` over the separable closure, a maximal split torus and a compatible
  ordering;
- a natural number `n` and a numbering `e : d.Vertex ≃ Fin n` of the simple vertices of the
  absolute root datum carried by `d`.

It assumes

- `2 ≤ n`;
- `IsSimplyConnected G`: every central isogeny from a semisimple group onto `G` is an
  isomorphism;
- `d.cartan a b = CartanMatrix.C n (e a) (e b)` for all simple vertices `a b`, that is, under
  the numbering `e` the actual Cartan pairings `d.pinning.rootDatum.pairing a b` of the simple
  roots of `G` form Mathlib's Cartan matrix of type `C_n`.

The statement then asserts that there is a quasi-split inner-form presentation
`q : QuasiSplitInnerForm G` (module `Rational/QuasiSplitInnerForm`) whose model group
`q.model` is isomorphic, as a group scheme over `Spec K`, to
`Symplectic.groupScheme K n`, the standard symplectic group scheme `Sp_{2n}`: the isometry
group of the standard alternating Gram matrix `Matrix.J (Fin n) K` of size `2n` (module
`Symplectic/Basic`).

`QuasiSplitInnerForm G` records a quasi-split model group, an adjoint quotient of the model,
a finite Galois extension `L/K`, an actual local isomorphism `model_L ≅ G_L`, and a cocycle of
the adjoint group whose inner action measures the discrepancy of the local isomorphism. The
statement asks for no further condition on these data.

The hypotheses are those of the published `TypeCDivisionFormStatement` except that the
absolute almost simplicity assumption is omitted; the intended proof does not use it, since
the Cartan matrix of type `C_n` already describes a connected Dynkin diagram.

## Intended proof (not part of the statement)

`G` is split by a finite Galois extension `L` of `K`. Over `L`, both `G_L` and `Sp_{2n,L}` are
split simply connected groups with root system of type `C_n`; the isomorphism theorem for
split reductive groups gives `Sp_{2n,L} ≅ G_L`. The Dynkin diagram of type `C_n`, `n ≥ 2`,
has no nontrivial automorphism, so every automorphism of `Sp_{2n}` is inner and the
discrepancy of this isomorphism on `L ⊗_K L` is a cocycle of the adjoint group `PSp_{2n}`.
This is the presentation. Formalizing it needs the existence of a finite splitting field, the
isomorphism theorem for split groups (the Library's published simply connected pinning and
root-datum results for `Sp_{2n}` in `SymplecticMatrix/SimplyConnected` and
`SymplecticMatrix/TypeC`), and the identification of the automorphism group of `Sp_{2n}`
with its adjoint group.

## Role

This is one of four prerequisites in the planned proof of
`TypeCDivisionFormStatement` (Task 5986). The others are
`SymplecticInnerFormAntihermitianStatement`, `AntihermitianSymplecticSplitRankStatement`
and `TypeCDistinguishedVerticesStatement`; a reduction of the target to these four compiles.

## Source and provenance

Provenance: derived.

1. M.-A. Knus, A. Merkurjev, M. Rost and J.-P. Tignol, *The Book of Involutions*, AMS
   Colloquium Publications 44, 1998, source `knus-merkurjev-rost-tignol-1998-book-of-involutions`,
   SHA-256 `e21641aeb1425b63bec70032352f0cb33275f7bd1ddf682c3bea62b798654fe0`, §26,
   Theorem (26.14), printed p.369 (PDF p.392), with its proof on printed pp.369–370 (PDF
   pp.392–393). Over an arbitrary field `F`, `(A, σ) ↦ Sp(A, σ)` is an equivalence from central
   simple algebras of degree `2n` with symplectic involution onto simply connected simple
   groups of type `C_n`. The proof shows that all such groups are twisted forms of one split
   group and that all automorphisms are inner (Theorem (25.16)), which is the content stated
   here.
2. J. Tits, *Classification of algebraic semisimple groups*, in *Algebraic Groups and
   Discontinuous Subgroups*, Proc. Sympos. Pure Math. 9, 1966, source
   `tits-1966-classification-algebraic-semisimple`, SHA-256
   `962203f9e47e9c3c43fc1049a38e28c751aa42beb7ee5250a095a132e215a5d4`, Table II, type `C_n`,
   printed p.56 (PDF p.61). The index of type `C_n` carries no Galois action on the diagram
   (the symbol has no superscript `g`), so every group of type `C_n` is an inner form; for
   `d = 1` the group is `Sp_{2n}(k)`.

The Lean statement is derived from these sources as follows. "Group of type `C_n`" is
expressed through actual `TitsIndexData` whose actual Cartan matrix is `CartanMatrix.C n`.
"Inner form of `Sp_{2n}`" is the published `QuasiSplitInnerForm` presentation with model
isomorphic to the published `Symplectic.groupScheme K n`. Knus–Merkurjev–Rost–Tignol use
cocycles of the absolute Galois group; the presentation here twists over a finite Galois
splitting field, which is the same procedure restricted to that field.

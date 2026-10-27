# Character determination on the actual intersection Levi

Author: Worker 632.

`Langlands.Geometric.intersectionLeviDiagonalCharacterTheorem` proves exactly
`Langlands.Geometric.IntersectionLeviDiagonalCharacterStatement.{uF}` from the
published statement module. It applies to every characteristic-zero field
`F : Type uF`, every natural rank `n` including zero, arbitrary ordered block
shapes `B C : GeneralLinear.BlockShape n`, and every
`w : MinimalRepresentatives B C`.

Write `p = GeneralLinear.permutation n F w.val` and

```text
I = General.intersectionIn (B.leviSubgroup F) (C.leviSubgroup F) p.
```

This is a subgroup of the actual matrix subgroup `B.leviSubgroup F`: its
elements satisfy `p * m.val.val * p⁻¹ ∈ C.leviSubgroup F`. For an arbitrary
monoid homomorphism `χ : I →* ℂˣ`, the theorem assumes that
`χ m = 1` whenever the literal underlying matrix of `m` equals
`Matrix.diagonal (fun x => (t x : F))` for a family `t : Fin n → Fˣ`.
It concludes `χ m = 1` for every `m : I`. No topology or regularity of the
character enters the proof.

## Characters of one general linear group

The character-specific helper declarations lie in
`Langlands.Geometric.DiagonalCharacter`.
`diagonalUnit t` is the element of `GeneralLinear k F` whose matrix is
`Matrix.diagonal (fun i => (t i : F))`, with inverse given by the diagonal
of the inverse units. The two inverse laws follow from diagonal matrix
multiplication. `diagonalUnit_one` proves that the all-one family gives
the identity, including in rank zero.

The shared `Langlands.GeneralLinear.transvectionUnit` is imported from
[Group.GL.Transvection](../../Group/GL/Transvection.md).
For distinct indices `i j : Fin k`, `transvectionUnit i j hij c` has matrix
`1 + Matrix.single i j c` and inverse with coefficient `-c`. The inverse
laws use Mathlib's multiplication formula for transvections with the same
ordered pair of indices.

`scale_transvection` assumes characteristic zero. Let `t` be this
transvection and let `d` be diagonal with entry `2` at `i` and entry `1`
elsewhere. The field element `2` is nonzero, so it defines a unit. The
lemma proves the actual invertible-matrix equality

```text
d * t = (t * t) * d.
```

The proof expands the matrix entries: left multiplication scales row `i`,
right multiplication scales column `i`, and `i ≠ j` ensures that the
transvection entry on the right acquires its coefficient from `t * t`.
The same-index transvection product has coefficient `c + c`.

`character_transvection` applies any homomorphism
`χ : GeneralLinear k F →* ℂˣ` to this equality. Commutativity of complex
units and cancellation of `χ d` give `χ t = χ t * χ t`; a second
cancellation gives `χ t = 1`. This argument needs no assumption that `χ`
is trivial on diagonal matrices.

`character_GL` adds triviality on every `diagonalUnit t` and concludes
triviality on all of `GeneralLinear k F`. It uses Mathlib's
`Matrix.diagonal_transvection_induction_of_det_ne_zero` on the underlying
matrix of an arbitrary invertible matrix. Its induction predicate says
that every unit with the given underlying matrix has character value one.
For a nonsingular diagonal matrix, the determinant product formula makes
every diagonal entry nonzero; these entries define the units required by
the hypothesis. The transvection case is `character_transvection`.
The product case lifts the nonsingular factors to general linear group
elements, uses their induction hypotheses, and applies multiplicativity.
There is no positive-rank assumption.

## Finite products

`character_pi` concerns a finite dependent product of arbitrary groups
`G i`. It proves that a character on `∀ i, G i` is trivial if it is trivial
on every element `Pi.mulSingle i g`. The proof inducts on a finite set
containing the support of a tuple. At the insertion step it factors the
tuple as its single coordinate at `i` times the tuple obtained by setting
that coordinate to one. The latter tuple is supported on the smaller
set. This proof uses no commutativity of the source groups.

`character_pi_GL` applies this lemma to a finite family
`GeneralLinear (d i) F` and applies `character_GL` to each single-coordinate
restriction. A diagonal in one factor and identity elements elsewhere is
the simultaneous family of diagonal units obtained by extending its unit
entries with ones. Consequently triviality on all simultaneous diagonal
families suffices for the entire product.

## Literal ambient matrices and the actual intersection

`leviEmbedding_diagonalUnit` proves, for any block shape `B` and diagonal
unit families `t i` in its blocks,

```text
(B.leviEmbedding F (fun i => diagonalUnit (t i))).val
  = Matrix.diagonal
      (fun x => (t (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2 : F)).
```

The proof writes both ambient indices in block coordinates using
`B.indexEquiv`. Entries in the same block are the prescribed diagonal
entries by `leviEmbedding_apply_same`; entries in distinct blocks are
zero by `leviEmbedding_apply_ne`. Injectivity and the inverse law of
`B.indexEquiv` give the stated literal diagonal matrix.

`sourceActualEquiv B C w` is a multiplicative equivalence from
`sourceLevi F B C w` to the actual `General.intersectionIn` group. This
helper works for any permutation `w`. Its forward map is the published
`B.leviEquiv F` restricted to the source subgroup. The source condition
is exactly that the conjugate of this embedded matrix belongs to the
second Levi, so it supplies actual intersection membership. The inverse
uses `(B.leviEquiv F).symm`, with membership checked by the equivalence's
inverse law. The two inverse laws and preservation of multiplication
are proved by subtype extensionality.

In the final theorem, `exists_standardIntersections F B C w.val
w.property.1` supplies an actual refinement `S : BlockRefinement B` and
the proved subgroup equality
`hS : sourceLevi F B C w.val = refinedLevi F B S`.
Compose `refinedLeviEquiv F B S`, the subgroup identification from
`hS.symm`, and `sourceActualEquiv B C w.val`. The result is a
multiplicative equivalence

```text
e : (∀ i, (S i).Levi F) ≃* I.
```

For a nested tuple `g`, its actual ambient matrix under `e` is
`B.leviEmbedding F (fun i => (S i).leviEmbedding F (g i))`.
In particular, if `g i j = diagonalUnit (t i j)`, two applications of
`leviEmbedding_diagonalUnit` compute this matrix as a literal ambient
diagonal. More explicitly, set

```text
r i a = t i ((S i).indexEquiv.symm a).1 ((S i).indexEquiv.symm a).2,
a x   = r (B.indexEquiv.symm x).1 (B.indexEquiv.symm x).2.
```

The matrix is `Matrix.diagonal (fun x => (a x : F))`. The original
hypothesis on actual matrices therefore shows that `ψ = χ ∘ e` is
trivial on every nested simultaneous diagonal family.

Apply `character_pi` to the outer blocks and `character_pi_GL` to the
inner blocks, extending each chosen outer diagonal family by ones in
the other outer blocks. This proves `ψ g = 1` for every nested tuple.
For an arbitrary `m : I`, use `g = e.symm m` and the inverse law
`e (e.symm m) = m` to obtain the desired `χ m = 1`.
Thus the use of product coordinates is connected to the actual group
and to its literal ambient-matrix diagonal test by proved maps and
entry identities.

## Provenance and scope

This is an internal derived algebraic reduction. It is not a theorem
quoted verbatim from Bernstein--Zelevinsky. Its inputs are the published
statement, the Library's actual block and permutation constructions,
the proved `exists_standardIntersections` from
`StandardIntersectionsProof`, the constructed `refinedLeviEquiv` from
`RefinementDefinitions`, and Mathlib's diagonal/transvection induction
from `Mathlib.LinearAlgebra.Matrix.Transvection`.
The additional unit constructions, character arguments, finite-product
reduction and actual-intersection adapter are proved in this module.

All imported Lean/Markdown pairs and the target statement are preserved.
The field universe is arbitrary and independent of the fixed complex
codomain; no step requires a nonzero rank. There are no extra
decomposition, generation, determinant-dependence, continuity or
character-comparison hypotheses. The result supplies character
determination only; no Haar-measure computation or correction
cancellation is proved here.

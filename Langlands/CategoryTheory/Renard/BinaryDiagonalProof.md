# Renard A.III.1: binary diagonal universal-arrow comparisons

Author: Worker 1570.

This unit proves the published closed proposition
`Langlands.Renard.BinaryDiagonal.BinaryDiagonalStatements.{vC,uC}`
from [BinaryDiagonalStatements](BinaryDiagonalStatements.md). The entry
theorem is `Langlands.Renard.BinaryDiagonal.binaryDiagonalStatements` in
`Langlands.CategoryTheory.Renard.BinaryDiagonalProof`. Its four component
theorems have exactly the published component propositions as their types.

## Source and scope

The source is David Renard, *Représentations des groupes réductifs
p-adiques*, French version dated 9 July 2026, registered as
`renard-2026-representations-groupes-reductifs-padiques`, SHA256
`7b539996793b7c3620e72e1e389588eb42d1a8e91d6f68b2eead5c2e2ffc182c`.
A.III.1 gives the right and left universal problems on printed p.251 /
one-based PDF257 and identifies coproducts and products with the diagonal's
right and left solutions in example 1 on printed p.252 / PDF258.
A.IV.1, example 3, and A.IV.2 on printed p.257 / PDF263 identify the binary
discrete-diagram limit and its colimit dual. These pages and PDF262 were
read directly for this proof.

The supplementary registered source
`renard-2010-corrections-complements`, SHA256
`fdf3c88716c294c451c1f6fad67f6b99c95dae670aae0b8ad191ab0a96e69863`,
was read on PDF18–19. This bounded check gives no correction to the binary
diagonal example. The [Appendix A discrepancy note](../../../notes/renard/appendix-a-corrections.md)
explains the arrow-direction and constant-functor problems in the general
limit and colimit prose. The proof uses actual cones and cocones and the
source's concrete factorization equations, with outward arrows for
colimits; it does not use fullness of a constant-functor map.

Every component quantifies an arbitrary `C : Type uC` with
`Category.{vC} C`. The object and morphism universes are independent. The
products and coproducts are supplied candidates: the theorem imposes no
general existence, completeness, additivity or zero-object hypothesis.
`Nonempty` expresses existence of the data carried by `IsUniversal`,
`IsLimit` and `IsColimit`.

## Implemented factorization comparisons

`productFactorizationStatement` specializes the published
`UniversalArrow.leftCharacterization_proof` to the actual
`Functor.diag C`, the target `(X,Y)`, and the supplied arrow
`CategoryTheory.Prod.mkHom p q`. This turns terminality in the
costructured-arrow category into unique factorization of every paired
arrow through the chosen pair `(p,q)`.

For an arbitrary test object `Z` and maps `f : Z ⟶ X`, `g : Z ⟶ Y`,
the generic characterization yields a unique `l : Z ⟶ P` with
`(l,l) ≫ (p,q) = (f,g)`. Product-category composition is componentwise.
Applying `congrArg` to the first and second projections produces both
`l ≫ p = f` and `l ≫ q = g`. Conversely,
`CategoryTheory.Prod.hom_ext` reassembles these equations into the paired
one. The same projection and reassembly steps translate the uniqueness
condition, so uniqueness always concerns maps satisfying both equations.
For the reverse implication, an arbitrary product-category arrow `fg` is
handled by applying the simultaneous factorization hypothesis to `fg.1`
and `fg.2`. The generic characterization then constructs terminality.

`coproductFactorizationStatement` performs the corresponding specialization
of `UniversalArrow.rightCharacterization_proof` for the supplied
`CategoryTheory.Prod.mkHom i j`. The pair equation is
`(i,j) ≫ (l,l) = (f,g)`, and its two projections are
`i ≫ l = f` and `j ≫ l = g`. The proof transfers existence and uniqueness
in both directions by the same explicit component operations. Here the
generic characterization constructs or extracts initiality in the
structured-arrow category.

## Implemented limit and colimit comparisons

`productLimitStatement` first rewrites left universality using the proved
simultaneous-factorization comparison. From unique factors it constructs
`IsLimit (BinaryFan.mk p q)` with `BinaryFan.IsLimit.mk`. Classical choice
selects the unique factor for each pair of test maps. The two components
of its specification provide the two factorization laws, and the
uniqueness clause supplies the constructor's uniqueness field.

Conversely, `BinaryFan.IsLimit.lift'` applied to a limiting fan supplies a
map and both equations for any test pair. If another map satisfies those
equations, its composites with `p` and `q` agree with those of the chosen
lift. `BinaryFan.IsLimit.hom_ext` identifies the two maps. The constructed
and extracted witnesses retain exactly the supplied vertex `P` and
projections `p,q`.

`coproductColimitStatement` uses the proved right factorization comparison,
then constructs `IsColimit (BinaryCofan.mk i j)` with
`BinaryCofan.IsColimit.mk`. The selected factor's two equations and unique
specification supply its fields. In the reverse direction,
`BinaryCofan.IsColimit.desc'` provides the factor and its two equations,
and `BinaryCofan.IsColimit.hom_ext` proves uniqueness. The vertex `Q` and
inclusions `i,j` remain the supplied data throughout.

Finally, `binaryDiagonalStatements` assembles the four component theorems
in the published aggregate's order. It has no outer mathematical
hypotheses. The explicit equivalences with Mathlib's witness types,
`Nonempty` wrappers, independent universes and aggregate are derived
formal packaging of the cited source assertions. The Lean proof reuses
the published generic universal-arrow dictionary and Mathlib's binary
fan/cofan API; it does not claim that the book states this packaging or
follows these implementation steps. Other A.III examples and the parent
whole-book obligations remain separate.

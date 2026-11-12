# Finitely generated free subcomodules of a coalgebra over a principal ideal domain

Author: Worker 4686.

This internal helper module proves that a flat coalgebra `B` over a principal
ideal domain `R` is a union of finitely generated free subcomodules, provided
the `R`-valued functionals on `B` separate its elements. It records the result
as the existence of matrix coefficients. All declarations are in the namespace
`Langlands.GroupScheme.IntegralLinearEmbedding`. They use Mathlib's `Coalgebra`
with `comul` and `counit`.

## Right translations (any commutative ring)

* `rightAct f`, for a functional `f : Module.Dual R B`, is the linear map
  `b ↦ ∑ f (b₂) • b₁` when `comul b = ∑ b₁ ⊗ b₂`. In Lean it is
  `TensorProduct.rid R B ∘ₗ f.lTensor B ∘ₗ comul`; `rightAct_apply` unfolds it.
* `rightAct_counit`: `rightAct counit b = b` (the counit axiom).
* `rightAct_rightAct`: `rightAct g (rightAct f a) = rightAct (g ∘ₗ rightAct f) a`.
  The proof uses coassociativity, `coassoc_symm_apply`.
* `exists_fg_rightAct`: all right translates of a fixed `a` lie in one
  finitely generated submodule, the span of the left tensor factors of one
  expression of `comul a`.
* `translateSpan S` is the span of all right translates of the elements of a
  finite set `S`. `subset_translateSpan` shows `S ⊆ translateSpan S` (translate
  by the counit). `rightAct_mem_translateSpan` shows that `translateSpan S` is
  stable under every `rightAct g`, by `rightAct_rightAct`.

## Saturation (integral domains)

* `saturation W` is the set of `b` with `r • b ∈ W` for some `r ≠ 0`; it is a
  submodule (`mem_saturation`, `le_saturation`).
* `isTorsionFree_quotient_saturation`: `B ⧸ saturation W` is torsion-free.

## Principal ideal domains

* `exists_finset_separating`: if the functionals separate the elements of `B`
  and `W` is finitely generated, finitely many functionals separate the
  elements of `W`. The restrictions of all functionals to `W` span a submodule
  of the finitely generated module `Module.Dual R W`, which is noetherian, so
  finitely many of them span it.
* `saturation_fg`: under the same hypotheses, and with `B` torsion-free, the
  saturation of `W` is finitely generated. Evaluation at finitely many
  separating functionals embeds `saturation W` into `T → R`, a noetherian
  module.
* `repr_rid_lTensor`: coordinates of a contraction `rid (f.lTensor Q x)` in a
  basis of `Q` are the values of `f` on the coordinates of `x` given by
  `TensorProduct.equivFinsuppOfBasisLeft`.
* `tensor_eq_zero_of_contract`: if `Q` is torsion-free and `u : Q ⊗ B` has
  every contraction `rid (f.lTensor Q u)` equal to `0`, then `u = 0`. The
  proof moves `u` into `Q₀ ⊗ B` for a finitely generated `Q₀ ⊆ Q`, which is
  free over the principal ideal domain (`Module.basisOfFiniteTypeTorsionFree'`),
  and applies the separation hypothesis to each coordinate.

## Subcomodules

* `rightAct_mem_saturation`: the saturation of a submodule stable under all
  right translations is again stable under them.
* `comul_mem_range_rTensor`: if `W` is stable under all right translations
  and `b ∈ saturation W`, then `comul b` lies in the image of
  `saturation W ⊗ B → B ⊗ B`. Proof: by right exactness of the tensor product
  (`rTensor_exact`) it suffices that the image of `comul b` in
  `(B ⧸ saturation W) ⊗ B` vanishes. That quotient is torsion-free, and the
  contraction with any `f` is the class of `rightAct f b`, which is zero; so
  `tensor_eq_zero_of_contract` applies.

## Matrix coefficients of a free subcomodule

Here `Λ` is a submodule with a basis `e : Basis (Fin N) R Λ`, and
`hΛ` says that `comul b` lies in the image of `Λ ⊗ B` for every `b ∈ Λ`.

* `coefficientMatrix e hΛ` is the matrix with
  `comul (e j) = ∑ i, e i ⊗ coefficientMatrix e hΛ i j` (`comul_basis`).
* `sum_basis_tmul_inj`: for a flat module `X`, coefficients against the
  basis `e` in `B ⊗ X` are unique (flatness makes `Λ ⊗ X → B ⊗ X` injective).
* `counit_coefficientMatrix` (for flat `B`): `counit` of the entries is the
  identity matrix, from the counit axiom `lTensor_counit_comul`.
* `comul_coefficientMatrix` (for flat `B`):
  `comul (coefficientMatrix i j) = ∑ l, coefficientMatrix i l ⊗ coefficientMatrix l j`,
  from coassociativity `coassoc_apply`.
* `basis_mem_span_coefficientMatrix`: each `e j` is an `R`-combination of the
  entries, from the other counit axiom `rTensor_counit_comul`.

## Main result

* `translateSpan_fg`: `translateSpan S` is finitely generated (a finite
  supremum of the submodules of `exists_fg_rightAct`).
* `exists_matrix_coefficients`: let `B` be a flat coalgebra over a principal
  ideal domain `R` whose functionals separate its elements, and let `S` be a
  finite subset of `B`. There are `N : ℕ` and `M : Matrix (Fin N) (Fin N) B`
  with `comul (M i j) = ∑ l, M i l ⊗ M l j`,
  `counit (M i j) = (1 : Matrix (Fin N) (Fin N) R) i j`, and
  `S ⊆ Submodule.span R (Set.range fun p => M p.1 p.2)`.
  Proof: take `Λ = saturation (translateSpan S)`. It is finitely generated
  (`saturation_fg`), torsion-free, hence free with a basis indexed by
  `Fin N`. It is a subcomodule by `comul_mem_range_rTensor`, and it contains
  `S`. Its coefficient matrix has the required properties.

## Provenance

The module is derived internally. It formalizes, over a principal ideal domain
and with a separation hypothesis in place of the usual finiteness argument, the
classical fact used in F. Bruhat and J. Tits, *Groupes réductifs sur un corps
local II*, Publ. Math. IHÉS 60 (1984), 1.4.5 (printed p.25 / PDF p.22),
registered as `bruhat-tits-1984-reductive-local-groups-ii`: a flat affine group
scheme of finite type over a Dedekind ring has a finitely generated projective
subcomodule of its coordinate ring that generates it, by a proposition of
Serre that they cite. The Lean proof is not taken from the source: the
saturation of the span of translates and the contraction criterion for
tensors are the route used here. The separation hypothesis is supplied for
local integral models in `LocalIntegralSeparation.lean`.

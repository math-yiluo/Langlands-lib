# Mixed degree-two cups and their shuffle detection

This is an internal extension of the ordered Čech shuffle calculation and its transport to actual right-derived structure-sheaf cohomology. It defines the actual mixed cup and its induced tensor map, and proves that the tensor map is injective under the hypotheses below. It does not assert the full degree-two Künneth decomposition or the host exterior/coproduct comparison.

## Raw shuffle identities

Work over a commutative ring `R` with a pullback square `P = X ×[Spec R] Y`, finite first-factor index type, and open families `U`, `V`. The supplied section algebra structures on `X` and `Y` agree with their structure maps (`halgX`, `halgY`). Two-entry intersections of `U` and all nonempty finite intersections of `V` are affine. Let `l` be any `R`-linear functional on all first-factor one-cochains. No covering assumption or boundary-vanishing condition on `l` is needed for these identities.

`L_prod_sum` applies shuffle slant to a product of `n+2` degree-one axis sums. All the input one-cochains `z_k` and `y_k` are cocycles. Its output on a second-factor tuple `b` is

\[
  \sum_{s=0}^{n+1}(-1)^s l(z_s)\,\big(\operatorname{prod}_{n+1}(y\circ s.\mathrm{succAbove})\big)(b),
\]

where the remaining factors retain their original order and the products are the ordered Čech products. The Lean expression uses `succAbove` for the omitted position. The proof evaluates each signed shuffle summand using the existing `res_prod_path` and `slant_mul` identities; it imposes no normalization of the values `l(z_s)`.

`L_cup_pull_add` specializes this to two factors:

\[
 L\big((p_1^*z_0+p_2^*y_0)\mathbin\cup
       (p_1^*z_1+p_2^*y_1)\big)
   =l(z_0)y_1-l(z_1)y_0.
\]

Setting selected inputs to zero gives `L_cup_pull_left_right`, which evaluates a mixed cup as `l(z)y`, and `L_cup_pull_left_left` and `L_cup_pull_right_right`, which kill cups supported entirely on one axis. The latter two lemmas concern cups of one-cocycles; they do not prove vanishing on arbitrary pulled-back degree-two classes.

## Actual cohomology and the mixed tensor map

Now `K` is any field, with no characteristic restriction, and `X`, `Y`, `P` are objects over `Spec K`. The canonical pullback `unitCohomologyPullback f n` composes `relativeCohomologyPullback` with the unit-module pullback isomorphism. Thus its source and target are the actual structure-sheaf cohomology objects.

For the mixed cup and tensor map, `P` is separated and its product family is a finite affine open cover. `mixedCup` is the bilinear map

\[
 H^1(X,\mathcal O_X)\times H^1(Y,\mathcal O_Y)
 \longrightarrow H^2(P,\mathcal O_P),\qquad
 (x,y)\longmapsto p_1^*x\cup p_2^*y,
\]

using `cupCanonical` for that product cover. `mixedTensor` is its linear extension by `TensorProduct.lift`; `mixedCup_apply` and `mixedTensor_tmul` are the defining evaluation formulas.

The detection lemmas retain these additional data explicitly: the square of `p₁`, `p₂` is an actual pullback; all three structure morphisms are separated; the section algebra actions on all three schemes agree with their structure maps; `U`, `V` are finite affine open covers; their intersections satisfy the raw shuffle affineness assumptions; and the product family is an affine open cover. These assumptions are inputs to the comparison and shuffle maps, not conclusions proved here.

For every linear functional `ell : H¹(X,O_X) → K`, `slantByH1Dual_mixedCup` proves

\[
 \operatorname{slant}_{\ell}(p_1^*x\cup p_2^*y)=\ell(x)y
\]

in actual `H¹(Y,O_Y)`. This uses the existing chosen extension of cohomology classes to all cochains from `AllSeqSlantDual`. The proof chooses cocycle representatives by `canonicalClass_surjective`, rewrites the actual pullbacks and cup using their cocycle formulas, applies `L_cup_pull_left_right`, and evaluates the extended functional on the first cocycle. No arbitrary Künneth equivalence enters the argument.

`slantByH1Dual_mixedTensor` extends that equality to every tensor `t` by tensor-product induction and additivity. Its right side is precisely contraction of the first factor:

\[
 \operatorname{slant}_{\ell}(\operatorname{mixedTensor}(t))
  =\operatorname{lid}\big((\ell\otimes\mathrm{id})(t)\big).
\]

Finally, `mixedTensor_injective` chooses an arbitrary vector-space basis of actual `H¹(X,O_X)` and applies each basis coordinate as `ell`. Equality of mixed images gives equality of all contractions by the preceding formula. `TensorProduct.equivFinsuppOfBasisLeft` then detects equality of tensors coefficient by coefficient. No finite-dimensionality or dimension formula is assumed.

## Provenance and scope

The new content is derived internally from the existing shuffle-path identities, ordered Čech-to-derived-cohomology comparison, pullback and cup cocycle formulas, and elementary tensor-product linear algebra. No additional literature theorem is claimed. The definitions retain their cover data, and slant retains its chosen cochain extension. Cover independence, annihilation of arbitrary degree-two axis pullbacks, surjectivity of the degree-two decomposition, creation-contraction identities, alternation, exterior generation and the full host comparison remain separate obligations.

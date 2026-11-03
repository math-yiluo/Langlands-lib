# Actual Lie kernels in a whole-torus centralizer

Author: Worker 74.

This internal supporting construction identifies the Lie kernel inside the actual
whole-group centralizer functor with the zero adjoint weight space. It is derived
from the published dual-number Lie model, all-test-algebra adjoint weight condition,
and whole-torus centralizer definitions, using the relative spectrum adjunction.
It makes no independent literature attribution. The acting group may be any affine
commutative group scheme; no torus, splitness, field, characteristic, finite type,
smoothness, connectedness, reductivity or monicity hypothesis is needed.

For `R : CommRingCat.{u}`, let `G` be a group scheme over `Spec R` with affine
structural morphism, let `T` be a commutative group scheme with affine structural
morphism, and let `i : T.toGrp ⟶ G`. The definition `torusCentralizerLie i` is a
submodule of `Additive (lieKernel G R)`. Its carrier consists exactly of those
vectors whose underlying point over `Spec (DualNumber R)` belongs to
`(torusCentralizer i).carrier`. That membership says that after every map from
an arbitrary test scheme to `Spec (DualNumber R)`, the point commutes with the
image of every `T`-point of that test scheme. `mem_torusCentralizerLie` states this
carrier description, and `torusCentralizerLie_eq_weightSpace_zero` identifies
the submodule with `weightSpace i 0`. The submodule operations are transported
from the latter using the proved equality of carriers; the definition retains the
actual centralizer membership predicate as its carrier.

The implementation first constructs `dualNumberEvaluation c hc`, an `R`-algebra
map from `DualNumber A` to an `R`-algebra `A`, for `hc : c * c = 0`. It fixes
constant coefficients and sends epsilon to `c`. The factorization lemma shows
that any `f : DualNumber R →ₐ[R] A` equals coefficient extension followed by
evaluation at `f epsilon`. Evaluation also sends a constant group point to the
original point.

`affinizationFactor G x` factors an arbitrary test-scheme map `x : V ⟶ G.X`
through the relative affinization unit of `V`. The construction uses the
coordinate algebra and coordinate isomorphism of the affine group scheme;
`unit_affinizationFactor` is the adjunction identity followed by cancellation of
that isomorphism. The test scheme `V` itself need not be affine.

The forward direction, `mem_weightSpace_zero_of_mem_torusCentralizer`, tests
centralizer membership on `Spec (DualNumber A)` for every coefficient algebra `A`
and every constant `T(A)`-point. The zero character has value one, so commutation
implies the trivial conjugation identity required by `weightSpace i 0`. This
direction does not require affineness of the acting commutative group scheme.

For the reverse direction, `commute_of_mem_weightSpace_zero` first rewrites the
zero-weight identity as commutation with a constant `T(A)`-point over dual
numbers. It then maps that equality under evaluation at `f epsilon` and applies
the factorization lemma, obtaining commutation after every algebra map
`f : DualNumber R →ₐ[R] A`. The proof
`mem_torusCentralizer_of_mem_weightSpace_zero` handles a general test scheme by
factoring both its map to the base dual-number spectrum and its `T`-point through
relative affinization, then pulling the affine commutation equality back along
the unit. Together these give
`mem_torusCentralizer_iff_mem_weightSpace_zero`, from which the submodule and its
zero-weight identification follow.

Finally, `mem_dynamicCentralizer_iff_mem_weightSpace_zero` specializes the
membership equivalence to a cocharacter `χ : (Gm (Spec R)).toGrp ⟶ G`. It uses
the Laurent-spectrum isomorphism to obtain affineness of `Gm` and the published
equality between its whole-group centralizer and `Dynamic.centralizer χ`.
The resulting weight is `Gm.powerHom (Spec R) 0`. This is only the centralizer
membership comparison: it does not prove the parabolic or unipotent dynamic Lie
clauses, representability or smoothness of any centralizer, equality of generic
and whole-torus group centralizers, or either exact target of the host task.

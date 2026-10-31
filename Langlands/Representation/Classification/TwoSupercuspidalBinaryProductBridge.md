# Binary products in the two-supercuspidal argument

Module `Langlands.Representation.Classification.TwoSupercuspidalBinaryProductBridge`,
namespace `Langlands.Classification.BinaryProductBridge`.

Author: Worker 745 (task `3c9849a4-a6c0-43ac-9982-d15ed76bf1e9`, Zelevinsky 1980
Proposition 1.11(a)).

## Purpose

The Library has two descriptions of a product `A × B` of representations of
`GL_a(F)` and `GL_c(F)`:

* `T.normalizedProductInductionFunctor (Shahidi.twoBlocks a c ha hc)` applied to
  `twoBlockFactors ha hc A B`, defined only for positive ranks; the target
  statement `TwoSupercuspidalNonadjacentProductIrreducible` uses this form;
* the all-rank binary product `T.binaryNormalizedProductFunctor a c`
  (`Langlands.Representation.Induction.BinaryProduct`), which also accepts
  rank-zero factors. Derivative statements in the Bernstein–Zelevinsky Leibniz
  form produce graded pieces of this second kind, with `GL_0` factors at the
  boundary.

This module compares the two descriptions and records what the binary product
does when a factor is zero or is a one-dimensional representation of `GL_0`. It
contains no source theorem and no derivative result.

## Declarations

All representations are smooth complex representations
`SmoothRep.{0, uF, uV} ℂ (GeneralLinear n F.Carrier)` with the topology
`T.topology`; the binary product lands in carrier universe `max uF uV`.

* `binary_eq_twoBlocks ha hc : BlockShape.binary a c ha hc = Shahidi.twoBlocks a c ha hc`.
  Both shapes have block sizes `(a, c)`.
* `normalizedProductInductionFunctor_obj_congr`: equal block shapes and
  heterogeneously equal factor families give equal normalized products.
* `binaryNormalizedProductFunctor_obj_eq_twoBlocks ha hc A B`: for positive
  ranks, `(T.binaryNormalizedProductFunctor a c).obj (A, B)` is equal to
  `(T.normalizedProductInductionFunctor (Shahidi.twoBlocks a c ha hc)).obj
  (twoBlockFactors ha hc A B)`. The proof unfolds the published
  `binaryNormalizedProductFunctor_of_pos` and compares factor families entry by
  entry.
* `subsingleton_of_isZero` and `isZero_of_subsingleton`: a smooth representation
  is a zero object exactly when its carrier is a subsingleton.
* `subsingleton_rankCast h hA`: `generalLinearRankCast T h` keeps a subsingleton
  carrier subsingleton.
* `subsingleton_rankCast_product h A B hAB`: if `A` or `B` has a subsingleton
  carrier, so does the rank cast along `h : a + b = m` of the binary product of
  `(A, B)`. This uses the published `isZero_binaryNormalizedProductFunctor_obj`.
* `nonempty_iso_unit Z hZ`: a representation `Z` of `GL_0(F)` with
  `finrank ℂ Z = 1` is isomorphic to the published unit `T.binaryProductUnit`.
  `GL_0(F)` acts trivially (`representation_apply_of_rank_eq_zero`), so any
  linear isomorphism of one-dimensional spaces intertwines.
* `rankCastEquiv h B` (definition): for `h : b = c`, the representation of the
  rank cast `(generalLinearRankCast T h).obj B` is equivalent, by the identity
  linear map after `subst`, to `B.representation` composed with the
  entry-preserving reindex `GL_c(F) → GL_b(F)` along `finCongr h.symm`.
* `nonempty_equiv_rankCast_product_right hb h h' A Z hZ`: if `b = 0` and
  `finrank ℂ Z = 1`, the rank cast along `h' : a = m` of `A` is equivalent, as a
  representation of `GL_m(F)`, to the rank cast along `h : a + b = m` of the
  binary product of `(A, Z)`. The proof replaces `Z` by the unit (previous item),
  then uses the published right unit equivalence `binaryProductRightUnitEquiv`,
  the carrier lift `liftEquiv` and `rankCastEquiv`.
* `nonempty_equiv_rankCast_product_left ha h h' Z B hZ`: the same for a
  one-dimensional left factor `Z` of `GL_0(F)` and `b = m`, using
  `binaryProductLeftUnitEquiv`.
* `finrank_rankCast_product_of_zero_zero ha hb h Z Z' hZ hZ'`: if both ranks are
  zero and both factors are one-dimensional, the rank cast of their binary
  product is one-dimensional. The proof uses the published
  `binaryZeroZeroTensorEquiv` (the product is `Z ⊗ Z'`) and
  `Module.finrank_tensorProduct`.

## Provenance

Internal. These are bookkeeping comparisons between published Library
constructions (`Induction.BinaryProduct`, `Shahidi.twoBlocks`,
`Derivative.generalLinearRankCast`); they restate no result from the
literature. In the proof of Zelevinsky 1980 Proposition 1.11(a) via
Bernstein–Zelevinsky 1977 Theorem 4.2 they translate the Leibniz-rule graded
pieces of the derivatives of `ρ × ρ'` (BZ77 Lemma 4.5, printed p.455) into the
forms needed there: interior pieces vanish, boundary pieces are rank casts of
`ρ` or `ρ'`, and the top piece is one-dimensional. All proofs are written for
this module; no Library proof is copied or adapted.

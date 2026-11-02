# Finite-algebra determinant-open candidate

This internal construction applies over any field `k : Type u` to any
commutative `k`-algebra `A : Type u` with a supplied finite basis
`b : Basis (Fin n) k A`. A basis supplies all finiteness and freeness used
in the construction. No nontriviality assumption on `A` is imposed.

`base k` is `Spec k`, and `algebraSchemeMap k A` is the ordinary spectrum
map associated with the algebra map. `presheaf k A` specializes the actual
relative global-unit presheaf to this morphism. Thus its tests range over
all schemes over `Spec k`.

Put `R = coordinateRing k n = MvPolynomial (Fin n) k`.
`genericElement b` is exactly `g = ∑ i, X i ⊗ b i` in `R ⊗[k] A`.
`determinant b` is `Algebra.norm R g`, which is defined in Mathlib as
the determinant of the `R`-linear endomorphism of `R ⊗[k] A` given by
left multiplication by `g`. The equation `determinant_eq_det` records
this definition, and `determinant_eq_matrix_det` expresses it in the
base-changed basis `b.baseChange R`.

`candidateRing b` is `Localization.Away (determinant b)`. The actual
scheme `candidate b` over `Spec k` is the spectrum of this ring, with
the morphism induced by its canonical `k`-algebra map. Polynomial
coordinates occur in the first tensor factor throughout.

The localized generic element is the image of `g` under the tensor map
induced by `R → candidateRing b` and the identity of `A`.
`localizedGenericElement_eq_sum` gives its formula as
`∑ i, algebraMap R (candidateRing b) (X i) ⊗ b i`.
The lemma `leftMulMatrix_map` proves coefficient-change compatibility by
tensor induction, computing entries in the base-changed basis.
Taking determinants gives `norm_map`. The norm of the localized
generic element is therefore the image of `determinant b`, which is a
unit by the defining property of away-localization. The finite-free
determinant criterion makes multiplication invertible, and
`Algebra.lmul_isUnit_iff` then proves that the element itself is a unit.
`algebraicUniversalUnit b` packages this invertibility; its underlying
value is `localizedGenericElement b`.

These definitions retain rank zero. `determinant_rank_zero` proves that
for a basis indexed by `Fin 0`, the determinant is one using the empty
matrix determinant. Nilpotents and inseparable algebras are also
retained: no reducedness or separability is used. This module constructs
the affine candidate and its unit in the tensor coordinate ring; it
does not establish representability or smoothness.

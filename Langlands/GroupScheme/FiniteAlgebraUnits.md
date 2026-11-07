# Actual units of finite-dimensional noncommutative algebras

Let `k : Type u` be a field, let `A : Type u` be an associative unital
`k`-algebra, and fix a finite basis `b : Basis (Fin n) k A`.
The algebra `A` may be noncommutative or the zero algebra.
This internal construction gives an actual smooth affine group scheme
whose points on a commutative `k`-algebra `R` are `(R ⊗[k] A)ˣ`.
The test algebra may be nonreduced, and no nontriviality assumption on it
is imposed. The construction permits rank zero.

The coordinate construction generalizes the published
`AlgebraicGeometry.Units.FiniteAlgebraDeterminant` and
`AlgebraicGeometry.Units.FiniteAlgebraAffine` implementation to `Ring A`.
The new definitions and proofs are in the separate namespace
`GroupScheme.FiniteAlgebraUnits`. The original commutative-algebra modules
also compare their candidate with global units on actual scheme
pullbacks. Here the object to represent is the displayed unit functor of
the algebra `A`; no spectrum of a noncommutative ring is used.

The polynomial ring `coordinateRing k n` supplies the coefficients of
`genericElement b = ∑ i, X i ⊗ b i`.
The polynomial `determinant b` is the determinant of left multiplication
by this generic element. The Mathlib operation `Algebra.norm` used to
define it supports associative, possibly noncommutative algebras.
In this unit that operation is the regular multiplication determinant;
no identification with a reduced norm is asserted.
The ring `candidateRing b` is its away-localization.

The theorem `leftMulMatrix_map` proves compatibility of the regular
multiplication matrix with every coefficient-algebra homomorphism by
tensor induction. Taking determinants gives `norm_map`.
The localized generic element has unit determinant, so its
left-multiplication endomorphism is invertible by
`LinearMap.isUnit_iff_isUnit_det`.
The theorem `Algebra.lmul_isUnit_iff`, valid without commutativity of `A`,
therefore proves invertibility of the element itself.
This constructs `algebraicUniversalUnit b`.
For rank zero the determinant is the empty-matrix determinant, namely one.

For any commutative coefficient algebra `R`, a coordinate-ring
homomorphism specializes the universal unit.
Conversely, the base-changed basis gives the coefficients of any
`x : (R ⊗[k] A)ˣ`. Its regular multiplication determinant is a unit,
so the coefficient homomorphism extends to the away-localization.
Basis uniqueness and localization uniqueness prove both inverse laws
of `algebraicPointEquiv`.
The theorem `algebraicPoint_comp` proves naturality under every map of
coefficient algebras using the actual finite coordinate expansion.

The definition `functor k A` is the group-valued functor
`R ↦ (R ⊗[k] A)ˣ`, with coefficient changes induced by the actual tensor
algebra maps. The natural equivalences just constructed give
`corepresentableBy b`.
The existing group-valued corepresentation construction supplies
`groupScheme b`, including its actual multiplication, identity and inverse.
Its underlying relative scheme is exactly `candidate b`.
Its affineness is the spectrum construction, and its smoothness follows
from the smoothness of a finite polynomial algebra followed by an
away-localization.

The multiplicative equivalence `affinePointsEquiv b R` identifies its
actual affine coefficient points with `(R ⊗[k] A)ˣ`.
The equivalence `pointsEquiv b T` works on every scheme `T` over `Spec k`
and has target `(((algΓ k).obj T).unop ⊗[k] A)ˣ`, using the actual
relative global-section algebra. Both naturality theorems identify
the actual pullbacks with the corresponding tensor coefficient maps.
Finally, `rationalPointsEquiv b` composes the canonical
rational/coefficient comparison, the affine point equivalence and
`k ⊗[k] A ≃ₐ[k] A` on units. It identifies actual rational points with
the original group `Aˣ`.

The provenance is an internal generalization of the two published
coordinate constructions named above, together with the existing
group-valued Yoneda, affine and all-test point comparisons.
All algebraic identities used in the generalization are proved under
`Ring A`; commutativity is required only of the base and test algebras.
The polynomial reduced-norm character, its actual norm-one kernel,
elementary-root constructions, and the general local Kneser–Tits theorem
remain separate obligations.

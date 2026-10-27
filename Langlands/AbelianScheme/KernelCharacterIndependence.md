# Independence of the intrinsic kernel character

Let `f : A ⟶ B` be an actual homomorphism of abelian schemes over `S`,
let `T` be over `S`, and retain `h : UniversalGlobalFunctions A`. The
intrinsic character constructed in `IntrinsicKernelCharacter` is independent
of the actual trivialization `α : f_T^* M ≅ O_(T ×_S A)` and invariant
under isomorphism of `M`. Consequently it defines
`trivialHomPullbackClassCharacter f h` from the existing
`TrivialHomPullbackClasses f T` to the existing
`(Cartier.characters (kernelCommGroupScheme f)).obj (op T)`.
This input consists of isomorphism classes of actual line bundles with
trivial homomorphism pullback; it contains no chosen character or
action. The point construction itself works for any module having the
specified trivialization, without a local freeness assumption.

The general helper `equalCompositeUnitAut_change_trivialization` concerns
an actual scheme map `p : X → Y`, maps `a,b : U → X` with equal composite
with `p`, a module `M` on `Y`, a trivialization `α : p^*M ≅ O_X`, and an
automorphism `e` of `O_X`. Replacing `α` by `α ; e` changes the normalized
comparison to

`(a^*e)⁻¹ ; comparison(α) ; b^*e`,

where both pulled-back automorphisms are normalized by the canonical
structure-module pullback isomorphisms. Its Lean proof expands the
actual composites and cancels inverse isomorphisms.

For an ordinary parameter map `q` and its kernel translate `r`,
`kernelShear_units_eq` proves `q^*c = r^*c` for every global unit `c` on
`T ×_S A`. Indeed universal global functions descends `c` to a unit on
`T`, and both `q` and `r` have the same composite with the projection to
`T`. To compare two arbitrary trivializations `α,β`, set `e = α⁻¹ ; β`
in the helper formula, extract their global scalars, use this equality
for the scalar of `e`, and cancel the two inverse factors in the
commutative group of global units. This proves
`kernelTranslationScalar_independent`; applying the canonical descent
homomorphism gives `kernelTranslationUnit_independent`. The all-point
evaluation formula and `hom_ext_points` then prove independence of the
actual scheme homomorphism and of its Cartier character.

For `e : M ≅ N`, first compare an arbitrary trivialization of `f_T^*M`
with the trivialization transported from `f_T^*N`. The imported
`equalCompositeUnitAut_of_iso` identifies the latter comparison with the
one for `N`. This proves `kernelTranslationScalar_of_iso` and
`intrinsicKernelCharacter_of_iso` for any choices of trivialization.

`trivialHomPullbackCharacter f h L hL` chooses an actual trivialization
from the proposition `hL : HasTrivialHomPullback f T L` and constructs the
character. `trivialHomPullbackCharacter_eq` shows that it can be evaluated
using any actual trivialization. Bundle isomorphism invariance proves
that this function descends through the existing quotient by bundle
isomorphism, giving `trivialHomPullbackClassCharacter`. Its `_classOf`
lemma computes the function on a representative.

This unit is internally derived from the imported normalized comparison,
actual relative units, and actual character interfaces. It implements the
trivialization-independence step motivated by Edixhoven–van der
Geer–Moonen, *Abelian Varieties*, preliminary build 2012-02-08,
VII §§7.3–7.4, printed pp.99–100 / PDF pp.103–104. The Lean route uses
the inverse to the actual projection on units rather than selecting a
local scalar. The character retains the orientation specified in
`KernelTranslationScalar` and its evaluation formula. Comparison with
replacement of the bundle by its test-scheme pullback and tensor
compatibility are subsequent units. No effective descent, quotient
equivalence, representability or duality is asserted.

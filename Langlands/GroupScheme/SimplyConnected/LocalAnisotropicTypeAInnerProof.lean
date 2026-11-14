import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicTypeAInnerReduction
import Langlands.GroupScheme.SimplyConnected.LocalOuterTypeAHermitianModelAssembly
import Langlands.GroupScheme.SimplyConnected.OuterTypeAUnitarySplitPresentationProof
import Langlands.Algebra.LocalUnitaryDivisionCommutativeProof

/-!
# Simply connected anisotropic groups of type A over local fields are inner forms

Proof of `LocalAnisotropicTypeAInnerStatement` (Bruhat–Tits 1967, Proposition 6, inner
part). Three published results are composed:

* `outerTypeAUnitarySplitPresentation` : over any field whose unitary involution algebras
  split, an outer type `A` group is a special unitary group of a nonsingular Hermitian
  matrix over its star field;
* `localUnitaryDivisionCommutative` : over a nonarchimedean local field, unitary division
  algebras are commutative;
* `localOuterTypeAHermitianModel_of_unitarySplitting` and
  `localAnisotropicTypeAInner_of_hermitianModel` : these two inputs make every outer form
  isomorphic to a Hermitian root model, whose nonzero split cocharacter contradicts
  anisotropy.
-/

universe u

namespace Langlands.GroupScheme

/-- **Bruhat–Tits 1967, Proposition 6 (inner part).** Over a nonarchimedean local field,
an affine, simply connected, absolutely almost-simple, anisotropic group of type `A_n` has
trivial star action on its Tits index: it is an inner form. -/
theorem localAnisotropicTypeAInner : LocalAnisotropicTypeAInnerStatement.{u} :=
  localAnisotropicTypeAInner_of_hermitianModel
    (localOuterTypeAHermitianModel_of_unitarySplitting
      outerTypeAUnitarySplitPresentation localUnitaryDivisionCommutative)

end Langlands.GroupScheme

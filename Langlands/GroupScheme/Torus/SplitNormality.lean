import Langlands.Algebra.IntLatticeAlgebra
import Langlands.AlgebraicGeometry.Picard.GeometricallyUnibranchDomain
import Langlands.AlgebraicGeometry.Picard.ValuationBaseNormality
import Langlands.GroupScheme.Torus.Diagonalizable
import Mathlib.RingTheory.Polynomial.IsIntegral

/-! # Normal Laurent models of split tori -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry

namespace Langlands.IntLatticeAlgebra

/-- A Laurent polynomial ring over an integrally closed domain is integrally closed. -/
theorem isIntegrallyClosed_laurent (R : Type v) [CommRing R] [IsDomain R]
    [IsIntegrallyClosed R] : IsIntegrallyClosed (LaurentPolynomial R) :=
  isIntegrallyClosed_of_isLocalization _ (Submonoid.powers (Polynomial.X : Polynomial R))
    (powers_le_nonZeroDivisors_of_noZeroDivisors Polynomial.X_ne_zero)

/-- The algebra of a finite integer lattice over an integrally closed domain is integrally closed. -/
theorem isIntegrallyClosed (R : Type v) [CommRing R] [IsDomain R] [IsIntegrallyClosed R]
    (I : Type u) [Finite I] : IsIntegrallyClosed (AddMonoidAlgebra R (I → ℤ)) := by
  induction I using Finite.induction_empty_option with
  | of_equiv e h =>
    let := h
    exact IsIntegrallyClosed.of_equiv (congrEquiv R e).toRingEquiv
  | h_empty =>
    exact IsIntegrallyClosed.of_equiv
      (AddMonoidAlgebra.uniqueAlgEquiv R (A := R) (PEmpty → ℤ)).symm.toRingEquiv
  | @h_option I _ h =>
    let := h
    let := isIntegrallyClosed_laurent (AddMonoidAlgebra R (I → ℤ))
    exact IsIntegrallyClosed.of_equiv (optionEquiv R I).symm.toRingEquiv

end Langlands.IntLatticeAlgebra

namespace Langlands.GroupScheme

/-- An actual finite Laurent-coordinate model of a split torus with a normal domain
as its coordinate ring. The comparison is an isomorphism of group schemes over `Spec R`. -/
structure SplitTorusNormalAffineModel (R : CommRingCat.{u}) (T : GroupScheme (Spec R)) where
  index : Type u
  finite : Finite index
  domain : IsDomain (AddMonoidAlgebra R (index → ℤ))
  normal : IsIntegrallyClosed (AddMonoidAlgebra R (index → ℤ))
  iso : (Diagonalizable.groupScheme R (index → ℤ)).toGrp ≅ T

/-- A split torus over any integrally closed domain has a normal Laurent-coordinate model. -/
def IsSplitTorus.normalAffineModel {R : CommRingCat.{u}} [IsDomain R] [IsIntegrallyClosed R]
    {T : GroupScheme (Spec R)} (hT : IsSplitTorus T) : SplitTorusNormalAffineModel R T := by
  classical
  let I := hT.choose
  let : Finite I := hT.choose_spec.choose
  let : Fintype I := Fintype.ofFinite I
  let e : T ≅ splitTorus (Spec R) I := hT.choose_spec.choose_spec.some
  exact ⟨I, inferInstance, inferInstance, IntLatticeAlgebra.isIntegrallyClosed R I,
    Diagonalizable.splitIso R (AddEquiv.refl (I → ℤ)) ≪≫ e.symm⟩

namespace SplitTorusNormalAffineModel

variable {R : CommRingCat.{u}} {T : GroupScheme (Spec R)} (M : SplitTorusNormalAffineModel R T)

/-- The underlying isomorphism from the normal affine scheme. -/
def specIso : Spec (CommRingCat.of (AddMonoidAlgebra R (M.index → ℤ))) ≅ T.X.left :=
  ((Grp.forget (Over (Spec R))) ⋙ Over.forget _).mapIso M.iso

include M

/-- The normal affine model makes the underlying scheme integral. -/
theorem isIntegral : IsIntegral T.X.left := by
  let := M.domain
  exact IsIntegral.of_isIso M.specIso.hom

/-- The model identifies the actual stalks with localizations of a normal domain. -/
theorem hasNormalStalks : Langlands.AlgebraicGeometry.HasNormalStalks T.X.left := by
  let A := CommRingCat.of (AddMonoidAlgebra R (M.index → ℤ))
  let : IsDomain A := M.domain
  let : IsIntegrallyClosed A := M.normal
  intro x
  let e := (asIso (M.specIso.inv.stalkMap x)).commRingCatIsoToRingEquiv
  have h := Langlands.AlgebraicGeometry.spec_hasNormalStalks A (M.specIso.inv x)
  let := h.1
  let := h.2
  exact ⟨e.symm.injective.isDomain e.symm, IsIntegrallyClosed.of_equiv e⟩

/-- The same model supplies geometric unibranchness in the actual-stalk sense. -/
theorem geometricallyUnibranch [IsIntegral T.X.left] :
    Langlands.AlgebraicGeometry.GeometricallyUnibranchIntegralScheme T.X.left :=
  Langlands.AlgebraicGeometry.geometricallyUnibranchIntegralScheme_of_stalks _
    (fun x => (M.hasNormalStalks x).2)

end SplitTorusNormalAffineModel

end Langlands.GroupScheme

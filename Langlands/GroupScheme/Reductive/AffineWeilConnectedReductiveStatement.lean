import Langlands.GroupScheme.AffineWeilRestriction
import Langlands.GroupScheme.Reductive.Basic
import Mathlib.FieldTheory.Separable

/-! # Connected reductivity of finite separable affine Weil restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Finite separable affine Weil restriction preserves connected reductivity of
the actual group scheme. -/
def AffineWeilConnectedReductiveStatement : Prop :=
  ∀ (k K : Type u) [Field k] [Field K] [Algebra k K] [FiniteDimensional k K]
    [Algebra.IsSeparable k K] (G : GroupScheme (Spec (CommRingCat.of K)))
    (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    IsConnectedReductive (AffineWeil.groupScheme k K G)

end Langlands.GroupScheme

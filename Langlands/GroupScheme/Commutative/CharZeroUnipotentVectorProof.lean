import Langlands.GroupScheme.Commutative.CharZeroUnipotentVectorStatement
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Unipotent.CharZeroConnectedProof
import Langlands.GroupScheme.Unipotent.PerfectFieldSplitProof
import Langlands.GroupScheme.Rational.CommutativeVectorClassificationProof

/-! # Commutative unipotent groups in characteristic zero are vector groups: proof -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Milne 2017, Corollary 16.15 (second sentence): over a field of characteristic zero, every
commutative unipotent affine group scheme of finite type is a vector group. -/
theorem charZeroCommutativeUnipotentVectorGroup :
    CharZeroCommutativeUnipotentVectorGroupStatement.{u} := by
  intro k _ _ G _ _ _ hu
  have hA : IsAffineHom G.X.hom := inferInstance
  have hft : LocallyOfFiniteType G.X.hom := inferInstance
  have : Smooth G.X.hom := affineCartierSmooth k G hA hft
  have hc : ConnectedSpace G.X.left := charZeroUnipotentConnected k G hA hft hu
  obtain ⟨n, hn⟩ := perfectFieldUnipotentSplit k G hc hu
  exact ⟨n, hn.isVectorGroupOfDimension_of_commutative⟩

end Langlands.GroupScheme

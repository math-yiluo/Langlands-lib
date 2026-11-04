import Langlands.GroupScheme.Descent.AffineEffectivityStatement
import Langlands.GroupScheme.Descent.AffineDatumGroup
import Langlands.GroupScheme.Descent.FpqcHomDescent
import Langlands.GroupScheme.BaseChangeReflection

/-! # Proof of finite-Galois effective descent for actual affine group schemes -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

/-- Every actual Čech datum on an affine group over a finite Galois extension
has a solution whose descended group is affine. -/
theorem affineGroupSchemeFiniteGaloisObjectDescent :
    AffineGroupSchemeFiniteGaloisObjectDescentStatement.{u} := by
  intro k L _ _ _ _ _ p H hH datum
  obtain ⟨_, _, -⟩ := fieldExtension_fpqc k L
  have : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  exact ⟨datum.affineSolution, inferInstance⟩

/-- Every actual homomorphism between base changes of affine groups over a
finite Galois extension, compatible with the canonical data, descends uniquely. -/
theorem affineGroupSchemeFiniteGaloisHomDescent :
    AffineGroupSchemeFiniteGaloisHomDescentStatement.{u} := by
  intro k L _ _ _ _ _ p C D _ _ f hf
  obtain ⟨_, _, _⟩ := fieldExtension_fpqc k L
  exact Descent.FpqcHomDescent.existsUnique_hom p f hf

/-- Finite-Galois effective descent for arbitrary affine group schemes. -/
theorem affineGroupSchemeFiniteGaloisDescent :
    AffineGroupSchemeFiniteGaloisDescentStatement.{u} :=
  ⟨affineGroupSchemeFiniteGaloisObjectDescent, affineGroupSchemeFiniteGaloisHomDescent⟩

end Langlands.GroupScheme

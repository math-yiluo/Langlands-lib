import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicClassificationStatement
import Langlands.GroupScheme.SimplyConnected.LocalAnisotropicInnerTypeAStatement
import Langlands.GroupScheme.Reductive.TitsIndexChoiceStatement
import Langlands.GroupScheme.CentralSimpleNormOneDivisionModel
import Mathlib.LinearAlgebra.Matrix.Unique

/-!
# The local anisotropic classification from actual Tits indices

This module reduces `LocalAnisotropicSimplyConnectedClassificationStatement` to
the existence of actual Tits-index data, the local inner-type-`A` statements, the
identification of inner type `A` with a reduced-norm-one group, and the split-rank
formula for `SL_m(D)`. Each input is a published, unproved proposition and is an
explicit hypothesis of the reduction.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace CentralSimpleUnits

variable (K A : Type u) [Field K] [Ring A] [Algebra K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]

/-- Assuming the split-rank formula for `SL_m(D)`, the reduced-norm-one group of
a central simple algebra with split rank zero is the reduced-norm-one group of a
finite-dimensional central division algebra. This does not assert the formula. -/
theorem exists_division_model_of_splitRank_zero
    (hrank : MatrixNormOneSplitRankStatement.{u}) (hA : splitRank (normOne K A) = 0) :
    ∃ (D : Type u) (_ : DivisionRing D) (_ : Algebra K D)
      (_ : FiniteDimensional K D) (_ : Algebra.IsCentral K D),
      Nonempty (normOne K A ≅ normOne K D) := by
  obtain ⟨m, hm, D, hD, hKD, hfd, hcentral, e, ⟨f⟩⟩ := exists_matrix_division_model K A
  have h : ((m - 1 : ℕ) : ℕ∞) = 0 :=
    (hrank K D m).symm.trans ((splitRank_eq_of_iso f).symm.trans hA)
  have hm' : m - 1 = 0 := by exact_mod_cast h
  have hm0 : m ≠ 0 := NeZero.ne m
  obtain rfl : m = 1 := by omega
  let g : Matrix (Fin 1) (Fin 1) D ≃ₐ[K] D :=
    { Matrix.uniqueEquiv with
      map_mul' := fun M N => by simp [Matrix.mul_apply]
      map_add' := fun M N => rfl
      commutes' := fun r => by simp [Matrix.algebraMap_matrix_apply] }
  exact ⟨D, hD, hKD, hfd, hcentral, ⟨normOneAlgEquivIso (e.trans g)⟩⟩

end CentralSimpleUnits

/-- The four unproved inputs of the local anisotropic classification: existence of
actual Tits-index data, the local inner-type-`A` statements, the norm-one
identification of inner type `A`, and the split rank of `SL_m(D)`. -/
def LocalAnisotropicClassificationInputs : Prop :=
  TitsIndexExistenceStatement.{u} ∧ LocalAnisotropicInnerTypeAStatement.{u} ∧
    InnerTypeANormOneStatement.{u} ∧ CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}

/-- The classification of anisotropic simply connected absolutely almost-simple
groups over nonarchimedean local fields follows from the four inputs. -/
theorem localAnisotropicSimplyConnectedClassification_of_statements
    (hexist : TitsIndexExistenceStatement.{u})
    (htype : LocalAnisotropicInnerTypeAStatement.{u})
    (hinner : InnerTypeANormOneStatement.{u})
    (hrank : CentralSimpleUnits.MatrixNormOneSplitRankStatement.{u}) :
    LocalAnisotropicSimplyConnectedClassificationStatement.{u} := by
  intro K _ _ _ _ G _ hsc habs hG
  have : LocallyOfFiniteType G.X.hom := by
    have := hsc.isSemisimple.isConnectedReductive.smooth
    infer_instance
  obtain ⟨d⟩ := hexist K G hsc.isSemisimple
  obtain ⟨n, hn, hcartan⟩ := htype.1 K G d habs hG
  have hstar := htype.2 K G d n hsc habs hG hcartan
  obtain ⟨A, _, _, _, _, _, -, ⟨e⟩⟩ := hinner K G d n hsc habs ⟨hn, hcartan, hstar⟩
  obtain ⟨D, hD, hKD, hfd, hcentral, ⟨f⟩⟩ :=
    CentralSimpleUnits.exists_division_model_of_splitRank_zero K A hrank
      ((splitRank_eq_of_iso e).symm.trans hG)
  exact ⟨D, hD, hKD, hfd, hcentral, ⟨e ≪≫ f⟩⟩

/-- The bundled form of `localAnisotropicSimplyConnectedClassification_of_statements`. -/
theorem localAnisotropicSimplyConnectedClassification_of_inputs
    (h : LocalAnisotropicClassificationInputs.{u}) :
    LocalAnisotropicSimplyConnectedClassificationStatement.{u} :=
  localAnisotropicSimplyConnectedClassification_of_statements h.1 h.2.1 h.2.2.1 h.2.2.2

end Langlands.GroupScheme

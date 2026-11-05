import Langlands.GroupScheme.Rational.CentralVectorSeparableClosure
import Langlands.GroupScheme.Rational.WoundCentralGalois
import Langlands.GroupScheme.Rational.AffineLineFieldReflection
import Langlands.GroupScheme.Rational.UnipotentWoundCriterionStatement
import Langlands.GroupScheme.Rational.UnipotentWoundSeparableExtensionStatement
import Langlands.GroupScheme.Unipotent.BaseChange

/-! # Separable invariance from the central additive-subgroup criterion -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- The central additive-subgroup criterion implies the unchanged separable
extension proposition. The criterion is an explicit input of this reduction. -/
def WoundSeparableFromCriterionStatement : Prop :=
  UnipotentWoundCriterionStatement.{u} →
    UnipotentWoundSeparableExtensionStatement.{u}

namespace HasConstantAffineLineMaps

variable {k K : Type u} [Field k] [Field K] [Algebra k K]
    [Algebra.IsSeparable k K]
    {G : GroupScheme (Spec (CommRingCat.of k))}

/-- A separable algebraic extension cannot create a central closed vector
line in an affine, locally finite-type group with affine-line constancy. -/
theorem not_exists_central_additive_closed_subgroup_separable
    [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : HasConstantAffineLineMaps G) :
    ¬ ∃ (V : GroupScheme (Spec (CommRingCat.of K)))
      (j : V ⟶ (baseChange (algebraBaseMap k K)).obj G),
      IsClosedSubgroup j ∧ IsCentral j ∧
        RelativeRoot.IsVectorGroupOfDimension V 1 := by
  rintro ⟨V, j, hj, hc, hV⟩
  let D := separableClosureVectorSubgroup K j hj hc hV
  let : IsClosedImmersion D.hom.hom.hom.left := D.closed
  let : Mono D.hom.hom.hom := Over.mono_of_mono_left _
  exact hG.not_isCentral_of_mono_galois D.hom D.central

/-- Constancy persists under every separable algebraic extension, provided
the full central additive-subgroup criterion is supplied. -/
theorem baseChange_of_criterion
    (hC : UnipotentWoundCriterionStatement.{u})
    [Smooth G.X.hom] [IsAffineHom G.X.hom] [ConnectedSpace G.X.left]
    (hU : IsUnipotent G) (hG : HasConstantAffineLineMaps G) :
    HasConstantAffineLineMaps ((baseChange (algebraBaseMap k K)).obj G) := by
  let b := algebraBaseMap k K
  have hs : Smooth ((baseChange b).obj G).X.hom := by
    change Smooth (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have ha : IsAffineHom ((baseChange b).obj G).X.hom := by
    change IsAffineHom (CategoryTheory.Limits.pullback.snd G.X.hom b)
    infer_instance
  have hc : ConnectedSpace ((baseChange b).obj G).X.left :=
    G.connectedSpace_baseChange_of_smooth_affine b
  let : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
  exact (hC K ((baseChange b).obj G) hs ha hc hU.baseChange).2
    hG.not_exists_central_additive_closed_subgroup_separable

end HasConstantAffineLineMaps

/-- This reduction proves the exact separable-extension proposition once
the separate exact central criterion is supplied. -/
theorem woundSeparableFromCriterion : WoundSeparableFromCriterionStatement.{u} := by
  intro hC k K _ _ _ _ G _ _ _ hU
  exact ⟨HasConstantAffineLineMaps.baseChange_of_criterion hC hU,
    HasConstantAffineLineMaps.of_fieldExtension⟩

end Langlands.GroupScheme

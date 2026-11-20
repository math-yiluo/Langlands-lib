import Langlands.GroupScheme.Torus.OrderedProjectorSubgroup
import Langlands.GroupScheme.Torus.DiagonalizableAutomorphismTestLocality
import Mathlib.GroupTheory.QuotientGroup.Basic

/-! # Generation of the weights of a closed projector subgroup -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.OrderedProjectorScheme

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

/-- On a nonempty test scheme, if the homomorphism of a weighted projector family
is a closed immersion, its weights generate the character group. -/
def ClosedProjectorWeightsGenerateStatement : Prop :=
  ∀ {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
    {J n : Type} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]
    (T : Over (Spec R)) [Nonempty T.left] (w : J → Λ) (P : Family J n Γ(T.left, ⊤)),
    IsClosedSubgroup (subgroupHom w T P) → AddSubgroup.closure (Set.range w) = ⊤

variable {R : CommRingCat.{u}} {Λ : Type u} [AddCommGroup Λ]
variable {J n : Type} [Fintype J] [DecidableEq J] [Fintype n] [DecidableEq n]

private theorem restrictMap_comp_subgroupHom {M : Type u} [AddCommGroup M]
    (T : Over (Spec R)) (g h : Λ →+ M) (w : J → Λ) (P : Family J n Γ(T.left, ⊤))
    (hw : ∀ i, g (w i) = h (w i)) :
    (baseChange T.hom).map (Diagonalizable.restrictMap R g) ≫ subgroupHom w T P =
      (baseChange T.hom).map (Diagonalizable.restrictMap R h) ≫ subgroupHom w T P := by
  refine hom_ext_points fun U x => (targetPoints T n U).injective ?_
  simp only [Grp.comp_hom_hom, ← Category.assoc, targetPoints_subgroupHom]
  congr 1
  funext i
  simp only [sourcePoints, MulEquiv.trans_apply, baseChangePointsEquiv_comp]
  let p := baseChangePointsEquiv T.hom (Diagonalizable.groupScheme R M).toGrp U x
  exact (Diagonalizable.pointsEquiv_restrictMap R g p (w i)).trans
    ((congrArg (fun m => Diagonalizable.characterPointsEquiv R M ((Over.map T.hom).obj U)
      p (.ofAdd m)) (hw i)).trans (Diagonalizable.pointsEquiv_restrictMap R h p (w i)).symm)

/-- A closed projector subgroup over a nonempty test has weights generating the character
lattice. The quotient by the weights and the zero character map induce the same subgroup
morphism on matrices, hence are equal by monicity and faithfulness of character restriction. -/
theorem closure_weights_eq_top_of_isClosedSubgroup :
    ClosedProjectorWeightsGenerateStatement.{u} := by
  intro R Λ _ J n _ _ _ _ T _ w P hj
  let L := AddSubgroup.closure (Set.range w)
  let q := QuotientAddGroup.mk' L
  let j := subgroupHom w T P
  have hc : IsClosedImmersion j.hom.hom.left := hj
  let : SurjectiveOnStalks j.hom.hom.left := hc.toSurjectiveOnStalks
  let : Mono j.hom.hom.left := SurjectiveOnStalks.mono_of_injective hc.isClosedEmbedding.injective
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hq := restrictMap_comp_subgroupHom T q 0 w P fun i =>
    (QuotientAddGroup.eq_zero_iff (w i)).mpr (AddSubgroup.subset_closure ⟨i, rfl⟩)
  have he : q = 0 := by
    apply Diagonalizable.restrictMap_baseChange_injective T
    apply Grp.hom_ext
    apply (cancel_mono j.hom.hom).mp
    exact congrArg (fun f => f.hom.hom) hq
  apply eq_top_iff.mpr
  intro m _
  exact (QuotientAddGroup.eq_zero_iff m).mp (DFunLike.congr_fun he m)

end Langlands.GroupScheme.OrderedProjectorScheme

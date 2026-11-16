import Langlands.GroupScheme.Torus.FlatDiagonalizableSubgroup
import Langlands.GroupScheme.SubgroupBaseChange
import Langlands.GroupScheme.Torus.DiagonalizableGeometry
import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-! # Finiteness of flat locally quasi-finite subgroups of multiplicative-type groups -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.RelativeMultiplicativeType

variable {S : Scheme.{u}} {H : GroupScheme S}

/-- A valuative lifting problem for a split ambient group reduces to its
finite subgroup over the valuation ring. -/
def closedSubgroupValuativeLift (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (i : H ⟶ diagonalizable S Λ) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyQuasiFinite H.X.hom]
    (sq : ValuativeCommSq H.X.hom) : sq.commSq.LiftStruct := by
  let b := sq.i₂
  let H' := (GroupScheme.baseChange b).obj H
  let e := diagonalizableBaseChangeIso b Λ ≪≫
    Diagonalizable.baseChangeIso (Gm.toSpecZ (Spec (CommRingCat.of sq.R))) Λ
  let j : H' ⟶ (Diagonalizable.groupScheme (CommRingCat.of sq.R) Λ).toGrp :=
    (GroupScheme.baseChange b).map i ≫ e.hom
  have hj : IsClosedSubgroup j := (hi.baseChange b).comp_iso e
  have : IsAffine (Diagonalizable.groupScheme (CommRingCat.of sq.R) Λ).X.left :=
    isAffine_of_isAffineHom (Diagonalizable.groupScheme (CommRingCat.of sq.R) Λ).X.hom
  have : IsClosedImmersion j.hom.hom.left := hj
  have : IsAffine H'.X.left := isAffine_of_isAffineHom j.hom.hom.left
  have : Flat H'.X.hom := by
    change Flat (pullback.snd _ _)
    infer_instance
  have : LocallyQuasiFinite H'.X.hom := by
    change LocallyQuasiFinite (pullback.snd _ _)
    infer_instance
  have : IsFinite H'.X.hom := Diagonalizable.isFinite_of_flat_closedSubgroup j hj
  have hval : ValuativeCriterion.Existence H'.X.hom := by
    have hclosed : UniversallyClosed H'.X.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at hclosed
    exact hclosed.1
  let sq' : ValuativeCommSq H'.X.hom := {
    R := sq.R
    K := sq.K
    i₁ := pullback.lift sq.i₁
      (Spec.map (CommRingCat.ofHom (algebraMap sq.R sq.K))) sq.commSq.w
    i₂ := 𝟙 _
    commSq := ⟨by
      change pullback.lift _ _ _ ≫ pullback.snd _ _ = _ ≫ 𝟙 _
      simp⟩ }
  let l := (hval sq').exists_lift.some
  exact {
    l := l.l ≫ pullback.fst H.X.hom b
    fac_left := by
      simpa [sq', Category.assoc] using congrArg
        (fun a => a ≫ pullback.fst H.X.hom b) l.fac_left
    fac_right := by
      rw [Category.assoc, pullback.condition, ← Category.assoc]
      have hr := l.fac_right
      change l.l ≫ pullback.snd H.X.hom b = 𝟙 _ at hr
      simpa using congrArg (fun a => a ≫ b) hr }

/-- A flat locally quasi-finite closed subgroup of a split diagonalizable
ambient group is finite over an arbitrary base scheme. -/
theorem isFinite_of_flat_closedSubgroup (Λ : Type u) [AddCommGroup Λ] [AddGroup.FG Λ]
    (i : H ⟶ diagonalizable S Λ) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom := by
  have : IsClosedImmersion i.hom.hom.left := hi
  have : IsAffineHom (Diagonalizable.groupScheme
      (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := Diagonalizable.isAffineHom _ _
  have : IsAffineHom (diagonalizable S Λ).X.hom := by
    change IsAffineHom (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ ‹_›
  have : IsAffineHom H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : UniversallyClosed H.X.hom := UniversallyClosed.of_valuativeCriterion _
    (fun sq => ⟨⟨closedSubgroupValuativeLift Λ i hi sq⟩⟩)
  have : LocallyOfFiniteType (Diagonalizable.groupScheme
      (CommRingCat.of (ULift.{u} ℤ)) Λ).X.hom := Diagonalizable.locallyOfFiniteType _ _
  have : LocallyOfFiniteType (diagonalizable S Λ).X.hom := by
    change LocallyOfFiniteType (pullback.snd _ _)
    exact MorphismProperty.pullback_snd _ _ ‹_›
  have : LocallyOfFiniteType H.X.hom := by
    rw [← Over.w i.hom.hom]
    infer_instance
  have : IsProper H.X.hom := ⟨⟩
  exact IsFinite.iff_isProper_and_isAffineHom.mpr ⟨inferInstance, inferInstance⟩

/-- Finiteness is unchanged when the diagonalizable ambient group is
specified by an actual group-scheme isomorphism. -/
theorem IsDiagonalizable.isFinite_closedSubgroup {G : GroupScheme S}
    (hG : IsDiagonalizable G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom := by
  obtain ⟨Λ, hΛ, hfg, ⟨e⟩⟩ := hG
  let : AddCommGroup Λ := hΛ
  let : AddGroup.FG Λ := hfg
  exact isFinite_of_flat_closedSubgroup Λ (i ≫ e.hom) (hi.comp_iso e)

/-- Flat locally quasi-finite closed subgroups of groups of multiplicative
type are finite, by the split result and fppf descent. -/
theorem IsMultiplicativeType.isFinite_closedSubgroup {G : GroupScheme S}
    (hG : IsMultiplicativeType G) (i : H ⟶ G) (hi : IsClosedSubgroup i)
    [Flat H.X.hom] [LocallyQuasiFinite H.X.hom] : IsFinite H.X.hom := by
  obtain ⟨𝒰, h𝒰⟩ := hG
  have : MorphismProperty.IsLocalAtTarget (@IsFinite : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Langlands.AlgebraicGeometry.FppfLocal.isLocalAtTarget_fppfPrecoverage _
  let 𝒱 : Scheme.Cover Scheme.fppfPrecoverage S := 𝒰
  apply MorphismProperty.IsLocalAtTarget.of_zeroHypercover 𝒱
  intro a
  have : Flat ((GroupScheme.baseChange (𝒰.f a)).obj H).X.hom := by
    change Flat (pullback.snd _ _)
    infer_instance
  have : LocallyQuasiFinite ((GroupScheme.baseChange (𝒰.f a)).obj H).X.hom := by
    change LocallyQuasiFinite (pullback.snd _ _)
    infer_instance
  exact (h𝒰 a).isFinite_closedSubgroup ((GroupScheme.baseChange (𝒰.f a)).map i)
    (hi.baseChange (𝒰.f a))

end Langlands.GroupScheme.RelativeMultiplicativeType

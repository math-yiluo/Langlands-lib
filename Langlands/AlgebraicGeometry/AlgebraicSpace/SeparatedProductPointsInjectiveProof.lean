import Langlands.AlgebraicGeometry.AlgebraicSpace.SeparatedProductPointsInjectiveStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.DiagonalEqualizer
import Mathlib.AlgebraicGeometry.PointsPi

/-! # Proof of injectivity for product-ring points of separated algebraic spaces -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Opposite
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology (ringTest ringTestMap)

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

theorem separatedProductPoints_injective (C : Type u) [CommRing C]
    (X : AlgebraicSpace (Spec (CommRingCat.of C))) (hX : IsSeparated X)
    (ι : Type u) (R : ι → Type u) [∀ i, CommRing (R i)] [∀ i, Algebra C (R i)] :
    Function.Injective
      (fun (p : RingPoints C X (∀ i, R i)) (i : ι) =>
        RingPoints.changeRing (Pi.evalAlgHom C R i) p) := by
  intro p q hpq
  obtain ⟨Z, j, hj, hcl⟩ :=
    exists_representsEqualizer_of_relative_diag
      (P := @_root_.AlgebraicGeometry.IsClosedImmersion.{u}) hX
      (U := ringTest C (∀ i, R i)) p q
  have hlift : ∀ i, ∃ z : ringTest C (R i) ⟶ Z,
      z ≫ j = ringTestMap C (Pi.evalAlgHom C R i) := fun i =>
    (hj (ringTestMap C (Pi.evalAlgHom C R i))).2 (congrFun hpq i)
  choose z hz using hlift
  have : _root_.AlgebraicGeometry.IsClosedImmersion j.left := hcl
  have : IsAffine (ringTest C (∀ i, R i)).left := inferInstanceAs (IsAffine (Spec _))
  have : IsAffine Z.left :=
    (_root_.AlgebraicGeometry.IsClosedImmersion.isAffine_surjective_of_isAffine j.left).1
  let R' : ι → CommRingCat.{u} := fun i => CommRingCat.of (R i)
  let g : Z.left ⟶ Spec (CommRingCat.of (∀ i, R' i)) := j.left
  have : IsImmersion g := inferInstanceAs (IsImmersion j.left)
  have hsig : Sigma.desc (fun i => (z i).left) ≫ g = sigmaSpec R' := by
    ext1 i
    rw [Sigma.ι_comp_desc_assoc]
    change (z i ≫ j).left = _
    rw [hz i]
    show _ = Sigma.ι (fun i => Spec (R' i)) i ≫ sigmaSpec R'
    simp only [sigmaSpec, Sigma.ι_comp_desc]
    rfl
  have : IsIso g := isIso_of_comp_eq_sigmaSpec R' _ g hsig
  have : IsIso j.left := this
  let s : ringTest C (∀ i, R i) ⟶ Z := Over.homMk (inv j.left) (by
    rw [IsIso.inv_comp_eq, ← Over.w j])
  have hs : s ≫ j = 𝟙 _ := by
    ext1
    simp [s]
  have h := (hj (𝟙 _)).1 ⟨s, hs⟩
  rw [op_id, X.presheaf.map_id] at h
  exact h

/-- Proof of `SeparatedProductPointsInjectiveStatement`. -/
theorem separatedProductPointsInjective : SeparatedProductPointsInjectiveStatement.{u} :=
  fun C _ X hX ι R _ _ => separatedProductPoints_injective C X hX ι R

end Langlands.AlgebraicGeometry.AlgebraicSpace

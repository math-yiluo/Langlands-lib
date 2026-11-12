import Langlands.AlgebraicGeometry.AlgebraicSpace.UnipotentOrbitStabilizerSmoothStatement
import Langlands.GroupScheme.ReducedBaseSmoothStatement
import Langlands.GroupScheme.Unipotent.CharZeroConnectedStatement
import Langlands.GroupScheme.SchemeActionStabilizer
import Langlands.GroupScheme.AffineCartierSmoothProof
import Langlands.GroupScheme.Reductive.UnipotentFieldExtensionProof
import Langlands.GroupScheme.UnipotentClosedSubgroupProof
import Mathlib.Data.ENat.Monoid

/-!
# Smooth stabilizers of unipotent actions, from SGA 3 VI_B 4.4 and Milne 14.15

`UnipotentOrbitStabilizerSmoothStatement` follows from the reduced-base smoothness criterion
`ReducedBaseConnectedFibreSmoothStatement` (SGA 3, Exposé VI_B, Corollaire 4.4) and the
connectedness of unipotent groups in characteristic zero
`CharZeroUnipotentConnectedStatement` (Milne, Corollary 14.15). The stabilizer scheme is a
group scheme over `Z` whose fibres are closed subgroups of the base changes of `G`; they are
unipotent, smooth by Cartier's theorem and connected, of constant dimension.
-/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open _root_.AlgebraicGeometry
open Langlands (GroupScheme)
open Langlands.GroupScheme (SchemeAction IsUnipotent)
open Langlands.GroupScheme.ActionStabilizer

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

set_option linter.defProp false in
/-- `UnipotentOrbitStabilizerSmoothStatement` follows from SGA 3, Exposé VI_B,
Corollaire 4.4 over a reduced locally Noetherian base with connected fibres, and from the
connectedness of unipotent groups in characteristic zero (Milne, Corollary 14.15). -/
def unipotentOrbitStabilizerSmooth_of_reducedBase_of_charZeroConnected
    (hA : GroupScheme.ReducedBaseConnectedFibreSmoothStatement.{u})
    (hB : GroupScheme.CharZeroUnipotentConnectedStatement.{u}) :
    UnipotentOrbitStabilizerSmoothStatement.{u} := by
  intro k _ _ G hGa hGl hGu Z hZr hZl b d hd
  have : IsAffineHom G.X.hom := hGa
  have : LocallyOfFiniteType G.X.hom := hGl
  have : LocallyOfFiniteType Z.hom := hZl
  have hfib : ∀ z : Z.left, Smooth ((stabProj b).left.fiberToSpecResidueField z) ∧
      ConnectedSpace ((stabProj b).left.fiber z) := by
    intro z
    obtain ⟨φ, hφ⟩ := Spec.map_surjective (Z.left.fromSpecResidueField z ≫ Z.hom)
    let : Algebra k (Z.left.residueField z) := φ.hom.toAlgebra
    have : CharZero (Z.left.residueField z) :=
      charZero_of_injective_algebraMap (algebraMap k (Z.left.residueField z)).injective
    have hr : Z.left.fromSpecResidueField z ≫ Z.hom =
        Spec.map (CommRingCat.ofHom (algebraMap k (Z.left.residueField z))) := hφ.symm
    let GK := (GroupScheme.baseChange
      (Spec.map (CommRingCat.ofHom (algebraMap k (Z.left.residueField z))))).obj G
    let E := (GroupScheme.baseChange (Z.left.fromSpecResidueField z)).obj (stabilizerGroup b)
    let j : E ⟶ GK := fibreHom b (Z.left.fromSpecResidueField z) hr
    have hj : GroupScheme.IsClosedSubgroup j := isClosedSubgroup_fibreHom b _ hr
    have : _root_.AlgebraicGeometry.IsClosedImmersion j.hom.hom.left := hj
    have hGKa : IsAffineHom GK.X.hom := by
      change IsAffineHom (pullback.snd G.X.hom _)
      infer_instance
    have hGKl : LocallyOfFiniteType GK.X.hom := by
      change LocallyOfFiniteType (pullback.snd G.X.hom _)
      infer_instance
    have hGKu : IsUnipotent GK :=
      GroupScheme.unipotentFieldExtensionStatement k (Z.left.residueField z) G hGa hGl hGu
    have hEw : j.hom.hom.left ≫ GK.X.hom = E.X.hom := Over.w j.hom.hom
    have hEa : IsAffineHom E.X.hom := by
      rw [← hEw]
      infer_instance
    have hEl : LocallyOfFiniteType E.X.hom := by
      rw [← hEw]
      infer_instance
    have hEu : IsUnipotent E := GroupScheme.unipotentClosedSubgroup _ GK E j hj hGKu
    exact ⟨GroupScheme.affineCartierSmooth (Z.left.residueField z) E hEa hEl,
      hB (Z.left.residueField z) E hEa hEl hEu⟩
  have hdim : ∀ z z' : Z.left, topologicalKrullDim ((stabProj b).left.fiber z) =
      topologicalKrullDim ((stabProj b).left.fiber z') := by
    intro z z'
    have h1 : topologicalKrullDim G.X.left =
        topologicalKrullDim ((stabProj b).left.fiber z) + (d : WithBot ℕ∞) := hd z
    have h2 : topologicalKrullDim G.X.left =
        topologicalKrullDim ((stabProj b).left.fiber z') + (d : WithBot ℕ∞) := hd z'
    exact ENat.WithBot.add_natCast_cancel.mp (h1.symm.trans h2)
  have : IsLocallyNoetherian Z.left := LocallyOfFiniteType.isLocallyNoetherian Z.hom
  exact hA Z.left (stabilizerGroup b) hZr inferInstance
    (inferInstance : LocallyOfFiniteType (stabProj b).left) (fun z => (hfib z).1)
    (fun z => (hfib z).2) (IsLocallyConstant.of_constant _ hdim)

end Langlands.AlgebraicGeometry.AlgebraicSpace

import Langlands.GroupScheme.Reductive.RootDatum
import Langlands.GroupScheme.Rational.RelativeCentralDirections
import Mathlib.LinearAlgebra.RootSystem.Hom
import Mathlib.Logic.Equiv.Set

/-! # Assembling a morphism of actual root data from root and coroot compatibility -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.RootDatumHom

variable {k : Type u} [Field k]
  {T T' : CommGroupScheme (Spec (CommRingCat.of k))}
  {J : Type v} {J' : Type w}
  (P : RootDatum J (characterLattice T) (cocharacterLattice T))
  (P' : RootDatum J' (characterLattice T') (cocharacterLattice T'))
  (t : T ⟶ T')

/-- The root-index equivalence induced by a bijection of root ranges under actual character
pullback. -/
def rootIndexEquivOfPullback
    (hroot : Set.BijOn (fun χ : characterLattice T' => t ≫ χ)
      (Set.range P'.root) (Set.range P.root)) : J' ≃ J :=
  (Equiv.ofInjective P'.root P'.root.injective).trans
    ((Set.BijOn.equiv _ hroot).trans (Equiv.ofInjective P.root P.root.injective).symm)

theorem rootIndexEquivOfPullback_root
    (hroot : Set.BijOn (fun χ : characterLattice T' => t ≫ χ)
      (Set.range P'.root) (Set.range P.root)) (j' : J') :
    P.root (rootIndexEquivOfPullback P P' t hroot j') = t ≫ P'.root j' := by
  exact Equiv.apply_ofInjective_symm P.root.injective _

/-- Actual character pullback and cocharacter pushforward define a morphism of root pairings
once the root bijection and the matching-coroot law have been established. -/
def ofRootCoroot
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (hroot : Set.BijOn (fun χ : characterLattice T' => t ≫ χ)
      (Set.range P'.root) (Set.range P.root))
    (hcoroot : ∀ (j : J) (j' : J'), t ≫ P'.root j' = P.root j →
      P.coroot j ≫ t = P'.coroot j') :
    RootPairing.Hom P' P where
  weightMap := (characterRestrict (CommGroupScheme.groupHom t)).toIntLinearMap
  coweightMap := RealTorusSpace.cocharacterMapInt t
  indexEquiv := rootIndexEquivOfPullback P P' t hroot
  weight_coweight_transpose := by
    ext ν χ
    change P.toLinearMap (t ≫ χ) ν = P'.toLinearMap χ (ν ≫ t)
    rw [hP, hP']
    exact congrArg (gmEndEquiv k) (Category.assoc ν t χ)
  root_weightMap := by
    funext j'
    exact (rootIndexEquivOfPullback_root P P' t hroot j').symm
  coroot_coweightMap := by
    funext j
    apply hcoroot j ((rootIndexEquivOfPullback P P' t hroot).symm j)
    rw [← rootIndexEquivOfPullback_root P P' t hroot, Equiv.apply_symm_apply]

@[simp]
theorem ofRootCoroot_weightMap
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (hroot : Set.BijOn (fun χ : characterLattice T' => t ≫ χ)
      (Set.range P'.root) (Set.range P.root))
    (hcoroot : ∀ (j : J) (j' : J'), t ≫ P'.root j' = P.root j →
      P.coroot j ≫ t = P'.coroot j') (χ : characterLattice T') :
    (ofRootCoroot P P' t hP hP' hroot hcoroot).weightMap χ = t ≫ χ :=
  rfl

@[simp]
theorem ofRootCoroot_coweightMap
    (hP : P.toLinearMap = latticePairing T) (hP' : P'.toLinearMap = latticePairing T')
    (hroot : Set.BijOn (fun χ : characterLattice T' => t ≫ χ)
      (Set.range P'.root) (Set.range P.root))
    (hcoroot : ∀ (j : J) (j' : J'), t ≫ P'.root j' = P.root j →
      P.coroot j ≫ t = P'.coroot j') (ν : cocharacterLattice T) :
    (ofRootCoroot P P' t hP hP' hroot hcoroot).coweightMap ν = ν ≫ t :=
  rfl

end Langlands.GroupScheme.RootDatumHom

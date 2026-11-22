import Langlands.GroupScheme.Rational.PositiveTorusTriangularCoordinatesProof
import Langlands.GroupScheme.Rational.RenardRadicalWeightComparison
import Langlands.GroupScheme.Rational.StandardCocharacterProof
import Langlands.GroupScheme.Rational.RelativeRootSystemProof

/-! # Polynomial eigen-coordinates on standard unipotent radicals -/

noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open AlgebraicGeometry CategoryTheory Set MvPolynomial
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

open Langlands.AlgebraicGeometry.PointTopology
open TorusUnipotence CharacterUnits RelativeRoot

variable {k : Type u} [Field k]
  {G U : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [IsAffine U.X.left]
  {T : CommGroupScheme (Spec (CommRingCat.of k))} (i : T.toGrp ⟶ G)
  (j : U ⟶ G)

/-- Polynomial coordinates vanishing at the identity and scaled by the characters `w`
under conjugation by the split torus. -/
def IsConjugationEigenCoordinates {d : ℕ} (t : Fin d → AffineCoordinateRing k U.X)
    (w : Fin d → characterLattice T) : Prop :=
  Function.Bijective (aeval t : MvPolynomial (Fin d) k →ₐ[k] AffineCoordinateRing k U.X) ∧
  (∀ (A : CommAlgCat.{u} k) a, U.affinePointEvaluation A 1 (t a) = 0) ∧
  ∀ (A : CommAlgCat.{u} k) (s : GroupScheme.affinePoints T.toGrp A) (x y : U.affinePoints A),
    U.affinePointsTarget j A y =
      GroupScheme.affinePointsTarget T.toGrp i A s * U.affinePointsTarget j A x *
        (GroupScheme.affinePointsTarget T.toGrp i A s)⁻¹ →
    ∀ a, U.affinePointEvaluation A y (t a) = (Lie.characterValue (w a) s : A) *
      U.affinePointEvaluation A x (t a)

private theorem exists_eigenCoordinates_of_dynamic [Smooth G.X.hom]
    [IsClosedImmersion j.hom.hom.left] (hT : IsSplitTorus T.toGrp) (zeta : cocharacterLattice T)
    (hj : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j) :
    ∃ (d : ℕ) (t : Fin d → AffineCoordinateRing k U.X) (w : Fin d → characterLattice T),
      IsConjugationEigenCoordinates i j t w ∧ ∀ a, w a ∈ positiveRelativeRoots i zeta := by
  let S := Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)
  let b := AutomorphicAction.conjugation i
  have hS : b.IsStable S := Dynamic.unipotent_isStable_conjugation i _
  let c := b.onRepresentedSubgroup j hj hS
  let : Mono j.hom.hom := hj.1
  let : IsAffineHom U.X.hom := isAffineHom_of_isAffine _
  let : LocallyOfFiniteType U.X.hom := by
    rw [← Over.w j.hom.hom]
    infer_instance
  let : Smooth U.X.hom := (dynamicSmooth k G (CommGroupScheme.groupHom zeta ≫ i) U j).2.2 hj
  have hU : ConnectedSpace U.X.left := DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G _ hj
  have hweight (χ : characterLattice T) :
      actionWeightSpace c χ ≠ ⊥ ↔ χ ∈ positiveRelativeRoots i zeta := by
    rw [← mem_actionWeightSupport_iff_onRepresentedSubgroup b j hj hS,
      actionWeightSupport_dynamicUnipotent_of_locallyOfFiniteType hT i zeta]
  have hpos (χ : characterLattice T) (hχ : χ ∈ CoordinateWeights.support c) :
      0 < latticePairing T χ zeta := by
    have hcmp := CoordinateWeights.coordinateSemigroupComparison.2 k U inferInstance inferInstance
      hU T hT c (positiveSemigroup zeta)
    refine (hcmp.mpr ?_) hχ
    intro ψ hψ
    rw [actionWeightSupport_top] at hψ
    exact ((hweight ψ).mp hψ).2
  obtain ⟨d, w, t, hbij, hwt, hzero, _, _⟩ := exists_positiveWeight_coordinates hT c zeta hpos
  refine ⟨d, fun a => coordToSections U (t a), w, ⟨?_, ?_, ?_⟩, ?_⟩
  · have h : (aeval (fun a => coordToSections U (t a)) :
        MvPolynomial (Fin d) k →ₐ[k] AffineCoordinateRing k U.X) =
        (coordToSections U).comp (aeval t) := by rw [MvPolynomial.comp_aeval]
    rw [h, AlgHom.coe_comp]
    exact (coordSectionsEquiv U).bijective.comp hbij
  · intro A a
    rw [affinePointEvaluation_coordToSections', Lie.pointCoordinates_one, AlgHom.comp_apply]
    change algebraMap k A (coordCounit U (t a)) = 0
    rw [hzero a, map_zero]
  · intro A s x y hy a
    have hy' : y = c.act s x := by
      rw [← cancel_mono j.hom.hom, AutomorphicAction.onRepresentedSubgroup_act_comp,
        AutomorphicAction.conjugation_act]
      exact hy
    rw [affinePointEvaluation_coordToSections', affinePointEvaluation_coordToSections', hy']
    exact (show CoordinateWeights.IsEigenfunction c (w a) (t a) from hwt a) A s x
  · intro a
    apply (hweight (w a)).mp
    intro hbot
    have he := finrank_actionWeightSpace hT c hbij hwt hzero (w a)
    rw [hbot, finrank_bot] at he
    have : Nonempty {l // w l = w a} := ⟨⟨a, rfl⟩⟩
    have : 0 < Nat.card {l // w l = w a} := Nat.card_pos
    omega

/-- The polynomial coordinate weights of a standard radical are positive roots outside the
additive monoid of the Levi's simple roots. -/
def StandardUnipotentEigenCoordinatesStatement : Prop :=
  IsConnectedReductive G → IsMaximalSplitTorus i → ∀ (ν : cocharacterLattice T),
  IsGenericCocharacter i ν → ∀ J ⊆ simpleRelativeRoots i ν,
    IsClosedImmersion j.hom.hom.left → SubgroupFunctor.range j = standardUnipotent i ν J →
    ∃ (d : ℕ) (t : Fin d → AffineCoordinateRing k U.X) (w : Fin d → characterLattice T),
      IsConjugationEigenCoordinates i j t w ∧
        ∀ a, w a ∈ positiveRelativeRoots i ν ∧ w a ∉ AddSubmonoid.closure J

theorem standardUnipotentEigenCoordinates :
    StandardUnipotentEigenCoordinatesStatement i j := by
  intro hG hi ν hν J hJ hclosed hj
  let : Mono i.hom.hom.left := hi.isSplitSubtorus.mono
  let : Smooth G.X.hom := hG.smooth
  let : IsClosedImmersion j.hom.hom.left := hclosed
  let : Mono j.hom.hom := Over.mono_of_mono_left _
  have hT := hi.isSplitSubtorus.1
  obtain ⟨⟨zeta, hzeta⟩, hcomp⟩ := standardCocharacter k G hG T i hi ν hν J hJ
  have hrep : (Dynamic.unipotent (CommGroupScheme.groupHom zeta ≫ i)).IsRepresentedBy j :=
    ⟨inferInstance, hj.trans (hcomp zeta hzeta).2.2⟩
  obtain ⟨d, t, w, hcoords, hw⟩ := exists_eigenCoordinates_of_dynamic i j hT zeta hrep
  refine ⟨d, t, w, hcoords, fun a => ?_⟩
  have hp := hw a
  have hpν : w a ∈ positiveRelativeRoots i ν := by
    refine ⟨hp.1, ?_⟩
    by_contra hneg
    have hne := hν _ hp.1
    have hroot := relativeRootSystem k G hG T i hi
    have hn : -w a ∈ positiveRelativeRoots i ν :=
      ⟨hroot.neg_mem_relativeRoots i hT hp.1, by simp only [map_neg, LinearMap.neg_apply]; omega⟩
    have hnp := hzeta.pairing_nonneg_of_positive i ν hn
    simp only [map_neg, LinearMap.neg_apply] at hnp
    have hpz := hp.2
    omega
  exact ⟨hpν, (hzeta.pairing_pos_iff_not_mem_closure i ν hpν).mp hp.2⟩

end Langlands.GroupScheme

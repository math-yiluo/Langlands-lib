import Langlands.Representation.Aubert.General.RationalIntersectionLeviConjugation
import Langlands.Representation.Aubert.General.LeviConjugation
import Langlands.Representation.Aubert.General.RationalInductionStagesGeometry

/-! # A common actual term for rational Jacquet cancellation -/

noncomputable section

open Classical

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep Group.RelativeWeylIndexing
open Langlands.AlgebraicGeometry.PointTopology

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left]
  (ν : cocharacterLattice T) [Fintype (SimpleRoot i ν)]
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)
  {CM : CoxeterMatrix (SimpleRoot i ν)}
  (cs : ActualCoxeterSystem (torusPoints i) CM)
  (hLength : RootLengthComparison i ν hN hZ cs)
  (hSimple : PositiveSimpleReflectionComparison i ν hN hZ cs)
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hConj : StandardLeviConjugationStatement.{u})

include hLength hSimple hG hi hν hConj in
/-- A supported common label identifies the actual fine Levis by the given
normalizer lift. Only the existence of one minimum representative index is
used to derive this membership statement. -/
theorem commonJacquetConjugationMembership
    (J : Finset (SimpleRoot i ν)) (w : Weyl i) (K : Finset (SimpleRoot i ν))
    (h : ∃ I, IsMinimal cs J I w ∧ simpleImage cs w I ∩ J = K)
    (n : Group.RelativeWeyl.normalizer (torusPoints i)) (hn : QuotientGroup.mk n = w) :
    ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J (K.subtype (· ∈ J))) ↔
        (n : RationalPoint k G.X)⁻¹ * x * (n : RationalPoint k G.X) ∈
          levi i ν (simpleImage cs w⁻¹ K) := by
  classical
  obtain ⟨I, hw, rfl⟩ := h
  have hK : leviIndex J ((simpleImage cs w I ∩ J).subtype (· ∈ J)) =
      simpleImage cs w I ∩ J :=
    Finset.subtype_map_of_mem fun _ ha => (Finset.mem_inter.mp ha).2
  have hH : simpleImage cs w⁻¹ (simpleImage cs w I ∩ J) =
      simpleImage cs w⁻¹ J ∩ I := by
    simpa only [inv_inv] using simpleImage_inv_inter cs w⁻¹ J I
  rw [hK, hH]
  have hchar : weylAction i ((normalizerEquiv i hN).symm n) ''
      rootSet i ν (simpleImage cs w⁻¹ J ∩ I) =
        rootSet i ν (simpleImage cs w I ∩ J) := by
    rw [← weylCharacterAction_point_mk i hN hZ, hn]
    exact rootSet_simpleImage_intersections i ν hN hZ cs hLength hSimple I J w hw
  exact conjugationMembership_of_map_eq _
    (levi_map_conj_of_character_image i ν hG hi hν hConj _ _
      ((normalizerEquiv i hN).symm n) hchar)

section Topology

variable [TopologicalSpace k]

local instance rationalJacquetCommonTermPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hInter : StandardLeviIntersectionStatement.{u})
  (hStandard : StandardCocharacterStatement.{u})
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (hM : ∀ A, IsClosed (levi i ν A : Set (RationalPoint k G.X)))
  (hfl : ∀ A, ParabolicFiniteLength.{u, max (u + 1) v}
    (isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν A) (hU A))
  (hLfl : ∀ J, letI := (hM J).locallyCompactSpace
    ∀ I : Finset J, ParabolicFiniteLength.{u, max (u + 1) v}
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
      ((hU (leviIndex J I)).preimage continuous_subtype_val))
  (J : Finset (SimpleRoot i ν))
  (lift : Weyl i → Group.RelativeWeyl.normalizer (torusPoints i))
  (hlift : ∀ w, QuotientGroup.mk (lift w) = w)

/-- The common actual term indexed by a Weyl element and a target fine
label. Supported labels use actual normalized induction, fine conjugation
and ambient Jacquet restriction; the remaining labels have value zero. -/
def rationalCommonJacquetTerm (w : Weyl i) (K : Finset (SimpleRoot i ν)) :
    FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) →ₗ[ℤ]
      FiniteLengthGrothendieckGroup.{0, u, max (u + 1) v} ℂ (levi i ν J) := by
  classical
  exact if h : ∃ I, IsMinimal cs J I w ∧ simpleImage cs w I ∩ J = K then
    (LeviConjugation.inductionMap.{u, max (u + 1) v}
      (hM J)
      (levi_le_of_subset i ν hInter hG hi hν _ J
        (leviIndex_subset J (K.subtype (· ∈ J))))
      (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J (K.subtype (· ∈ J)))
      (hU (leviIndex J (K.subtype (· ∈ J)))) (hLfl J (K.subtype (· ∈ J)))).comp
        ((conjugationK0.{u, max (u + 1) v} (lift w : RationalPoint k G.X)
          (commonJacquetConjugationMembership i ν hN hZ cs hLength hSimple
            hG hi hν hConj J w K h (lift w) (hlift w))).comp
          (jacquetK0.{u, max (u + 1) v}
            (isSemidirectDecomposition_of_standardCocharacterStatement
              i ν hStandard hG hi hν (simpleImage cs w⁻¹ K))
            (hU (simpleImage cs w⁻¹ K))
            (hfl (simpleImage cs w⁻¹ K)).2.2.1
            (hfl (simpleImage cs w⁻¹ K)).2.2.2))
    else 0

/-- Evaluate a supported common term using any proof of the actual fine
conjugation membership. Its value does not retain a choice of source index. -/
theorem rationalCommonJacquetTerm_of_supported
    (w : Weyl i) (K : Finset (SimpleRoot i ν))
    (h : ∃ I, IsMinimal cs J I w ∧ simpleImage cs w I ∩ J = K)
    (hFine : ∀ x : RationalPoint k G.X,
      x ∈ levi i ν (leviIndex J (K.subtype (· ∈ J))) ↔
        (lift w : RationalPoint k G.X)⁻¹ * x * (lift w : RationalPoint k G.X) ∈
          levi i ν (simpleImage cs w⁻¹ K)) :
    rationalCommonJacquetTerm.{u, v}
        i ν hN hZ cs hLength hSimple hG hi hν hConj
        hInter hStandard hU hM hfl hLfl J lift hlift w K =
      (LeviConjugation.inductionMap.{u, max (u + 1) v}
        (hM J)
        (levi_le_of_subset i ν hInter hG hi hν _ J
          (leviIndex_subset J (K.subtype (· ∈ J))))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J (K.subtype (· ∈ J)))
        (hU (leviIndex J (K.subtype (· ∈ J)))) (hLfl J (K.subtype (· ∈ J)))).comp
          ((conjugationK0.{u, max (u + 1) v} (lift w : RationalPoint k G.X) hFine).comp
            (jacquetK0.{u, max (u + 1) v}
              (isSemidirectDecomposition_of_standardCocharacterStatement
                i ν hStandard hG hi hν (simpleImage cs w⁻¹ K))
              (hU (simpleImage cs w⁻¹ K))
              (hfl (simpleImage cs w⁻¹ K)).2.2.1
              (hfl (simpleImage cs w⁻¹ K)).2.2.2)) := by
  classical
  simp only [rationalCommonJacquetTerm, dite_eq_left h]

end Topology

end Langlands.Aubert.General.RationalPointFamily

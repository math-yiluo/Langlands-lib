import Langlands.Representation.Aubert.General.RationalTerminalJacquet
import Langlands.Representation.Aubert.General.RationalSupportCategoryTargets
import Langlands.Representation.Aubert.General.RationalJacquetTransitivity
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RestrictedLeviTopology
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RootAssociationLaws

/-! # Jacquet cuspidality of support objects from support vanishing -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

section Association

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}
  [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) [Mono i.hom.hom.left] (ν : cocharacterLattice T)
  (hN : HasPointNormalizerComparison i) (hZ : HasPointCentralizerComparison i)

/-- No standard subset contained in a proper Levi index of `I` is associated
to `I`: association preserves the number of simple roots. -/
theorem not_rootAssociation_of_subset_leviIndex
    (I : Finset (SimpleRoot i ν)) (K : Finset I) (hK : K ≠ Finset.univ)
    (J : Finset (SimpleRoot i ν)) (hJ : J ⊆ leviIndex I K)
    (n : RationalPoint k G.X) :
    ¬ rootAssociation i ν hN hZ I J n := by
  intro hIJ
  have hcard := rootAssociation_card_eq i ν hN hZ hIJ
  have hle : J.card ≤ K.card :=
    (Finset.card_le_card hJ).trans_eq (card_leviIndex I K)
  have hlt : K.card < Fintype.card I := (Finset.card_lt_iff_ne_univ K).mpr hK
  rw [Fintype.card_coe] at hlt
  omega

end Association

section Transfer

variable {H : Type*} [Group H] [TopologicalSpace H]

/-- A zero carrier transfers backwards along an isomorphism of smooth
representations. -/
theorem subsingleton_of_smoothRepIso {A B : SmoothRep.{0, _, v} ℂ H} (e : A ≅ B)
    [Subsingleton B] : Subsingleton A := by
  have hinv : Function.LeftInverse (SmoothRep.hom e.inv) (SmoothRep.hom e.hom) := by
    intro z
    change SmoothRep.hom (e.hom ≫ e.inv) z = z
    rw [e.hom_inv_id]
    rfl
  exact hinv.injective.subsingleton

end Transfer

section Stages

variable {k : Type u} [Field k] [ValuativeRel k] [TopologicalSpace k]
  [IsNonarchimedeanLocalField k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))} [IsAffineHom G.X.hom]
  (i : T.toGrp ⟶ G) (ν : cocharacterLattice T)
  (hInter : StandardLeviIntersectionStatement.{u})
  (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
  (hν : IsGenericCocharacter i ν) (hStandard : StandardCocharacterStatement.{u})

local instance rationalJacquetCuspidalPointTopology :
    TopologicalSpace (RationalPoint k G.X) := pointTopology

variable
  [LocallyCompactSpace (RationalPoint k G.X)]
  [NonarchimedeanGroup (RationalPoint k G.X)]
  (hU : ∀ A, IsClosed (unipotent i ν A : Set (RationalPoint k G.X)))
  (J : Finset (SimpleRoot i ν)) (I : Finset J)

/-- Actual normalized Jacquet restriction in stages for the literal standard
families. Continuity of the standard projections and the compact-limit
property of the restricted radical are both derived from the
standard-cocharacter statement, so only closedness of radicals and of the
coarse Levi remain as inputs. -/
def standardJacquetStagesIso_of_standardCocharacterStatement
    (hM : IsClosed (levi i ν J : Set (RationalPoint k G.X))) :
    jacquetFunctor.{u, max (u + 1) v}
        (isSemidirectDecomposition_of_standardCocharacterStatement
          i ν hStandard hG hi hν J) (hU J) ⋙
      leviNormalizedJacquetFunctor hM
        (levi_le_of_subset i ν hInter hG hi hν _ J (leviIndex_subset J I))
        (isSemidirectDecomposition_in_levi i ν hInter hG hi hν J I)
        (hU (leviIndex J I)) ≅
    jacquetFunctor
      (isSemidirectDecomposition_of_standardCocharacterStatement
        i ν hStandard hG hi hν (leviIndex J I)) (hU (leviIndex J I)) :=
  standardJacquetStagesIso_of_standardProjection.{u, v}
    i ν hInter hG hi hν hStandard hU
    (continuous_standard_projection i ν hStandard hG hi hν) J I hM
    (standardLeviUnipotent_isLimitOfCompactSubgroups i ν
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν) J hM I)

end Stages

/-- Jacquet cuspidality of every member of `Alg({I})` follows from the
full-smooth vanishing of `r_K` outside the support: for a proper `K' ⊂ I`,
transitivity identifies the Jacquet module of `r_I(E)` inside `M(I)` along
`K'` with `r_K(E)` for `K = leviIndex I K'`, and no subset of `K` is associated
to `I`. -/
theorem rationalJacquetCuspidal_of_jacquetVanishing
    (hvan : RationalSupportCategoryJacquetVanishingStatement.{u, v}) :
    RationalJacquetCuspidalStatement.{u, v} := by
  intro k _ _ _ _ G hG T i hi
  let := hG.isAffineHom
  let := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hN hZ hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro _ I E hE K'
  have hvanK := hvan k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM
    I (leviIndex I K'.1)
    (fun J n hJ hIJ _ =>
      not_rootAssociation_of_subset_leviIndex i ν hN hZ I K'.1 K'.2 J hJ n hIJ)
    E hE
  let e := (standardJacquetStagesIso_of_standardCocharacterStatement.{u, v}
    i ν hInter hG hi hν hStandard hU I K'.1 (hM I)).app E
  have hsrc := subsingleton_of_smoothRepIso e
  exact hsrc

end Langlands.Aubert.General.RationalPointFamily

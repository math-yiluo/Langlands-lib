import Langlands.Representation.Aubert.General.RationalSupercuspidalInductionInputsStatement
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.RationalWeylComparisonProof
import Langlands.Representation.Aubert.General.RootAssociationLaws
import Langlands.Representation.Aubert.General.InductionCarrierTransport
import Langlands.Representation.Aubert.General.CuspidalRemainderProjection
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Filtration.ExactFamilyLengthProof

/-! # Finite length of actual supercuspidal induction from detection and Jacquet lengths -/

noncomputable section

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RationalPointFamily

open GroupScheme SmoothRep
open Langlands.AlgebraicGeometry.PointTopology

/-- Associated Jacquet detection and finite length of the associated Jacquet
modules imply finite length of actual supercuspidal induction. -/
theorem rationalSupercuspidalInductionFiniteLengthFromInputs :
    RationalSupercuspidalInductionFiniteLengthFromInputsStatement.{u, v} := by
  intro hdet hfin k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  intro h hL I σ hσ hcusp
  classical
  obtain ⟨hN, hZ⟩ := rationalWeylComparison k G hG T i hi
  -- Lift the input carrier to the carrier universe of the two inputs.
  let σ' := SmoothRep.universeLift.{u + 1} σ
  have hσ' : σ'.IsIrreducible := (SmoothRep.isIrreducible_universeLift_iff σ).mpr hσ
  have hcusp' : IsLeviCuspidal (parabolic i ν) (levi i ν) (unipotent i ν)
      hU I (hM I) (hL I) σ' := by
    let := (hM I).locallyCompactSpace
    exact IsCuspidalFor.of_surjective_intertwiner hcusp
      (SmoothRep.universeLiftEquiv.{u + 1} σ).toIntertwiningMap
      (SmoothRep.universeLiftEquiv.{u + 1} σ).surjective
  let A := (normalizedInductionFunctor.{u, max (u + 1) v} (h I) (hU I)).obj σ'
  -- The finite family of associated standard indices.
  let Idx := {J : Finset (SimpleRoot i ν) // ∃ n, rootAssociation i ν hN hZ I J n}
  let F : ∀ J : Idx, SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X) ⥤
      SmoothRep.{0, u, max (u + 1) v} ℂ (levi i ν J.1) :=
    fun J => jacquetFunctor (h J.1) (hU J.1)
  have hF : ∀ J, Derivative.Mirabolic.MapsShortExactIntertwiners (F J) := by
    intro J B C D f g hf hg hex
    have hs := jacquetFunctor_map_isShortExact (h J.1) (hU J.1)
      (standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
        i ν hStandard hG hi hν J.1) f g ⟨hf, hg, hex⟩
    exact ⟨hs.1, hs.2.2, hs.2.1⟩
  have hfinJ : ∀ J : Idx, repLength ((F J).obj A).representation ≠ ⊤ := by
    intro J
    obtain ⟨n, hn⟩ := J.2
    exact Module.length_ne_top_iff.mpr
      (hfin k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM I J.1 n hn σ' hσ' hcusp')
  let bnd : Idx → ℕ := fun J => (repLength ((F J).obj A).representation).toNat
  have hb : ∀ J, repLength ((F J).obj A).representation ≤ (bnd J : ℕ∞) :=
    fun J => (ENat.natCast_toNat (hfinJ J)).ge
  -- Every irreducible subquotient is detected along an associated index.
  have hrefl : rootAssociation i ν hN hZ I I 1 := rootAssociation_one i ν hN hZ I
  have hAlg := isInSupportCategory_cuspidalInduction.{_, u, max (u + 1) v}
    (h := h) (hU := hU) (hM := hM I) (hI := hL I) hrefl σ' hσ' hcusp'
  have hdetect : ∀ D : SmoothRep.{0, u, max (u + 1) v} ℂ (RationalPoint k G.X),
      D.IsIrreducible → SmoothRep.IsSubquotient D A → ∃ J, Nontrivial ((F J).obj D) := by
    intro D hD hDA
    obtain ⟨J, n, hassoc, -, hnt⟩ :=
      hdet k G hG T i hi ν hν hStandard hInter hRoots hN hZ hU hM I D hD
        (hAlg.of_isSubquotient hDA)
    exact ⟨⟨J, n, hassoc⟩, hnt⟩
  obtain ⟨m, -, s, hs⟩ :=
    exactFamilyLengthBound Idx (RationalPoint k G.X) (fun J => levi i ν J.1) F hF A bnd hb
      hdetect
  have hA : A.HasFiniteLength := by
    apply Module.length_ne_top_iff.mp
    change repLength A.obj.ρ ≠ ⊤
    rw [repLength_eq_of_hasSimpleFactors s hs]
    exact ENat.natCast_ne_top m
  exact (normalizedInduction_universeLift_hasFiniteLength_iff (h I) (hU I) σ).mp hA

end Langlands.Aubert.General.RationalPointFamily

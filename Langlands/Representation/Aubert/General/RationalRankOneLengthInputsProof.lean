import Langlands.Representation.Aubert.General.RationalRankOneLengthInputsStatement
import Langlands.Representation.Aubert.General.LengthTwoExtraction
import Langlands.Representation.Aubert.General.RationalStandardInductionNonzero
import Langlands.Representation.Aubert.General.RationalUnipotentRegularity
import Langlands.Representation.Aubert.General.AlternatingOperator
import Langlands.Representation.Filtration.ExactFamilyLengthProof

/-! # Rational rank-one length two from detection and Jacquet-length inputs -/

noncomputable section

universe uI uG uV u v

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General

open SmoothRep

section Generic

variable {H : Type uG} [Group H] [TopologicalSpace H] [LocallyCompactSpace H]
  [NonarchimedeanGroup H] {Idx : Type uI} [Fintype Idx] {P M U : Idx → Subgroup H}
  (h : ∀ b, IsSemidirectDecomposition (P b) (M b) (U b))
  (hU : ∀ b, IsClosed (U b : Set H))
  (hUc : ∀ b, Jacquet.Localization.IsLimitOfCompactSubgroups (U b))

include hUc in
/-- A finite family of actual normalized Jacquet functors with compact-limit
radicals, whose image lengths add up to at most two in `ℕ∞` and which detects
every actual irreducible subquotient, bounds the composition length by two. -/
theorem repLength_le_two_of_jacquetFamily (A : SmoothRep.{0, uG, uV} ℂ H)
    (hbudget : (∑ b, repLength ((jacquetFunctor.{uG, uV} (h b) (hU b)).obj A).representation)
      ≤ 2)
    (hdetect : ∀ D : SmoothRep.{0, uG, uV} ℂ H, D.IsIrreducible → IsSubquotient D A →
      ∃ b, Nontrivial ((jacquetFunctor.{uG, uV} (h b) (hU b)).obj D)) :
    repLength A.representation ≤ 2 := by
  classical
  let F : ∀ b, SmoothRep.{0, uG, uV} ℂ H ⥤ SmoothRep.{0, uG, uV} ℂ (M b) :=
    fun b => jacquetFunctor (h b) (hU b)
  have hF : ∀ b, Derivative.Mirabolic.MapsShortExactIntertwiners (F b) := by
    intro b B C D f g hf hg hex
    have hs := jacquetFunctor_map_isShortExact (h b) (hU b) (hUc b) f g ⟨hf, hg, hex⟩
    exact ⟨hs.1, hs.2.2, hs.2.1⟩
  have hfin : ∀ b, repLength ((F b).obj A).representation ≠ ⊤ := by
    intro b
    have hle : repLength ((F b).obj A).representation ≤ 2 :=
      (Finset.single_le_sum (f := fun c => repLength ((F c).obj A).representation)
        (fun c _ => zero_le) (Finset.mem_univ b)).trans hbudget
    exact ne_top_of_le_ne_top (by simp) hle
  let bnd : Idx → ℕ := fun b => (repLength ((F b).obj A).representation).toNat
  have hcast : ∀ b, ((bnd b : ℕ) : ℕ∞) = repLength ((F b).obj A).representation :=
    fun b => ENat.natCast_toNat (hfin b)
  have hb : ∀ b, repLength ((F b).obj A).representation ≤ (bnd b : ℕ∞) :=
    fun b => (hcast b).ge
  have hsum : (∑ b, bnd b) ≤ 2 := by
    have hcastsum : ((∑ b, bnd b : ℕ) : ℕ∞) =
        ∑ b, repLength ((F b).obj A).representation := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun b _ => hcast b)
    have h2 : ((∑ b, bnd b : ℕ) : ℕ∞) ≤ ((2 : ℕ) : ℕ∞) := by
      rw [hcastsum]
      exact hbudget
    exact_mod_cast h2
  obtain ⟨m, hm, s, hs⟩ := exactFamilyLengthBound Idx H (fun b => M b) F hF A bnd hb hdetect
  change repLength A.obj.ρ ≤ 2
  rw [repLength_eq_of_hasSimpleFactors s hs]
  exact_mod_cast hm.trans hsum

end Generic

namespace RationalPointFamily

open GroupScheme
open Langlands.AlgebraicGeometry.PointTopology

/-- The detection and Jacquet-length inputs imply the whole rational rank-one
length-two target, at independent field and carrier universes. -/
theorem rationalRankOneLengthTwoFromInputs :
    RationalRankOneLengthTwoFromInputsStatement.{u, v} := by
  intro hdet hbud k _ _ _ _ G hG T i hi
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  let : TopologicalSpace (RationalPoint k G.X) := pointTopology
  intro _ _ _ ν hν hStandard hInter hRoots hU hM
  let := simpleRelativeRootFintype i hRoots hi.isSplitSubtorus.1 ν
  let : DecidableEq (SimpleRoot i ν) := Classical.decEq _
  intro J hJ σ hσ hcusp hred
  let : σ.val.representation.IsIrreducible := hσ
  have : Nontrivial σ.val :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (levi i ν J)) σ.val.representation.asModule
  have : Nontrivial ((normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
      (hU J)).obj σ.val) :=
    rationalStandardInductionNonzero k G hG T i hi ν hν hStandard J (hU J) σ.val
  have hlen := repLength_le_two_of_jacquetFamily
    (P := fun β : SimpleRoot i ν => parabolic i ν (Finset.univ.erase β))
    (M := fun β : SimpleRoot i ν => levi i ν (Finset.univ.erase β))
    (U := fun β : SimpleRoot i ν => unipotent i ν (Finset.univ.erase β))
    (fun β => isSemidirectDecomposition_of_standardCocharacterStatement
      i ν hStandard hG hi hν (Finset.univ.erase β))
    (fun β => hU (Finset.univ.erase β))
    (fun β => standardUnipotent_isLimitOfCompactSubgroups_of_standardCocharacterStatement
      i ν hStandard hG hi hν (Finset.univ.erase β))
    ((normalizedInductionFunctor.{u, max (u + 1) v}
      (isSemidirectDecomposition_of_standardCocharacterStatement i ν hStandard hG hi hν J)
      (hU J)).obj σ.val)
    (hbud k G hG T i hi ν hν hStandard hInter hRoots hU hM J hJ σ.val hσ hcusp)
    (hdet k G hG T i hi ν hν hStandard hInter hRoots hU hM J hJ σ.val hσ hcusp)
  exact exists_hasTwoConstituents_of_length_le_two _ hlen hred

end RationalPointFamily

end Langlands.Aubert.General

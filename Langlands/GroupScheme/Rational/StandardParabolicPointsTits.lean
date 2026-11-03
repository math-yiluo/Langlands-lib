import Langlands.GroupScheme.Rational.StandardParabolicPointsStatement
import Langlands.GroupScheme.Rational.StandardParabolicEndpointsStatement
import Langlands.GroupScheme.Rational.StandardParabolicOrderStatement
import Langlands.GroupScheme.Rational.NormalizerParabolicPoints
import Langlands.Group.TitsSystemBruhat

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise

namespace Langlands.GroupScheme

open Langlands.Group

/-- Realization data from which, together with the published endpoint and order statements, the
four standard-parabolic clauses follow: a Tits system on `(P_∅(k), N(k), N(k)/Z(k), S)` and the
description of each `W_J` as `⟨X⟩` for some `X ⊆ S` (and conversely). -/
def StandardParabolicTitsRealization : Prop :=
  ∀ (k : Type u) [Field k] (G : GroupScheme (Spec (CommRingCat.of k)))
    (hG : IsConnectedReductive G) (T : CommGroupScheme (Spec (CommRingCat.of k)))
    (i : T.toGrp ⟶ G) (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice T),
    haveI := hG.isAffineHom
    haveI := hi.isSplitSubtorus.mono
    IsGenericCocharacter i ν →
      ∃ S : Set (relativeWeylGroup i),
        IsTitsSystem (standardParabolicPoints i ν ∅) (normalizerPoints i)
          (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))) S ∧
        (∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
          ∃ X ⊆ S, standardRelativeWeylGroup i ν J = Subgroup.closure X) ∧
        (∀ X ⊆ S, ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
          standardRelativeWeylGroup i ν J = Subgroup.closure X)

theorem standardParabolicPointsStatement_of_titsRealization
    (h : StandardParabolicTitsRealization.{u}) (hE : StandardParabolicEndpointsStatement.{u})
    (hO : StandardParabolicOrderStatement.{u}) : StandardParabolicPointsStatement.{u} := by
  intro k _ G hG T i hi ν
  let _ := hG.isAffineHom
  let _ := hi.isSplitSubtorus.mono
  intro hν
  obtain ⟨S, hT, hJX, hXJ⟩ := h k G hG T i hi ν hν
  have hB : (Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i)).carrier
      (Over.mk (𝟙 (Spec (CommRingCat.of k)))) = standardParabolicPoints i ν ∅ := by
    rw [standardParabolicPoints, (hE k G hG T i hi ν hν).1]
  have hBP : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      standardParabolicPoints i ν ∅ ≤ standardParabolicPoints i ν J := fun J hJ =>
    SubgroupFunctor.le_def.1
      (((hO k G hG T i hi ν hν).1 ∅ J (Set.empty_subset _) hJ).1.1 (Set.empty_subset J)) _
  rw [hB]
  -- `P_J(k) = B ⟨X⟩ B` whenever `W_J = ⟨X⟩`
  have hPJ : ∀ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν →
      ∀ X : Set (relativeWeylGroup i), standardRelativeWeylGroup i ν J = Subgroup.closure X →
        ((standardParabolicPoints i ν J : Subgroup _) : Set _) =
          TitsSystem.standardParabolic (standardParabolicPoints i ν ∅)
            (QuotientGroup.mk' ((centralizerPoints i).subgroupOf (normalizerPoints i))) X := by
    intro J hJ X hX
    refine hT.coe_eq_standardParabolic (hBP J hJ) (fun n hn => hX ▸ hi.isSplitSubtorus.mk_mem_standardRelativeWeylGroup ν J hn) ?_
    intro v hv
    rw [← hX] at hv
    obtain ⟨n, hn, rfl⟩ := hv
    exact ⟨n, rfl, standardLevi_le_standardParabolic i ν J _ hn⟩
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro J hJ g
    have hcoe := hPJ J hJ (standardRelativeWeylGroup i ν J)
      (Subgroup.closure_eq _).symm
    rw [← SetLike.mem_coe, hcoe]
    constructor
    · rintro ⟨w, hw, n, rfl, b, hb, b', hb', rfl⟩
      rw [Subgroup.closure_eq] at hw
      exact ⟨n, hw, b, hb, b', hb', rfl⟩
    · rintro ⟨n, hn, p, hp, q, hq, rfl⟩
      exact ⟨_, Subgroup.subset_closure hn, n, rfl, p, hp, q, hq, rfl⟩
  · intro H
    constructor
    · intro hH
      obtain ⟨X, hXS, hX⟩ := hT.exists_eq_standardParabolic H hH
      obtain ⟨J, hJ, hJX'⟩ := hXJ X hXS
      exact ⟨J, hJ, SetLike.coe_injective (hX.trans (hPJ J hJ X hJX').symm)⟩
    · rintro ⟨J, hJ, rfl⟩
      exact hBP J hJ
  · intro J hJ
    exact hT.normalizer_eq_of_le (hBP J hJ)
  · intro J K hJ hK
    obtain ⟨X, hXS, hX⟩ := hJX J hJ
    obtain ⟨Y, hYS, hY⟩ := hJX K hK
    obtain ⟨e, he⟩ := hT.exists_doubleCoset_equiv hXS hYS hX hY (hPJ J hJ X hX) (hPJ K hK Y hY)
    exact ⟨e, he⟩

end Langlands.GroupScheme

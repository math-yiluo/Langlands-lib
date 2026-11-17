import Langlands.GroupScheme.RelativeUnipotent.RootWeightKernel
import Langlands.GroupScheme.RelativeUnipotent.FreeVectorBundle
import Langlands.GroupScheme.RelativeUnipotent.FiltrationTermination

/-! # Finite vector-bundle series from nonnegative root weights -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootWeightData

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} {C : RootHeightChart U}
    (W : RootWeightData C)

/-- A represented positive-weight term above every root weight is trivial on all tests. -/
theorem range_id_eq_bot {d : ℕ} (hd : ∀ k, W.weight k < d + 1) :
    SubgroupFunctor.range (𝟙 (W.groupScheme d)) = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro _
    have hx : x ≫ (W.inclusion d).hom.hom ∈ (W.subgroup d).carrier T :=
      (W.isRepresentedBy_inclusion d).pointsEquiv T x |>.property
    rw [W.subgroup_eq_bot hd, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    have he : (W.isRepresentedBy_inclusion d).pointsEquiv T x = 1 := Subtype.ext hx
    exact ((W.isRepresentedBy_inclusion d).pointsEquiv T).injective
      (he.trans ((W.isRepresentedBy_inclusion d).pointsEquiv T).map_one.symm)
  · rintro rfl
    exact Subgroup.one_mem _

/-- Every supplied weight bound gives a series with that exact length. -/
theorem hasVectorBundleSeries_of_bound (n : ℕ) (hn : ∀ k, W.weight k < n + 1) :
    HasVectorBundleSeries n (W.groupScheme 0) := by
  have hterm : SubgroupFunctor.range (𝟙 (W.groupScheme (0 + n))) = ⊥ :=
    W.range_id_eq_bot (by simpa only [Nat.zero_add] using hn)
  apply hasVectorBundleSeries_of_segment
    (fun k => W.groupScheme k) (fun k => W.step k)
    (fun k => ?_) n 0 hterm
  exact ⟨VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (W.exactSupport k)),
    W.quotientMap k, W.isClosedSubgroup_step k, W.smooth_groupScheme (k + 1),
    W.isNormal_range_step k, W.isFppfQuotient_quotientMap k,
    isVectorBundleAdditive_vectorGroup _ _⟩

/-- The largest weight, with value zero when the root family is empty. -/
def weightBound : ℕ := Finset.univ.sup W.weight

theorem weight_le_weightBound (k : Fin C.dimension) : W.weight k ≤ W.weightBound :=
  Finset.le_sup (Finset.mem_univ k)

include W in
/-- A supplied positive-weight subgroup has a finite vector-bundle series. -/
theorem hasFiniteVectorBundleSeries : HasFiniteVectorBundleSeries (W.groupScheme 0) :=
  ⟨W.weightBound, W.hasVectorBundleSeries_of_bound W.weightBound
    (fun k => Nat.lt_succ_of_le (W.weight_le_weightBound k))⟩

/-- A chosen finite length together with its series proof. -/
def seriesWitness : {n : ℕ // HasVectorBundleSeries n (W.groupScheme 0)} :=
  ⟨W.weightBound, W.hasVectorBundleSeries_of_bound W.weightBound
    (fun k => Nat.lt_succ_of_le (W.weight_le_weightBound k))⟩

end Langlands.GroupScheme.RelativeUnipotent.RootWeightData

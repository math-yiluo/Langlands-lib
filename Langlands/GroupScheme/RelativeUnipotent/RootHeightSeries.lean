import Langlands.GroupScheme.RelativeUnipotent.RootHeightKernel
import Langlands.GroupScheme.RelativeUnipotent.FreeVectorBundle
import Langlands.GroupScheme.RelativeUnipotent.SeriesTransport
import Langlands.GroupScheme.RelativeUnipotent.FiltrationTermination

/-! # Finite vector-bundle series from positive root-height charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Classical
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

variable {R : Type u} [CommRing R]
    {U : GroupScheme (Spec (CommRingCat.of R))} (C : RootHeightChart U)

/-- A represented height term above every root height is trivial on all tests. -/
theorem range_id_eq_bot {d : ℕ} (hd : ∀ k, C.height k < d) :
    SubgroupFunctor.range (𝟙 (C.groupScheme d)) = ⊥ := by
  apply SubgroupFunctor.ext
  intro T
  apply Subgroup.ext
  intro x
  rw [SubgroupFunctor.bot_carrier, Subgroup.mem_bot]
  constructor
  · intro _
    have hx : x ≫ (C.inclusion d).hom.hom ∈ (C.subgroup d).carrier T :=
      (C.isRepresentedBy_inclusion d).pointsEquiv T x |>.property
    rw [C.subgroup_eq_bot hd, SubgroupFunctor.bot_carrier, Subgroup.mem_bot] at hx
    have he : (C.isRepresentedBy_inclusion d).pointsEquiv T x = 1 := Subtype.ext hx
    exact ((C.isRepresentedBy_inclusion d).pointsEquiv T).injective
      (he.trans ((C.isRepresentedBy_inclusion d).pointsEquiv T).map_one.symm)
  · rintro rfl
    exact Subgroup.one_mem _

/-- The identity of the original group represents its height-one subgroup. -/
theorem subgroup_one_isRepresentedBy_id :
    (C.subgroup 1).IsRepresentedBy (𝟙 U) := by
  refine ⟨inferInstance, ?_⟩
  rw [C.subgroup_one]
  apply SubgroupFunctor.ext
  intro T
  apply top_unique
  intro x _
  exact SubgroupFunctor.mem_range.mpr ⟨x, Category.comp_id x⟩

/-- The first height term is the actual original group, as a group scheme. -/
def heightOneIso : C.groupScheme 1 ≅ U :=
  (C.isRepresentedBy_inclusion 1).isoOfIsRepresentedBy C.subgroup_one_isRepresentedBy_id

/-- Every supplied height bound gives a series with that exact length. -/
theorem hasVectorBundleSeries_of_bound (n : ℕ) (hn : ∀ k, C.height k < n + 1) :
    HasVectorBundleSeries n U := by
  have hterm : SubgroupFunctor.range (𝟙 (C.groupScheme (0 + n + 1))) = ⊥ :=
    C.range_id_eq_bot (by simpa only [Nat.zero_add] using hn)
  have hseries : HasVectorBundleSeries n (C.groupScheme (0 + 1)) := by
    apply hasVectorBundleSeries_of_segment
      (fun k => C.groupScheme (k + 1)) (fun k => C.step (k + 1))
      (fun k => ?_) n 0 hterm
    exact ⟨VectorGroup.groupScheme (CommRingCat.of R) (Nat.card (C.exactSupport (k + 1))),
      C.quotientMap (k + 1) (Nat.zero_lt_succ k),
      C.isClosedSubgroup_step (k + 1), C.smooth_groupScheme (k + 1 + 1),
      C.isNormal_range_step (k + 1),
      C.isFppfQuotient_quotientMap (k + 1) (Nat.zero_lt_succ k),
      isVectorBundleAdditive_vectorGroup _ _⟩
  exact hseries.of_iso C.heightOneIso

/-- The largest height, with value zero when the root family is empty. -/
def heightBound : ℕ := Finset.univ.sup C.height

theorem height_le_heightBound (k : Fin C.dimension) : C.height k ≤ C.heightBound :=
  Finset.le_sup (Finset.mem_univ k)

include C in
/-- A supplied positive root-height chart has a finite vector-bundle series. -/
theorem hasFiniteVectorBundleSeries : HasFiniteVectorBundleSeries U :=
  ⟨C.heightBound, C.hasVectorBundleSeries_of_bound C.heightBound
    (fun k => Nat.lt_succ_of_le (C.height_le_heightBound k))⟩

/-- A chosen finite length together with its series proof. -/
def seriesWitness : {n : ℕ // HasVectorBundleSeries n U} :=
  ⟨C.heightBound, C.hasVectorBundleSeries_of_bound C.heightBound
    (fun k => Nat.lt_succ_of_le (C.height_le_heightBound k))⟩

end Langlands.GroupScheme.RelativeUnipotent.RootHeightChart

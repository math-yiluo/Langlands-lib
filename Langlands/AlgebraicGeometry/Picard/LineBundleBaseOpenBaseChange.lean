import Langlands.AlgebraicGeometry.Modules.RankOneCartesianBaseChange
import Mathlib.AlgebraicGeometry.PullbackCarrier

/-! # The base open classifying line-bundle base changes -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.Picard

variable {P Y T S : Scheme.{u}} {a : P ⟶ Y} {p : P ⟶ T}
  {f : Y ⟶ S} {g : T ⟶ S}

/-- A cartesian pullback is a line bundle exactly when the base morphism has
image in the full-fibre rank-one base open. -/
lemma isLocallyFreeRankOne_pullback_iff_mem_baseOpen (H : IsPullback a p f g)
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M) :
    IsLocallyFreeRankOne ((Scheme.Modules.pullback a).obj M) ↔
      ∀ t : T, g t ∈ rankOneBaseOpen f M := by
  constructor
  · intro h t
    apply (mem_rankOneBaseOpen f M (g t)).mpr
    intro y hy
    obtain ⟨x, hax, hpx⟩ := Scheme.exists_preimage_of_isPullback H y t hy
    have hx : x ∈ rankOneLocus ((Scheme.Modules.pullback a).obj M) :=
      (mem_rankOneLocus _ x).mpr (h x)
    rw [Modules.rankOneLocus_pullback_of_isPullback H M hM] at hx
    change a x ∈ rankOneLocus M at hx
    simpa only [hax] using hx
  · exact isLocallyFreeRankOne_pullback_over_baseOpen f M p a g H.w.symm

/-- Formation of the full-fibre rank-one base open commutes with arbitrary
cartesian base change. -/
lemma rankOneBaseOpen_pullback_of_isPullback (H : IsPullback a p f g)
    [UniversallyClosed f] [UniversallyClosed p] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M) :
    rankOneBaseOpen p ((Scheme.Modules.pullback a).obj M) =
      g ⁻¹ᵁ rankOneBaseOpen f M := by
  apply TopologicalSpace.Opens.ext
  change (p '' (rankOneLocus ((Scheme.Modules.pullback a).obj M) : Set P)ᶜ)ᶜ =
    g ⁻¹' (f '' (rankOneLocus M : Set Y)ᶜ)ᶜ
  rw [Modules.rankOneLocus_pullback_of_isPullback H M hM]
  change (p.base '' (a.base ⁻¹' (rankOneLocus M : Set Y))ᶜ)ᶜ = _
  rw [← Set.preimage_compl, Scheme.image_preimage_eq_of_isPullback H]
  rfl

/-- The actual morphism to the classifying base open induced by a line-bundle
cartesian pullback. -/
def rankOneBaseOpenLift (H : IsPullback a p f g)
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M)
    (h : IsLocallyFreeRankOne ((Scheme.Modules.pullback a).obj M)) :
    T ⟶ (rankOneBaseOpen f M).toScheme :=
  IsOpenImmersion.lift (rankOneBaseOpen f M).ι g (by
    rw [Scheme.Opens.range_ι]
    rintro _ ⟨t, rfl⟩
    exact (isLocallyFreeRankOne_pullback_iff_mem_baseOpen H M hM).mp h t)

@[reassoc (attr := simp)]
lemma rankOneBaseOpenLift_fac (H : IsPullback a p f g)
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M)
    (h : IsLocallyFreeRankOne ((Scheme.Modules.pullback a).obj M)) :
    rankOneBaseOpenLift H M hM h ≫ (rankOneBaseOpen f M).ι = g :=
  IsOpenImmersion.lift_fac _ _ _

/-- The factorization through the classifying open is unique. -/
lemma rankOneBaseOpenLift_uniq (H : IsPullback a p f g)
    [UniversallyClosed f] [LocallyOfFinitePresentation f]
    (M : Y.Modules) [M.IsFinitePresentation] (hM : Modules.IsFlatOver f M)
    (h : IsLocallyFreeRankOne ((Scheme.Modules.pullback a).obj M))
    (l : T ⟶ (rankOneBaseOpen f M).toScheme)
    (hl : l ≫ (rankOneBaseOpen f M).ι = g) :
    l = rankOneBaseOpenLift H M hM h := by
  rw [← cancel_mono (rankOneBaseOpen f M).ι, hl, rankOneBaseOpenLift_fac]

end Langlands.AlgebraicGeometry.Picard

import Langlands.Geometry.Analytic.EquivariantSitePullbacksReduction
import Langlands.Geometry.Analytic.EtalePointwiseLifting.LocalizedStability
import Langlands.Geometry.Analytic.LocalizedEtalePullbackPoints
import Langlands.Geometry.Analytic.LocalizedEtalePullbackProof
import Langlands.Geometry.Analytic.RestrictionSiteMorphismReduction

/-! # The actual equivariant étale pretopology -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation

open _root_.CategoryTheory _root_.CategoryTheory.Limits

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] {X : GSpace.{u, v, v} K G}

namespace EquivariantEtaleSite

/-- Every arrow in the equivariant étale site is itself étale on underlying spaces. -/
theorem etale_map_left {U V : EquivariantEtaleSite X} (f : U ⟶ V) :
    etale (GSpace.forget.map f.left) := by
  let := (localizedEtaleStability (K := K)).2
  apply (etale (K := K)).of_postcomp (GSpace.forget.map f.left) (GSpace.forget.map V.hom) V.prop
  rw [← GSpace.forget.map_comp, MorphismProperty.Over.w]
  exact U.prop

/-- Cospans in the equivariant étale site have pullbacks computed on the underlying spaces. -/
theorem exists_analyticPullback {U V W : EquivariantEtaleSite X} (f : U ⟶ W) (g : V ⟶ W) :
    ∃ (P : EquivariantEtaleSite X) (p : P ⟶ U) (q : P ⟶ V),
      IsPullback (GSpace.forget.map p.left) (GSpace.forget.map q.left)
        (GSpace.forget.map f.left) (GSpace.forget.map g.left) := by
  obtain ⟨P, p, q, hP, hq⟩ := localizedEtalePullbackBaseChange (K := K)
    (GSpace.forget.map f.left) (GSpace.forget.map g.left) (etale_map_left f)
  exact exists_equivariantSitePullback_of_isPullback f g hP
    (etale_le_quasiEtale _ (etale_map_left f)) (etale_comp hq V.prop)

instance hasPullbacks : HasPullbacks (EquivariantEtaleSite X) :=
  GSpace.hasPullbacks_of_isPullback_forget (fun _ _ _ f g => exists_analyticPullback f g)

/-- The pullback property in the equivariant étale site implies the analytic
pullback property for its underlying square. -/
theorem isPullback_forget {P U V W : EquivariantEtaleSite X}
    {p : P ⟶ U} {q : P ⟶ V} {f : U ⟶ W} {g : V ⟶ W} (h : IsPullback p q f g) :
    IsPullback (GSpace.forget.map p.left) (GSpace.forget.map q.left)
      (GSpace.forget.map f.left) (GSpace.forget.map g.left) := by
  let F := MorphismProperty.Over.forget GSpace.etale ⊤ X ⋙ Over.forget X ⋙ GSpace.forget
  obtain ⟨Q, p', q', hQ⟩ := exists_analyticPullback f g
  have hQ' : IsPullback p' q' f g := GSpace.isPullback_of_isPullback_forget hQ
  have hF : IsPullback (F.map p') (F.map q') (F.map f) (F.map g) := hQ
  let : PreservesLimit (cospan f g) F :=
    preservesLimit_of_preserves_limit_cone hQ'.isLimit
      ((isLimitMapConePullbackConeEquiv F hQ'.w).symm hF.isLimit)
  exact h.map F

end EquivariantEtaleSite

instance equivariantEtalePrecoverage_isStableUnderBaseChange (X : GSpace.{u, v, v} K G) :
    (equivariantEtalePrecoverage X).IsStableUnderBaseChange where
  mem_coverings_of_isPullback {ι} S U f hf V g P p q hp := by
    rw [ofArrows_mem_equivariantEtalePrecoverage_iff] at hf ⊢
    intro x
    obtain ⟨i, y, hy⟩ := hf ((EquivariantEtaleSite.points X).map g x)
    obtain ⟨z, -, hz⟩ := exists_point_of_isPullback_of_etale
      (EquivariantEtaleSite.isPullback_forget (hp i)).flip
      (EquivariantEtaleSite.etale_map_left (f i)) y x hy
    exact ⟨i, z, hz⟩

/-- Jointly surjective equivariant families form a pretopology. -/
def equivariantEtalePretopology (X : GSpace.{u, v, v} K G) : Pretopology (EquivariantEtaleSite X) :=
  (equivariantEtalePrecoverage X).toPretopology

/-- The verified equivariant étale pretopology generates the existing site topology. -/
theorem equivariantEtalePretopology_toGrothendieck (X : GSpace.{u, v, v} K G) :
    (equivariantEtalePretopology X).toGrothendieck = equivariantEtaleTopology X :=
  (equivariantEtalePrecoverage X).toGrothendieck_toPretopology_eq_toGrothendieck

end Langlands.Analytic.SaturatedAtlasPresentation

import Langlands.Geometry.Analytic.CompactProbeQuasiEtaleHausdorffComparisonProof
import Langlands.Geometry.Analytic.EquivariantCompactProbeTopology
import Langlands.Geometry.Analytic.InducedQuasiEtaleProof
import Langlands.Geometry.Analytic.InducedSiteEquivalenceProof
import Langlands.Geometry.Analytic.InducedSpaceContinuityProof
import Mathlib.CategoryTheory.Sites.Equivalence

/-! # Open-subgroup induction on equivariant compact-probe sites -/

noncomputable section

universe u v z

namespace Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

open _root_.CategoryTheory

private theorem pushforward_pullback_iso {C D : Type*} [Category* C] [Category* D]
    (F : C ⥤ D) {U V : C} (e : U ≅ V) (S : Sieve V) :
    (S.pullback e.hom).functorPushforward F =
      (S.functorPushforward F).pullback (F.map e.hom) := by
  refine le_antisymm (Sieve.functorPushforward_pullback_le F e.hom S) ?_
  rintro W f ⟨A, a, b, ha, hab⟩
  refine ⟨A, a ≫ e.inv, b, ?_, ?_⟩
  · change S ((a ≫ e.inv) ≫ e.hom)
    simpa using ha
  · change f ≫ F.map e.hom = b ≫ F.map a at hab
    calc
      f = (f ≫ F.map e.hom) ≫ F.map e.inv := by
        rw [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id,
          Category.comp_id]
      _ = (b ≫ F.map a) ≫ F.map e.inv := by rw [hab]
      _ = b ≫ F.map (a ≫ e.inv) := by rw [Functor.map_comp, Category.assoc]

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {H : Subgroup G}
  (hH : IsOpen (H : Set G)) (X : GSpace.{u, max z v, max z v} K H)

/-- Induction along an open subgroup, using the continuity theorem for induced actions. -/
abbrev inducedGSpace : GSpace.{u, max z v, max z v} K G :=
  (gSpaceInduction hH (continuityStatement.{u, v, z})).obj X

/-- Induction on quasi-étale objects, with continuity and preservation of the
quasi-étale property supplied by the induction theorems. -/
abbrev compactProbeSiteInduction :
    EquivariantQuasiEtaleSite X ⥤ EquivariantQuasiEtaleSite (inducedGSpace hH X) :=
  quasiEtaleSiteInduction hH (continuityStatement.{u, v, z})
    (inductionFunctor_map_quasiEtale_etale.{u, v, z}) X

instance compactProbeSiteInduction_isEquivalence : (compactProbeSiteInduction hH X).IsEquivalence :=
  (quasiEtaleSiteEquivalenceStatement.{u, v, z}
    K G H hH continuityStatement inductionFunctor_map_quasiEtale_etale X).1

/-- Induction is an equivalence of equivariant quasi-étale over-categories. -/
def compactProbeSiteInductionEquivalence :
    EquivariantQuasiEtaleSite X ≌ EquivariantQuasiEtaleSite (inducedGSpace hH X) :=
  (compactProbeSiteInduction hH X).asEquivalence

/-- The generating compact-probe coverings are preserved and reflected by induction. -/
theorem map_compactProbeSiteInduction_mem_iff {U : EquivariantQuasiEtaleSite X} (R : Presieve U) :
    R.map (compactProbeSiteInduction hH X) ∈
      equivariantCompactProbeQuasiEtalePrecoverage (inducedGSpace hH X)
        ((compactProbeSiteInduction hH X).obj U) ↔
      R ∈ equivariantCompactProbeQuasiEtalePrecoverage X U := by
  simp only [equivariantCompactProbeQuasiEtalePrecoverage_eq_of_comparison
    (compactProbeQuasiEtaleHausdorffComparison K)]
  exact map_quasiEtaleSiteInduction_mem_iff hH continuityStatement
    inductionFunctor_map_quasiEtale_etale X U R

/-- The induced equivalence preserves and reflects covering sieves of the compact-probe
topology. The inverse transports covers using the counit isomorphism. -/
instance compactProbeSiteInduction_isDenseSubsite :
    (compactProbeSiteInduction hH X).IsDenseSubsite (equivariantCompactProbeQuasiEtaleTopology X)
      (equivariantCompactProbeQuasiEtaleTopology (inducedGSpace hH X)) where
  functorPushforward_mem_iff {U S} := by
    let E := compactProbeSiteInductionEquivalence hH X
    let X' := inducedGSpace hH X
    let J := equivariantCompactProbeQuasiEtaleTopology X
    let J' := equivariantCompactProbeQuasiEtaleTopology X'
    have hForward : J ≤ E.functor.restrictedTopology J' := by
      apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
      intro V R hR
      apply E.functor.mem_restrictedTopology_of_functorPushforward_mem
      rw [← Sieve.generate_map_eq_functorPushforward]
      exact Precoverage.generate_mem_toGrothendieck ((map_compactProbeSiteInduction_mem_iff hH X R).mpr hR)
    have hInverse : J' ≤ E.inverse.restrictedTopology J := by
      apply Precoverage.toGrothendieck_le_iff_le_toPrecoverage.mpr
      intro V R hR
      apply E.inverse.mem_restrictedTopology_of_functorPushforward_mem
      let T := Sieve.generate R
      let A := T.functorPushforward E.inverse
      have hT := mem_equivariantCompactProbeQuasiEtalePrecoverage_iff.mp hR
      rw [Sieve.generate_map_eq_functorPushforward] at hT
      have hA : A.arrows.map E.functor ∈
          equivariantCompactProbeQuasiEtalePrecoverage X' (E.functor.obj (E.inverse.obj V)) := by
        rw [mem_equivariantCompactProbeQuasiEtalePrecoverage_iff]
        simp only [Sieve.generate_map_eq_functorPushforward, Sieve.generate_sieve]
        have hCounit : A.functorPushforward E.functor = T.pullback (E.counit.app V) :=
          Sieve.functorPushforward_equivalence_eq_pullback E.symm T
        let F := EquivariantQuasiEtaleSite.toQuasiEtaleSite X'
        have hPullback : (T.pullback (E.counit.app V)).functorPushforward F =
            (T.functorPushforward F).pullback (F.map (E.counit.app V)) :=
          pushforward_pullback_iso F (E.counitIso.app V) T
        rw [hCounit, hPullback]
        exact (compactProbeQuasiEtaleTopology (GSpace.forget.obj X')).pullback_stable _ hT
      have hCover := Precoverage.generate_mem_toGrothendieck
        ((map_compactProbeSiteInduction_mem_iff hH X A.arrows).mp hA)
      change Sieve.generate A.arrows ∈ J (E.inverse.obj V) at hCover
      rw [Sieve.generate_sieve] at hCover
      exact hCover
    change S.functorPushforward E.functor ∈ J' _ ↔ S ∈ J U
    constructor
    · intro hS
      have hA := (E.inverse.mem_restrictedTopology_iff).mp (hInverse _ hS)
      have h := J.pullback_stable (E.unit.app U) hA
      rw [Sieve.pullback_functorPushforward_equivalence_eq] at h
      exact h
    · intro hS
      exact (E.functor.mem_restrictedTopology_iff).mp (hForward _ hS)

end Langlands.Analytic.SaturatedAtlasPresentation.InducedSpace

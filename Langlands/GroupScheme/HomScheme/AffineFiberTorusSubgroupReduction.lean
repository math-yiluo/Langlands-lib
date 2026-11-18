import Langlands.GroupScheme.Descent.FiniteCoefficientAffineFiberGroup
import Langlands.GroupScheme.HomScheme.ChartCoverBaseChange
import Langlands.GroupScheme.HomScheme.ChartCoverOpenExtension
import Langlands.GroupScheme.HomScheme.SmoothAffineFiberTorusSubgroupRepresentabilityStatement
import Langlands.GroupScheme.HomScheme.TorusSubgroupChartGluingProof

/-! # Reduction of affine-fibre torus-subgroup moduli to noetherian affine bases -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
open Langlands.GroupScheme.Descent.FiniteCoefficient

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.GroupScheme.TorusSubgroupModuli

variable {S : Scheme.{u}} {G : GroupScheme S}

/-- The noetherian affine specialization of smooth torus-subgroup representability
for smooth separated quasi-compact groups with affine residue fibres. -/
def NoetherianAffineTorusSubgroupRepresentabilityStatement : Prop :=
  ∀ (A : Type u) [CommRing A] [IsNoetherianRing A]
    (G : GroupScheme (Spec (CommRingCat.of A)))
    [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
    (∀ s : Spec (CommRingCat.of A),
      IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
    ∃ (M : Over (Spec (CommRingCat.of A))) (K : GroupScheme M.left)
      (j : K ⟶ (baseChange M.hom).obj G),
      IsClosedSubgroup j ∧ RelativeTorus.IsTorus K ∧ IsUniversal j ∧ Smooth M.hom

/-- A smooth universal family is a one-member open chart cover. -/
theorem IsUniversal.hasChartCover {M : Over S} {K : GroupScheme M.left}
    {j : K ⟶ (baseChange M.hom).obj G} (hu : IsUniversal j)
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K) (hs : Smooth M.hom) :
    HasChartCover G := by
  refine ⟨PUnit, fun _ => M, fun _ => K, fun _ => j, fun _ => ⟨hj, hK, hs, ?_, ?_⟩, ?_⟩
  · intro T a b hab
    obtain ⟨c, _, hc⟩ := hu T _ (isAdmissible_evaluate j hj hK a)
    exact (hc a rfl).trans (hc b hab.symm).symm
  · intro T L i hi hL
    refine ⟨⊤, fun T' b => ⟨fun _ => Set.subset_univ _, fun _ => ?_⟩⟩
    obtain ⟨a, ha, _⟩ := hu T' _ (isAdmissible_evaluate i hi hL b)
    exact ⟨a, ha⟩
  · intro k _ x L i hi hL
    obtain ⟨a, ha, _⟩ := hu (Over.mk x) _ (isAdmissible_range i hi hL)
    exact ⟨PUnit.unit, a, ha⟩

/-- Chart covers over all affine bases imply a smooth universal family over
an arbitrary base. -/
theorem smoothAffineFiberTorusSubgroupRepresentability_of_spec
    (h : ∀ (R : CommRingCat.{u}) (G : GroupScheme (Spec R))
      [Smooth G.X.hom] [IsSeparated G.X.hom] [QuasiCompact G.X.hom],
      (∀ s : Spec R, IsAffineHom (RelativeIdentityComponent.residueFiber G s).X.hom) →
      HasChartCover G) :
    SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u} := by
  intro S G _ _ _ hG
  have hLocus : affineFiberLocus G.X.hom = Set.univ := Set.eq_univ_of_forall hG
  have hc : HasChartCover G := by
    refine hasChartCover_of_openCover (J := S.affineOpens) (fun V => V.2.fromSpec) ?_ ?_
    · intro s
      obtain ⟨_, ⟨V, hV, rfl⟩, hsV, _⟩ :=
        S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ s) isOpen_univ
      exact ⟨⟨V, hV⟩, by simpa only [IsAffineOpen.range_fromSpec] using hsV⟩
    · intro V
      let p := V.2.fromSpec
      let G' := (baseChange p).obj G
      let : Smooth G'.X.hom := by
        change Smooth (pullback.snd G.X.hom p)
        infer_instance
      let : IsSeparated G'.X.hom := by
        change IsSeparated (pullback.snd G.X.hom p)
        infer_instance
      let : QuasiCompact G'.X.hom := by
        change QuasiCompact (pullback.snd G.X.hom p)
        infer_instance
      have hLocus' : affineFiberLocus G'.X.hom = Set.univ := by
        change affineFiberLocus (pullback.snd G.X.hom p) = Set.univ
        rw [affineFiberLocus_baseChange (IsPullback.of_hasPullback _ _), hLocus, Set.preimage_univ]
      exact h _ G' (Set.eq_univ_iff_forall.mp hLocus')
  obtain ⟨I, U, K, j, hj, hcov⟩ := hc
  exact OpenCharts.exists_smooth_universal j hj (hasEffectiveAdmissibleDescent G) hcov

/-- Smooth representability over noetherian affine bases suffices for the
unchanged arbitrary-base affine-fibre statement. -/
theorem smoothAffineFiberTorusSubgroupRepresentability_of_noetherianAffine
    (h : NoetherianAffineTorusSubgroupRepresentabilityStatement.{u}) :
    SmoothAffineFiberTorusSubgroupRepresentabilityStatement.{u} := by
  apply smoothAffineFiberTorusSubgroupRepresentability_of_spec
  intro A G _ _ _ hG
  let R := (⊥ : Subalgebra ℤ A)
  let : Algebra.FiniteType ℤ R := (Subalgebra.fg_iff_finiteType R).mp Subalgebra.fg_bot
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing ℤ R
  have hLocus : affineFiberLocus G.X.hom = Set.univ := Set.eq_univ_of_forall hG
  obtain ⟨D⟩ := exists_smoothAffineFiberGroupModel R A G hLocus
  let : IsNoetherianRing D.coefficients := SmoothAffineFiberGroupModel.isNoetherianRing R A D
  let : Smooth D.group.X.hom := D.smooth
  let : IsSeparated D.group.X.hom := D.separated
  let : QuasiCompact D.group.X.hom := D.quasiCompact
  obtain ⟨M, K, j, hj, hK, hu, hs⟩ := h D.coefficients D.group
    (Set.eq_univ_iff_forall.mp D.affineFibres)
  exact hasChartCover_iso D.iso.symm
    (hasChartCover_baseChange (Spec.algebraMap D.coefficients A) (hu.hasChartCover hj hK hs))

end Langlands.GroupScheme.TorusSubgroupModuli

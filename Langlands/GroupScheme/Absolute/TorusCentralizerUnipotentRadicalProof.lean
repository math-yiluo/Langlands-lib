import Langlands.GroupScheme.Absolute.TorusCentralizerUnipotentRadicalStatement
import Langlands.GroupScheme.Absolute.CentralizerUnipotentBorelContainmentProof
import Langlands.GroupScheme.Absolute.ChevalleyUnipotentEnvelopeProof
import Langlands.GroupScheme.Reductive.NormalUnipotentCentralizer
import Langlands.GroupScheme.Rational.MaximalTorusFiniteType
import Langlands.GroupScheme.Torus.SplitReflection
import Langlands.GroupScheme.Torus.FiniteGaloisSplittingProof
import Langlands.GroupScheme.Torus.CentralizerConnected

/-! # The unipotent radical of a torus centralizer -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

/-- The radical of a torus centralizer is its intersection with the ambient radical,
as subgroup functors on every test scheme. -/
theorem torusCentralizerUnipotentRadical : TorusCentralizerUnipotentRadicalStatement.{u} := by
  intro k _ _ G _ _ _ S s hS hs C c hc hcc U u hu V v hv
  let : IsAffineHom C.X.hom := hcc.isAffineHom
  let : Smooth C.X.hom := torusCentralizerSmooth k G S s hS hs C c hc hcc
  let : ConnectedSpace C.X.left := hS.connectedSpace_centralizer s hc
  let : IsAffineHom U.X.hom := hu.isClosedSubgroup.isAffineHom
  let : Smooth U.X.hom := hu.smooth
  let : ConnectedSpace U.X.left := hu.connectedSpace
  let : Mono u.hom.hom := by
    have : IsClosedImmersion u.hom.hom.left := hu.isClosedSubgroup
    exact Over.mono_of_mono_left _
  have hsplit : IsSplitTorus S.toGrp :=
    hS.isSplitTorus_of_finiteGaloisSplitting torusFiniteGaloisSplitting
  obtain ⟨ν, hν⟩ := hsplit.exists_cocharacter_centralizer s
  let χ := CommGroupScheme.groupHom ν ≫ s
  have hcχ : (Dynamic.centralizer χ).IsRepresentedBy c := by
    rw [show Dynamic.centralizer χ = torusCentralizer s from hν]
    exact hc
  have hforward : SubgroupFunctor.range (v ≫ c) ≤ SubgroupFunctor.range u := by
    obtain ⟨M, m, hm, f, hf⟩ :=
      exists_maximalTorus_extension_of_finiteType G s hS hs
    have hvm : IsClosedSubgroup (v ≫ c) := hv.isClosedSubgroup.comp hcc
    have hB : ∀ (B : GroupScheme (Spec (CommRingCat.of k))) (b : B ⟶ G),
        IsBorelSubgroup b → SubgroupFunctor.range m ≤ SubgroupFunctor.range b →
          SubgroupFunctor.range (v ≫ c) ≤ SubgroupFunctor.range b := by
      intro B b hb hmb
      apply centralizerUnipotentBorelContainment k G χ C c hcc hcχ
        inferInstance inferInstance V v hv.isClosedSubgroup hv.smooth hv.connectedSpace
        hv.isUnipotent hv.isNormal B b hb
      intro T x hx
      obtain ⟨t, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      apply hmb T
      refine SubgroupFunctor.mem_range.mpr ⟨t ≫
        (CommGroupScheme.groupHom ν ≫ f).hom.hom, ?_⟩
      simp only [χ, Grp.comp_hom_hom, Category.assoc, ← hf]
    obtain ⟨N, n, hn, hns, hnc, hnu, hnn, hle⟩ :=
      chevalleyUnipotentEnvelope k G M m hm V (v ≫ c) hvm hv.smooth
        hv.connectedSpace hv.isUnipotent hB
    exact hle.trans (hu.greatest N n hn hns hnc hnu hnn)
  have hnχ : (SubgroupFunctor.range u).IsNormalizedBy (SubgroupFunctor.range χ) :=
    fun T g x _ hx => hu.isNormal T g x (Subgroup.mem_top _) hx
  have hnC : (SubgroupFunctor.range u).IsNormalizedBy (SubgroupFunctor.range c) :=
    fun T g x _ hx => hu.isNormal T g x (Subgroup.mem_top _) hx
  have hinter : SubgroupFunctor.range (subgroupIntersectionSnd u c) ≤
      SubgroupFunctor.range v :=
    hv.greatest (subgroupIntersection u c) (subgroupIntersectionSnd u c)
      (Dynamic.isClosedSubgroup_intersectionSnd u c hu.isClosedSubgroup)
      (Dynamic.subgroupIntersection_smooth χ u c hcχ hcc hnχ hu.smooth inferInstance)
      (connectedSpace_normalUnipotentCentralizer χ u c hu.isClosedSubgroup
        hcχ hcc hu.isNormal hu.isUnipotent)
      (unipotentClosedSubgroup k U (subgroupIntersection u c)
        (subgroupIntersectionFst u c)
        (Dynamic.isClosedSubgroup_intersectionFst u c hcc) hu.isUnipotent)
      (Dynamic.range_intersectionSnd_isNormal u c hnC)
  apply le_antisymm
  · intro T x hx
    exact ⟨hforward T hx, by
      obtain ⟨y, rfl⟩ := SubgroupFunctor.mem_range.mp hx
      exact SubgroupFunctor.mem_range.mpr ⟨y ≫ v.hom.hom, Category.assoc _ _ _⟩⟩
  · have hle := SubgroupFunctor.range_comp_mono hinter c
    rw [← subgroupIntersection_condition u c] at hle
    change SubgroupFunctor.range (subgroupIntersectionHom u c) ≤
      SubgroupFunctor.range (v ≫ c) at hle
    rwa [range_subgroupIntersectionHom] at hle

end Langlands.GroupScheme

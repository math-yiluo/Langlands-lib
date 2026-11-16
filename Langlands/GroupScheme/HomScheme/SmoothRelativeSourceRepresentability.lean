import Langlands.GroupScheme.HomScheme.GraphLocusUniversal
import Langlands.GroupScheme.HomScheme.SmoothTorusSubgroupRepresentabilityProof
import Langlands.GroupScheme.Torus.RelativeReductive

/-! # Actual Hom schemes with relative torus source -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open CategoryTheory.MonoidalCategory CategoryTheory.CartesianMonoidalCategory
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

namespace RelativeTorus

/-- Two relative tori admit a common etale splitting cover. -/
theorem exists_common_splitting_cover {S : Scheme.{u}} {H G : GroupScheme S}
    (hH : IsTorus H) (hG : IsTorus G) :
    ∃ 𝒰 : Scheme.Cover.{u} (Scheme.precoverage @Etale) S,
      (∀ i, IsSplitTorus ((baseChange (𝒰.f i)).obj H)) ∧
      (∀ i, IsSplitTorus ((baseChange (𝒰.f i)).obj G)) := by
  obtain ⟨𝒰, h𝒰⟩ := hH
  choose 𝒱 h𝒱 using fun i => hG.baseChange (𝒰.f i)
  refine ⟨𝒰.bind 𝒱, ?_, ?_⟩
  · intro i
    exact IsSplitTorus.of_iso
      (baseChangeCompIso (𝒰.f i.1) ((𝒱 i.1).f i.2) H)
      ((h𝒰 i.1).baseChange ((𝒱 i.1).f i.2))
  · intro i
    exact IsSplitTorus.of_iso
      (baseChangeCompIso (𝒰.f i.1) ((𝒱 i.1).f i.2) G) (h𝒱 i.1 i.2)

end RelativeTorus

namespace TorusIsomorphismLocus

/-- The open isomorphism locus represents invertibility between relative tori
on every test scheme. -/
theorem isIso_baseChange_iff_factors_of_relative
    {S T : Scheme.{u}} {H G : GroupScheme S}
    (hH : RelativeTorus.IsTorus H) (hG : RelativeTorus.IsTorus G)
    (i : H ⟶ G) (b : T ⟶ S) :
    IsIso ((baseChange b).map i) ↔
      ∃ a : T ⟶ opens i, a ≫ (opens i).ι = b := by
  obtain ⟨𝒰, h𝒰H, h𝒰G⟩ := RelativeTorus.exists_common_splitting_cover hH hG
  rw [isIso_baseChange_iff_range_subset_opens_of_cover 𝒰 h𝒰H h𝒰G i b]
  constructor
  · intro h
    have h' : Set.range b ⊆ Set.range (opens i).ι := by simpa using h
    exact ⟨IsOpenImmersion.lift (opens i).ι b h', IsOpenImmersion.lift_fac _ _ _⟩
  · rintro ⟨a, rfl⟩
    simpa only [Set.range_comp, Scheme.Hom.comp_base, TopCat.coe_comp,
      Scheme.Opens.range_ι] using Set.range_comp_subset_range a (opens i).ι

end TorusIsomorphismLocus

namespace HomScheme

variable {S : Scheme.{u}} {H G : GroupScheme S} {M T : Over S}
variable {K : GroupScheme M.left}

/-- The graph of a homomorphism with relative torus source is an admissible
closed relative torus subgroup. -/
theorem isAdmissible_relativeGraph_of_relativeTorus [IsSeparated G.X.hom]
    (hH : RelativeTorus.IsTorus H) (i : RelativeHom H G T) :
    TorusSubgroupModuli.IsAdmissible (relativeGraph i) :=
  TorusSubgroupModuli.isAdmissible_range _ (isClosedSubgroup_relativeGraphHom i)
    (hH.baseChange T.hom)

/-- Restricting an actual universal closed torus-subgroup family to its open
graph locus gives an actual universal Hom family. -/
theorem isUniversal_graphLocusHom_of_relativeTorus [IsSeparated G.X.hom]
    (hH : RelativeTorus.IsTorus H)
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) :
    IsUniversal (graphLocusHom j) := by
  intro T
  constructor
  · intro a b hab
    obtain ⟨c, hc, hu⟩ := huni T
      (relativeGraph (evaluate a (graphLocusHom j)))
      (isAdmissible_relativeGraph_of_relativeTorus hH _)
    have ha : a ≫ graphLocusMap j = c :=
      hu _ (evaluate_graphLocusHom j a)
    have hb : b ≫ graphLocusMap j = c := by
      apply hu
      rw [evaluate_graphLocusHom]
      exact congrArg relativeGraph hab.symm
    exact (cancel_mono (graphLocusMap j)).mp (ha.trans hb.symm)
  · intro f
    obtain ⟨c, hc, _⟩ := huni T (relativeGraph f)
      (isAdmissible_relativeGraph_of_relativeTorus hH f)
    let : IsClosedImmersion (TorusSubgroupModuli.familyHom j c).hom.hom.left :=
      TorusSubgroupModuli.isClosedSubgroup_familyHom j hj c
    let : Mono (TorusSubgroupModuli.familyHom j c).hom.hom :=
      Over.mono_of_mono_left _
    have hi : IsIso (TorusSubgroupModuli.familyHom j c ≫
        (baseChange T.hom).map (fst H G)) :=
      isIso_firstProjection_of_range_eq_relativeGraph _ f hc
    have hp := (isIso_familyHom_fst_iff j c).mp hi
    obtain ⟨a, ha⟩ :=
      (TorusIsomorphismLocus.isIso_baseChange_iff_factors_of_relative
        hK (hH.baseChange M.hom)
        (j ≫ (baseChange M.hom).map (fst H G)) c.left).mp hp
    let a' : T ⟶ graphLocus j := Over.homMk a (by
      change a ≫ ((TorusIsomorphismLocus.opens
        (j ≫ (baseChange M.hom).map (fst H G))).ι ≫ M.hom) = T.hom
      rw [← Category.assoc, ha]
      exact Over.w c)
    have hfac : a' ≫ graphLocusMap j = c := by
      apply Over.OverMorphism.ext
      exact ha
    refine ⟨a', relativeGraph_injective ?_⟩
    rw [← evaluate_graphLocusHom, hfac, hc]

/-- A smooth universal subgroup family in the product supplies smooth actual
Hom representability. Existence of that subgroup family is an explicit premise. -/
theorem exists_smooth_universal_of_relativeTorusSubgroupFamily [IsSeparated G.X.hom]
    (hH : RelativeTorus.IsTorus H)
    (j : K ⟶ (baseChange M.hom).obj (H ⊗ G))
    (hj : IsClosedSubgroup j) (hK : RelativeTorus.IsTorus K)
    (huni : TorusSubgroupModuli.IsUniversal j) [Smooth M.hom] :
    ∃ (N : Over S) (i : RelativeHom H G N), IsUniversal i ∧ Smooth N.hom :=
  ⟨graphLocus j, graphLocusHom j, isUniversal_graphLocusHom_of_relativeTorus hH j hj hK huni,
    smooth_graphLocus j⟩

/-- Smooth actual Hom representability from a relative torus over any base. -/
theorem exists_smooth_universal_of_relativeTorus
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : RelativeTorus.IsTorus H) :
    ∃ (M : Over S) (i : RelativeHom H G M), IsUniversal i ∧ Smooth M.hom := by
  let : Smooth H.X.hom := hH.smooth
  let : IsAffineHom H.X.hom := hH.isAffineHom
  let : Smooth (H ⊗ G).X.hom := smooth_tensor H.X G.X inferInstance inferInstance
  let : IsAffineHom (H ⊗ G).X.hom := by
    change IsAffineHom (pullback.fst H.X.hom G.X.hom ≫ H.X.hom)
    let : IsAffineHom (pullback.fst H.X.hom G.X.hom) :=
      MorphismProperty.pullback_fst _ _ (inferInstance : IsAffineHom G.X.hom)
    infer_instance
  obtain ⟨M, K, j, hj, hK, huni, hM⟩ :=
    TorusSubgroupModuli.smoothTorusSubgroupRepresentability S (H ⊗ G)
  let := hM
  exact exists_smooth_universal_of_relativeTorusSubgroupFamily hH j hj hK huni

/-- A chosen smooth scheme with its actual universal Hom family. -/
def smoothRelativeSourceHomModel
    [Smooth G.X.hom] [IsAffineHom G.X.hom] (hH : RelativeTorus.IsTorus H) :
    Σ M : Over S, { i : RelativeHom H G M // IsUniversal i ∧ Smooth M.hom } :=
  let M := Classical.choose (exists_smooth_universal_of_relativeTorus (G := G) hH)
  let i := Classical.choose (Classical.choose_spec
    (exists_smooth_universal_of_relativeTorus (G := G) hH))
  ⟨M, i, Classical.choose_spec (Classical.choose_spec
    (exists_smooth_universal_of_relativeTorus (G := G) hH))⟩

end HomScheme
end Langlands.GroupScheme

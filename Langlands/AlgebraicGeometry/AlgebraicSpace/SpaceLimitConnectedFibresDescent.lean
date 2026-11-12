import Langlands.AlgebraicGeometry.AlgebraicSpace.AffineTargetFamilyConnectedBaseChange
import Langlands.AlgebraicGeometry.AlgebraicSpace.ConnectedFibreLocus
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceBaseChangeMorphismComparison
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceLimitPropertyDescentStatement
import Langlands.AlgebraicGeometry.AlgebraicSpace.SpaceFilteredRingPointProof
import Langlands.AlgebraicGeometry.EtaleEquivalenceRelationActionLimits

/-! # Connected nonempty geometric fibres descend along affine limits -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Topology
open Langlands.AlgebraicGeometry.EtaleEquivalenceRelation.Action

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

namespace AffineTargetFamily

variable {S T : Scheme.{u}} {X Y : AlgebraicSpace S} (f : X ⟶ Y)
    {V : Over S} (b : (schemeYoneda S).obj V ⟶ Y.presheaf)

/-- The good geometric-fibre locus on the actual base-changed target chart. -/
def connectedFibreLocusOver (g : T ⟶ S) : Set (Limits.pullback g V.hom : Scheme.{u}) :=
  (pullback.snd g V.hom) ⁻¹' connectedFibreLocus (space f b)

/-- The actual good locus is constructible on the changed target chart. -/
theorem isConstructible_connectedFibreLocusOver [IsAffine S] [IsAffine V.left]
    [LocallyOfFinitePresentation V.hom]
    (hXqs : IsQuasiSeparated X)
    (hX : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) X)
    (hY : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u}) Y)
    (hYqs : IsQuasiSeparated Y) (g : T ⟶ S) :
    IsConstructible (connectedFibreLocusOver f b g) :=
  (pullback.snd g V.hom).isConstructible_preimage
    (isConstructible_schemeComponentCount_affine (space f b)
      (isQuasiSeparated f b hXqs) (hasAtlasProperty_finitePresentation f b hX hY hYqs) 1)

/-- The changed morphism has connected nonempty geometric fibres exactly when
its good locus on the changed chart is the whole chart. -/
theorem hasGeometricallyConnectedFibres_iff_locus_eq_univ
    (hb : IsEtale b) (hs : IsSurjective b)
    (hfp : HasAtlasProperty (@LocallyOfFinitePresentation.{u} ⊓ @QuasiCompact.{u})
      (space f b)) (g : T ⟶ S) :
    HasGeometricallyConnectedFibres (baseChangeMap g f) ↔
      connectedFibreLocusOver f b g = Set.univ := by
  rw [hasGeometricallyConnectedFibres_baseChange_iff f b g hb hs,
    hasGeometricallyConnectedFibres_structural_baseChange_iff _ _ hfp]
  constructor
  · intro h
    apply Set.eq_univ_of_forall
    intro p
    have hp := h ((pullbackSymmetry g V.hom).hom p)
    change schemeGeometricFibreComponentCount (space f b) ((pullback.snd g V.hom) p) = 1
    simpa only [← Scheme.Hom.comp_apply, pullbackSymmetry_hom_comp_fst] using hp
  · intro h p
    have hp := Set.eq_univ_iff_forall.mp h ((pullbackSymmetry g V.hom).inv p)
    change schemeGeometricFibreComponentCount (space f b)
      ((pullback.snd g V.hom) ((pullbackSymmetry g V.hom).inv p)) = 1 at hp
    simpa only [← Scheme.Hom.comp_apply, pullbackSymmetry_inv_comp_snd] using hp

end AffineTargetFamily

/-- Conrad's connected nonempty geometric-fibre clause for arbitrary cofiltered
limits of affine schemes, with exactly the published stage hypotheses. -/
theorem spaceLimitGeometricallyConnectedFibresDescent :
    SpaceLimitPropertyDescends.{u} (fun f => HasGeometricallyConnectedFibres f) := by
  intro I _ _ D _ c hc i X Y hXqs hX hYqs hY f
  obtain ⟨V, b, hVa, hb, hs, hVl⟩ := exists_affine_finitePresentation_atlas Y hY
  let := hVa
  let := hVl
  have hfp := AffineTargetFamily.hasAtlasProperty_finitePresentation f b hX hY hYqs
  let E := TargetLimit.diagram (SpaceFilteredPoints.overDiagram D i)
    (SpaceFilteredPoints.overStructure D i) V.hom
  let p := c.π.app i
  let C := TargetLimit.coneOfPullback (SpaceFilteredPoints.overDiagram D i)
    (SpaceFilteredPoints.overStructure D i) V.hom (c.whisker (Over.forget i)) p
    (SpaceFilteredPoints.overCone_π_comp i c) (IsPullback.of_hasPullback p V.hom)
  have hC : IsLimit C := TargetLimit.isLimitConeOfPullback _ _ _ _ _ _ _
    (SpaceFilteredPoints.overConeIsLimit i c hc)
  have (j : Over i) : IsAffine (E.obj j) := by
    change IsAffine (Limits.pullback (D.map j.hom) V.hom)
    infer_instance
  have {j k : Over i} (a : j ⟶ k) : IsAffineHom (E.map a) := inferInstance
  have hproj (j : Over i) :
      C.π.app j ≫ pullback.snd (D.map j.hom) V.hom = pullback.snd p V.hom :=
    TargetLimit.coneOfPullback_π_snd _ _ _ _ _ _ _ _
  constructor
  · intro hf
    have hgood := (AffineTargetFamily.hasGeometricallyConnectedFibres_iff_locus_eq_univ
      f b hb hs hfp p).mp hf
    let i₀ : Over i := Over.mk (𝟙 i)
    let s₀ := AffineTargetFamily.connectedFibreLocusOver f b (D.map i₀.hom)
    have hs₀ : IsConstructible s₀ :=
      AffineTargetFamily.isConstructible_connectedFibreLocusOver f b hXqs hX hY hYqs _
    have hlimit : (C.π.app i₀) ⁻¹' s₀ = Set.univ := by
      apply Set.eq_univ_of_forall
      intro x
      have hx := Set.eq_univ_iff_forall.mp hgood x
      change (pullback.snd (D.map i₀.hom) V.hom) (C.π.app i₀ x) ∈
        connectedFibreLocus (AffineTargetFamily.space f b)
      erw [← Scheme.Hom.comp_apply, hproj]
      exact hx
    obtain ⟨j, a, hj⟩ := SchemeFiberGeometry.exists_map_preimage_eq_univ_of_isConstructible
      E C hC i₀ s₀ hs₀ hlimit
    have hnat : E.map a ≫ pullback.snd (D.map i₀.hom) V.hom =
        pullback.snd (D.map j.hom) V.hom := by
      have hn := (TargetLimit.comparison (SpaceFilteredPoints.overDiagram D i)
        (SpaceFilteredPoints.overStructure D i) V.hom).naturality a
      change E.map a ≫ pullback.snd (D.map i₀.hom) V.hom =
        pullback.snd (D.map j.hom) V.hom ≫ 𝟙 V.left at hn
      exact hn.trans (Category.comp_id _)
    refine ⟨j.left, j.hom,
      (AffineTargetFamily.hasGeometricallyConnectedFibres_iff_locus_eq_univ
        f b hb hs hfp (D.map j.hom)).mpr ?_⟩
    apply Set.eq_univ_of_forall
    intro x
    have hx := Set.eq_univ_iff_forall.mp hj x
    change (pullback.snd (D.map i₀.hom) V.hom) (E.map a x) ∈
      connectedFibreLocus (AffineTargetFamily.space f b) at hx
    erw [← Scheme.Hom.comp_apply, hnat] at hx
    exact hx
  · rintro ⟨j, r, hr⟩
    let e := baseChangeCompNatIso (D.map r) (c.π.app j) (c.π.app i) (c.w r)
    exact HasGeometricallyConnectedFibres.of_arrow_iso (e.app X) (e.app Y)
      (e.hom.naturality f).symm (hr.baseChangeMap (g := c.π.app j))

end Langlands.AlgebraicGeometry.AlgebraicSpace

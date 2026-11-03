import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenMorphism
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartPullbackCoherence
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainAlgebraGluing

/-! # Identity and composition of actual ordinary-open pullbacks -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory TopologicalSpace Topology Opposite
open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B C : PresentedAffinoidAlgebra K}

namespace OpenSections

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Identity coefficient pullback retains every actual quotient component. -/
@[simp]
theorem pullback_id (U : Opens (BanachSpectrum A))
    (s : Sections (U : Set (BanachSpectrum A))) :
    pullback (BoundedAlgHom.id K A) U s = s := by
  apply ext
  intro e
  calc
    _ = (pullbackIdIso e.val).inv.restriction
        (pullbackMap (BoundedAlgHom.id K A) e.val (s.val e)) :=
      pullback_local (BoundedAlgHom.id K A) U s e e (pullbackIdIso e.val).inv
    _ = (pullbackIdIso e.val).inv.restriction
        ((pullbackIdIso e.val).hom.restriction (s.val e)) :=
      congrArg (fun f : BoundedAlgHom K e.val.algebra
        (RationalChart.pullback (BoundedAlgHom.id K A) e.val).algebra =>
          (pullbackIdIso e.val).inv.restriction (f (s.val e)))
        (pullbackIdIso_hom_restriction e.val).symm
    _ = s.val e :=
      congrArg (fun f : e.val ⟶ e.val => f.restriction (s.val e))
        (pullbackIdIso e.val).inv_hom_id

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem transported_comp (φ : BoundedAlgHom K A B)
    (ψ : BoundedAlgHom K B C) (d : RationalChart K A) (b : RationalChart K B)
    (w : RationalChart K C) (h : b ⟶ RationalChart.pullback φ d)
    (f : w ⟶ RationalChart.pullback ψ b)
    (g : w ⟶ RationalChart.pullback (ψ.comp φ) d) (a : d.algebra) :
    f.restriction (pullbackMap ψ b (h.restriction (pullbackMap φ d a))) =
      g.restriction (pullbackMap (ψ.comp φ) d a) := by
  have hn := congrArg (fun k : BoundedAlgHom K
      (RationalChart.pullback φ d).algebra (RationalChart.pullback ψ b).algebra =>
        k (pullbackMap φ d a)) (pullbackRestriction_comp_pullbackMap ψ h)
  change (pullbackRestriction ψ h).restriction
      (pullbackMap ψ (RationalChart.pullback φ d) (pullbackMap φ d a)) =
    pullbackMap ψ b (h.restriction (pullbackMap φ d a)) at hn
  have ha : f ≫ pullbackRestriction ψ h = g ≫ (pullbackCompIso φ ψ d).hom :=
    @Subsingleton.elim (Restriction _ _) inferInstance _ _
  have hc := congrArg (fun k : BoundedAlgHom K d.algebra
    (RationalChart.pullback (ψ.comp φ) d).algebra => k a)
      (pullbackCompIso_hom_transport φ ψ d)
  change (pullbackCompIso φ ψ d).hom.restriction
    (pullbackMap ψ (RationalChart.pullback φ d) (pullbackMap φ d a)) =
      pullbackMap (ψ.comp φ) d a at hc
  calc
    _ = (f ≫ pullbackRestriction ψ h).restriction
        (pullbackMap ψ (RationalChart.pullback φ d) (pullbackMap φ d a)) :=
      congrArg f.restriction hn.symm
    _ = (g ≫ (pullbackCompIso φ ψ d).hom).restriction
        (pullbackMap ψ (RationalChart.pullback φ d) (pullbackMap φ d a)) :=
      congrArg (fun k : w ⟶ RationalChart.pullback ψ (RationalChart.pullback φ d) =>
        k.restriction
          (pullbackMap ψ (RationalChart.pullback φ d) (pullbackMap φ d a))) ha
    _ = g.restriction (pullbackMap (ψ.comp φ) d a) := by
      rw [Restriction.restriction_comp, BoundedAlgHom.comp_apply]
      exact congrArg g.restriction hc

private abbrev CompositionLabel (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A)) :=
  Σ d : ChartIn (U : Set (BanachSpectrum A)),
    ChartIn (comap φ.toBoundedRingHom ⁻¹' interior d.val.locus)

/-- A finite target refinement with actual rational neighborhoods at both
intermediate stages of a composite coefficient map. -/
private def compositionRefinement (φ : BoundedAlgHom K A B)
    (ψ : BoundedAlgHom K B C) (U : Opens (BanachSpectrum A))
    (e : ChartIn (comap (ψ.comp φ).toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A)))) :
    FiniteOpenRefinement e.val
      (fun l : CompositionLabel φ U =>
        {x : e.val.locus | comap ψ.toBoundedRingHom x.val ∈ interior l.2.val.locus}) :=
  FiniteOpenRefinement.ofOpenCover e.val _
    (fun l => isOpen_interior.preimage
      ((comapContinuous ψ.toBoundedRingHom).continuous.comp continuous_subtype_val))
    (by
      intro x
      let y := comap ψ.toBoundedRingHom x.val
      have hy : comap φ.toBoundedRingHom y ∈ U := e.property x.property
      let d := pointChart U (comap φ.toBoundedRingHom y) hy
      let V := (Opens.map (openSpectrumMap φ)).obj (interiorOpen d.val)
      have hyV : y ∈ V :=
        mem_interior_iff_mem_nhds.mpr (pointChart_mem_nhds U _ hy)
      let b := pointChart V y hyV
      exact ⟨⟨d, b⟩, mem_interior_iff_mem_nhds.mpr (pointChart_mem_nhds V y hyV)⟩)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Direct and successive pullback agree as actual compatible quotient families. -/
theorem pullback_comp (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C)
    (U : Opens (BanachSpectrum A)) (s : Sections (U : Set (BanachSpectrum A))) :
    pullback (ψ.comp φ) U s =
      pullback ψ ((Opens.map (openSpectrumMap φ)).obj U) (pullback φ U s) := by
  apply ext
  intro e
  let c := compositionRefinement φ ψ U e
  apply Domain.FiniteCover.algebra_ext_of_restrict_eq c.toFiniteCover
  intro i
  let d := (c.label i).1
  let b₀ := (c.label i).2
  let V := (Opens.map (openSpectrumMap φ)).obj U
  let b : ChartIn (V : Set (BanachSpectrum B)) :=
    ⟨b₀.val, fun y hy => d.property (interior_subset (b₀.property hy))⟩
  let h : b.val ⟶ RationalChart.pullback φ d.val :=
    restrictionOfSubset _ _ (by
      rw [pullback_locus]
      intro y hy
      change comap φ.toBoundedRingHom y ∈ d.val.locus
      exact interior_subset (b₀.property hy))
  let f : c.chart i ⟶ RationalChart.pullback ψ b.val :=
    restrictionOfSubset _ _ (by
      rw [pullback_locus]
      intro z hz
      change comap ψ.toBoundedRingHom z ∈ b₀.val.locus
      exact interior_subset (c.subordinate_point i z hz))
  let g : c.chart i ⟶ RationalChart.pullback (ψ.comp φ) d.val :=
    restrictionOfSubset _ _ (by
      rw [pullback_locus]
      intro z hz
      change comap φ.toBoundedRingHom (comap ψ.toBoundedRingHom z) ∈ d.val.locus
      exact interior_subset (b₀.property (interior_subset (c.subordinate_point i z hz))))
  change (c.map i).restriction (pullbackElement (ψ.comp φ) s e) =
    (c.map i).restriction (pullbackElement ψ (U := V) (pullback φ U s) e)
  calc
    _ = g.restriction (pullbackMap (ψ.comp φ) d.val (s.val d)) :=
      pullbackElement_local (ψ.comp φ) s e d (c.chart i) (c.map i) g
    _ = f.restriction
        (pullbackMap ψ b.val (h.restriction (pullbackMap φ d.val (s.val d)))) :=
      (transported_comp φ ψ d.val b.val (c.chart i) h f g (s.val d)).symm
    _ = f.restriction (pullbackMap ψ b.val ((pullback φ U s).val b)) :=
      congrArg (fun a => f.restriction (pullbackMap ψ b.val a))
        (pullback_local φ U s b d h).symm
    _ = _ :=
      (pullbackElement_local ψ (U := V) (pullback φ U s) e b (c.chart i) (c.map i) f).symm

end OpenSections

omit [CompleteSpace K] in
/-- The underlying spectral maps compose as actual continuous maps. -/
theorem openSpectrumMap_comp (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    openSpectrumMap (ψ.comp φ) = openSpectrumMap ψ ≫ openSpectrumMap φ := by
  apply TopCat.ext
  intro x
  apply BanachSpectrum.ext
  intro a
  rfl

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The concrete section law is also a law of presheaf morphisms. -/
theorem openAlgebraPresheafMap_comp (φ : BoundedAlgHom K A B)
    (ψ : BoundedAlgHom K B C) :
    openAlgebraPresheafMap (ψ.comp φ) =
      openAlgebraPresheafMap φ ≫
        (TopCat.Presheaf.pushforward (CommAlgCat K) (openSpectrumMap φ)).map
          (openAlgebraPresheafMap ψ) := by
  apply NatTrans.ext
  funext U
  apply CommAlgCat.hom_ext
  exact AlgHom.ext (fun s => OpenSections.pullback_comp φ ψ U.unop s)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- The actual algebra-sheaf map of the identity is the identity morphism. -/
@[simp]
theorem algebraSheafedSpaceMap_id (A : PresentedAffinoidAlgebra K) :
    algebraSheafedSpaceMap (BoundedAlgHom.id K A) = 𝟙 (algebraSheafedSpace K A) := by
  apply InducedCategory.hom_ext
  refine AlgebraicGeometry.PresheafedSpace.hext _ _ ?_ ?_
  · rfl
  · apply heq_of_eq
    apply NatTrans.ext
    funext U
    apply CommAlgCat.hom_ext
    exact AlgHom.ext (fun s => OpenSections.pullback_id U.unop s)

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- Algebra-sheaf pullback composes in the contravariant direction. -/
theorem algebraSheafedSpaceMap_comp (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    algebraSheafedSpaceMap (ψ.comp φ) =
      algebraSheafedSpaceMap ψ ≫ algebraSheafedSpaceMap φ := by
  apply InducedCategory.hom_ext
  refine AlgebraicGeometry.PresheafedSpace.hext _ _ ?_ ?_
  · exact openSpectrumMap_comp φ ψ
  · exact heq_of_eq (openAlgebraPresheafMap_comp φ ψ)

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting scalars preserves the proved identity law. -/
@[simp]
theorem ringSheafedSpaceMap_id (A : PresentedAffinoidAlgebra K) :
    ringSheafedSpaceMap (BoundedAlgHom.id K A) = 𝟙 (ringSheafedSpace K A) := by
  apply InducedCategory.hom_ext
  have h := congrArg (fun f : algebraSheafedSpace K A ⟶ algebraSheafedSpace K A => f.hom)
    (algebraSheafedSpaceMap_id A)
  exact (congrArg (forget₂ (CommAlgCat K) CommRingCat.{u}).mapPresheaf.map h).trans
    ((forget₂ (CommAlgCat K) CommRingCat.{u}).mapPresheaf.map_id _)

set_option backward.isDefEq.respectTransparency false in
/-- Forgetting scalars preserves the proved composition law. -/
theorem ringSheafedSpaceMap_comp (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    ringSheafedSpaceMap (ψ.comp φ) =
      ringSheafedSpaceMap ψ ≫ ringSheafedSpaceMap φ := by
  apply InducedCategory.hom_ext
  have h := congrArg (fun f : algebraSheafedSpace K C ⟶ algebraSheafedSpace K A => f.hom)
    (algebraSheafedSpaceMap_comp φ ψ)
  exact (congrArg (forget₂ (CommAlgCat K) CommRingCat.{u}).mapPresheaf.map h).trans
    ((forget₂ (CommAlgCat K) CommRingCat.{u}).mapPresheaf.map_comp _ _)

set_option backward.isDefEq.respectTransparency false in
/-- The locally ringed-space morphism of the identity is the identity. -/
@[simp]
theorem locallyRingedSpaceMap_id (A : PresentedAffinoidAlgebra K) :
    locallyRingedSpaceMap (BoundedAlgHom.id K A) = 𝟙 (locallyRingedSpace K A) := by
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  exact congrArg (fun f : ringSheafedSpace K A ⟶ ringSheafedSpace K A => f.hom)
    (ringSheafedSpaceMap_id A)

set_option backward.isDefEq.respectTransparency false in
/-- The constructed local morphisms compose in the contravariant direction. -/
theorem locallyRingedSpaceMap_comp (φ : BoundedAlgHom K A B) (ψ : BoundedAlgHom K B C) :
    locallyRingedSpaceMap (ψ.comp φ) =
      locallyRingedSpaceMap ψ ≫ locallyRingedSpaceMap φ := by
  apply AlgebraicGeometry.LocallyRingedSpace.Hom.ext'
  exact congrArg (fun f : ringSheafedSpace K C ⟶ ringSheafedSpace K A => f.hom)
    (ringSheafedSpaceMap_comp φ ψ)

/-- The actual locally ringed spectrum functor on positive-radius affinoid
presentations and every bounded algebra map. -/
def locallyRingedSpaceFunctor (K : Type u) [NormedField K] [IsUltrametricDist K]
    [CompleteSpace K] : PresentedAffinoidSpace K ⥤ AlgebraicGeometry.LocallyRingedSpace where
  obj A := locallyRingedSpace K A.unop
  map f := locallyRingedSpaceMap f.unop
  map_id A := locallyRingedSpaceMap_id A.unop
  map_comp f g := locallyRingedSpaceMap_comp g.unop f.unop

/-- The underlying topological functor is the original bounded-seminorm spectrum. -/
@[simp]
theorem locallyRingedSpaceFunctor_forget (K : Type u) [NormedField K]
    [IsUltrametricDist K] [CompleteSpace K] :
    locallyRingedSpaceFunctor K ⋙ AlgebraicGeometry.LocallyRingedSpace.forgetToTop =
      affinoidSpectrumFunctor K := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

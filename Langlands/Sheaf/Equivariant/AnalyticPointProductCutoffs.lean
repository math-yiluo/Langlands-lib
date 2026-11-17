import Langlands.Sheaf.Equivariant.TwistedPointProductCutoffs
import Langlands.Sheaf.Equivariant.AnalyticOpenPointProducts
import Langlands.Sheaf.Equivariant.AnalyticEtaleGodement
import Langlands.Geometry.Analytic.LocalizedCompactNeighborhoods

/-! # Actual stable cutoffs on analytic induced point products -/

noncomputable section

attribute [local instance] Classical.propDecidable

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

universe u v uL z

namespace Langlands.Sheaf.Equivariant.Analytic

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Langlands.Analytic Langlands.Analytic.SaturatedAtlasPresentation
open Langlands.Sheaf.PointProduct
open TwistedOver TwistedOver.InductionCoordinates LocalActionSystem

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
variable (L : Type uL) [NormedField L] [NormedAlgebra K L]
variable {X : LocalizedCategory.{u, v, v} (K := K)}
variable (h : ∀ x : (localizedFieldPointFunctor L).obj X, EtaleSite.PointAxioms L x)
variable {G : Type z} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable (ρ : G →* Aut X)
variable {R : Type (max u (v + 1) uL)} [CommRing R]
variable [Small.{max u (v + 1) uL} G]

variable (M : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X) →
  ModuleCat.{max u (v + 1) uL} R)

/-- The actual raw induction of the independently specified analytic point product. -/
abbrev etaleRawInducedPointProduct :
    (TwistedOver (etale (K := K)) ρ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  (ι etale ρ).op.ran.obj
    (productSheaf (etaleGodementPoints.{u, v, uL} L h) (ModuleCat.{max u (v + 1) uL} R) M).obj

/-- Its spatial mask uses the actual underlying point before translation. -/
def etaleSpatialCutoff (V : Set (localizedSpaceFunctor.obj X))
    (U : TwistedOver (etale (K := K)) ρ)
    (s : (etaleRawInducedPointProduct L h ρ M).obj (op U)) :
    (etaleRawInducedPointProduct L h ρ M).obj (op U) :=
  haveI := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  let := localizedSpaceAction ρ
  spatialCutoff.{max u (v + 1), max u (v + 1), z, max u (v + 1) uL, max u (v + 1) uL, v}
    ρ (etaleGodementPoints.{u, v, uL} L h) M
    (fun x => pointProjection L X x.down) V U s

omit [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G] in
/-- The original spatial coordinate of a lifted point is its image under the
untranslated structure morphism. -/
theorem translated_fiber_spatial_coordinate
    (U : EtaleSite X) (g : G)
    (x : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X))
    (p : (etaleGodementPoints.{u, v, uL} L h x).fiber.obj ((translate etale ρ g).obj U)) :
    localizedSpaceFunctor.map (ρ g⁻¹).hom (pointProjection L X x.down) =
      localizedSpaceFunctor.map U.hom (pointProjection L U.left p.down.1) := by
  let := localizedSpaceAction ρ
  have hp := (pointProjection_map L ((translate etale ρ g).obj U).hom p.down.1).symm.trans
    (congrArg (pointProjection L X) p.down.2)
  change localizedSpaceFunctor.map (U.hom ≫ (ρ g).hom)
    (pointProjection L U.left p.down.1) = pointProjection L X x.down at hp
  rw [CategoryTheory.Functor.map_comp, TopCat.comp_app] at hp
  change localizedSpaceFunctor.map (ρ g).hom
    (localizedSpaceFunctor.map U.hom (pointProjection L U.left p.down.1)) = _ at hp
  let y : localizedSpaceFunctor.obj X :=
    localizedSpaceFunctor.map U.hom (pointProjection L U.left p.down.1)
  have hp' : g • y = pointProjection L X x.down := hp
  change g⁻¹ • pointProjection L X x.down = y
  rw [← hp', inv_smul_smul]

omit [TopologicalSpace G] [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G] in
/-- An open-domain fiber has its original spatial coordinate in the defining open. -/
theorem translated_open_fiber_mem
    (U : Opens (localizedSpaceFunctor.obj X)) (g : G)
    (x : ULift.{max u (v + 1) uL} ((localizedFieldPointFunctor L).obj X))
    (p : (etaleGodementPoints.{u, v, uL} L h x).fiber.obj
      ((translate etale ρ g).obj (openEtaleObject X U))) :
    localizedSpaceFunctor.map (ρ g⁻¹).hom (pointProjection L X x.down) ∈ U := by
  rw [translated_fiber_spatial_coordinate L h ρ (openEtaleObject X U) g x p]
  have he := domainι_apply
    ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen)
    (pointProjection L (openEtaleObject X U).left p.down.1)
  exact he.symm ▸ (pointProjection L (openEtaleObject X U).left p.down.1).property

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- On an open inside the selected set, the cutoff is the identity. -/
theorem etaleSpatialCutoff_eq_self
    (V : Set (localizedSpaceFunctor.obj X))
    (U : Opens (localizedSpaceFunctor.obj X)) (hUV : (U : Set _) ⊆ V)
    (s : (etaleRawInducedPointProduct L h ρ M).obj
      (op ((ι etale ρ).obj (openEtaleObject X U)))) :
    etaleSpatialCutoff L h ρ M V _ s = s := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  let := localizedSpaceAction ρ
  apply (moduleCoordinates ρ _ _).injective
  funext g
  apply (sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
    (etaleGodementPoints.{u, v, uL} L h) M _).injective
  funext x p
  rw [etaleSpatialCutoff, spatialCutoff_coordinates]
  split_ifs with hx
  · rfl
  · exact (hx (hUV (translated_open_fiber_mem L h ρ U g x p))).elim

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- On an open disjoint from the selected set, the cutoff is zero. -/
theorem etaleSpatialCutoff_eq_zero
    (V : Set (localizedSpaceFunctor.obj X))
    (U : Opens (localizedSpaceFunctor.obj X)) (hUV : Disjoint (U : Set _) V)
    (s : (etaleRawInducedPointProduct L h ρ M).obj
      (op ((ι etale ρ).obj (openEtaleObject X U)))) :
    etaleSpatialCutoff L h ρ M V _ s = 0 := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  let := localizedSpaceAction ρ
  apply (moduleCoordinates ρ _ _).injective
  funext g
  apply (sectionCoordinates.{max u (v + 1) uL, max u (v + 1) uL}
    (etaleGodementPoints.{u, v, uL} L h) M _).injective
  funext x p
  have hn : localizedSpaceFunctor.map (ρ g⁻¹).hom (pointProjection L X x.down) ∉ V :=
    fun hx => Set.disjoint_left.1 hUV (translated_open_fiber_mem L h ρ U g x p) hx
  rw [etaleSpatialCutoff, spatialCutoff_coordinates]
  split_ifs with hx
  · exact (hn hx).elim
  · simp only [map_zero, Pi.zero_apply]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Ordinary restrictions commute with the actual spatial cutoff. -/
theorem etaleSpatialCutoff_restrict
    (V : Set (localizedSpaceFunctor.obj X)) {U W : EtaleSite X}
    (f : U ⟶ W)
    (s : (etaleRawInducedPointProduct L h ρ M).obj (op ((ι etale ρ).obj W))) :
    (etaleRawInducedPointProduct L h ρ M).map ((ι etale ρ).map f).op
        (etaleSpatialCutoff L h ρ M V _ s) =
      etaleSpatialCutoff L h ρ M V _
        ((etaleRawInducedPointProduct L h ρ M).map ((ι etale ρ).map f).op s) := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  let := localizedSpaceAction ρ
  unfold etaleSpatialCutoff spatialCutoff
  rw [map_indexedMapApp]
  simp only [homMk_twist, inv_one, mul_one]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Every raw section on an actual ordinary-open domain extends globally. -/
theorem etaleRawInducedPointProduct_open_restriction_surjective
    (U : Opens (localizedSpaceFunctor.obj X)) :
    Function.Surjective
      ((etaleRawInducedPointProduct L h ρ M).map
        ((ι etale ρ).map (openEtaleToSelf X U)).op) := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  have := etaleSite_locallySmall_points.{u, v, uL} X
  apply pointProduct_map_surjective_of_fiber_injective
    ρ (etaleGodementPoints.{u, v, uL} L h) M ((ι etale ρ).map (openEtaleToSelf X U))
  intro g x
  have hm : Mono (transport ρ ((ι etale ρ).map (openEtaleToSelf X U)) g) := by
    constructor
    intro W a b he
    apply MorphismProperty.Over.Hom.ext
    apply (cancel_mono
      (domainι X ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen))).1
    exact congrArg (fun k => k.left) he
  exact (etaleGodementPoints.{u, v, uL} L h x).fiber_map_injective_of_mono _

variable [(distinguishedLiftSystem ρ).HasAdmissibleRefinements (twistedEtaleTopology ρ)]

/-- A stable actual spatial cutoff preserves the analytic locally discrete part. -/
theorem etaleSpatialCutoff_mem_smoothSubmodule
    (V : Set (localizedSpaceFunctor.obj X)) (H : OpenSubgroup G)
    (hV : ∀ g ∈ H, ∀ y ∈ V, localizedSpaceFunctor.map (ρ g).hom y ∈ V)
    (U : TwistedOver (etale (K := K)) ρ)
    (s : (etaleRawInducedPointProduct L h ρ M).obj (op U))
    (hs : s ∈ LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)
      (etaleRawInducedPointProduct L h ρ M) U) :
    etaleSpatialCutoff L h ρ M V U s ∈
      LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)
        (etaleRawInducedPointProduct L h ρ M) U := by
  have := etale_hasPointwiseRightKanExtension.{u, v, uL} ρ R
  let := localizedSpaceAction ρ
  exact spatialCutoff_mem_smoothSubmodule ρ (etaleGodementPoints.{u, v, uL} L h) M
    (fun x => pointProjection L X x.down) V (distinguishedLiftSystem ρ)
      (isLiftSystem_liftSystem _) (twistedEtaleTopology ρ) H hV U s hs

omit [IsTopologicalGroup G] [Small.{max u (v + 1) uL} G] in
/-- Local discreteness of a global section can be checked on two ordinary
opens covering the actual underlying analytic space. -/
theorem mem_smoothSubmodule_of_two_opens
    {F : (TwistedOver (etale (K := K)) ρ)ᵒᵖ ⥤ ModuleCat.{max u (v + 1) uL} R}
    (s : F.obj (op ((ι etale ρ).obj (etaleSelf X))))
    (U W : Opens (localizedSpaceFunctor.obj X))
    (hcover : ∀ y : localizedSpaceFunctor.obj X, y ∈ U ∨ y ∈ W)
    (hU : F.map ((ι etale ρ).map (openEtaleToSelf X U)).op s ∈
      LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) F
        ((ι etale ρ).obj (openEtaleObject X U)))
    (hW : F.map ((ι etale ρ).map (openEtaleToSelf X W)).op s ∈
      LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) F
        ((ι etale ρ).obj (openEtaleObject X W))) :
    s ∈ LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) F
      ((ι etale ρ).obj (etaleSelf X)) := by
  let S : Sieve ((ι etale ρ).obj (etaleSelf X)) :=
    { arrows V f := F.map f.op s ∈
        LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ) F V
      downward_closed := by
        intro V V' f hf g
        rw [map_op_comp_apply]
        exact LocalActionSystem.map_mem_smoothSubmodule (distinguishedLiftSystem ρ)
          (twistedEtaleTopology ρ) F g hf }
  have hS : S ∈ twistedEtaleTopology ρ ((ι etale ρ).obj (etaleSelf X)) := by
    change Sieve.functorPullback (ι etale ρ) S ∈ etaleTopology X (etaleSelf X)
    apply mem_etaleTopology_of_jointlySurjective
    intro y
    rcases hcover y with hy | hy
    · refine ⟨openEtaleObject X U, openEtaleToSelf X U, hU, ⟨⟨y, hy⟩, ?_⟩⟩
      exact domainι_apply
        ((presentationOf X).openDomain (U : Set (localizedSpaceFunctor.obj X)) U.isOpen) ⟨y, hy⟩
    · refine ⟨openEtaleObject X W, openEtaleToSelf X W, hW, ⟨⟨y, hy⟩, ?_⟩⟩
      exact domainι_apply
        ((presentationOf X).openDomain (W : Set (localizedSpaceFunctor.obj X)) W.isOpen) ⟨y, hy⟩
  exact LocalActionSystem.mem_smoothSubmodule_of_covering (distinguishedLiftSystem ρ)
    (twistedEtaleTopology ρ) s hS fun _ _ hf => hf

/-- The open complement of the closure of a cutoff open. -/
abbrev etaleCutoffOutside (V : Opens (localizedSpaceFunctor.obj X)) :
    Opens (localizedSpaceFunctor.obj X) :=
  ⟨(closure (V : Set (localizedSpaceFunctor.obj X)))ᶜ, isClosed_closure.isOpen_compl⟩

/-- A locally discrete point-product section extends near every compact set to
a global locally discrete section vanishing outside a compact closed set. -/
theorem exists_etaleSmoothPointProduct_compact_extension
    [T2Space (localizedSpaceFunctor.obj X)] (hρ : IsContinuousAction ρ)
    {C : Set (localizedSpaceFunctor.obj X)} (hC : IsCompact C)
    (U : Opens (localizedSpaceFunctor.obj X)) (hCU : C ⊆ U)
    (s : (etaleRawInducedPointProduct L h ρ M).obj
      (op ((ι etale ρ).obj (openEtaleObject X U))))
    (hs : s ∈ LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)
      (etaleRawInducedPointProduct L h ρ M) ((ι etale ρ).obj (openEtaleObject X U))) :
    ∃ (V : Opens (localizedSpaceFunctor.obj X)) (hVU : V ≤ U)
      (t : (etaleRawInducedPointProduct L h ρ M).obj (op ((ι etale ρ).obj (etaleSelf X)))),
      C ⊆ V ∧ closure (V : Set (localizedSpaceFunctor.obj X)) ⊆ U ∧
        IsCompact (closure (V : Set (localizedSpaceFunctor.obj X))) ∧
        t ∈ LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)
          (etaleRawInducedPointProduct L h ρ M) ((ι etale ρ).obj (etaleSelf X)) ∧
        (etaleRawInducedPointProduct L h ρ M).map
            ((ι etale ρ).map (openEtaleToSelf X V)).op t =
          (etaleRawInducedPointProduct L h ρ M).map
            ((ι etale ρ).map (openEtaleMap X (homOfLE hVU))).op s ∧
        (etaleRawInducedPointProduct L h ρ M).map
          ((ι etale ρ).map (openEtaleToSelf X (etaleCutoffOutside V))).op t = 0 := by
  obtain ⟨V, H, hCV, hVU, hVc, hV⟩ :=
    exists_compact_stable_neighbourhood_localizedSpaceAction ρ hρ hC U hCU
  let hVU' : V ≤ U := subset_closure.trans hVU
  obtain ⟨r, hr⟩ :=
    etaleRawInducedPointProduct_open_restriction_surjective L h ρ M U s
  let t := etaleSpatialCutoff L h ρ M V ((ι etale ρ).obj (etaleSelf X)) r
  have htU : (etaleRawInducedPointProduct L h ρ M).map
      ((ι etale ρ).map (openEtaleToSelf X U)).op t ∈
      LocalActionSystem.smoothSubmodule (distinguishedLiftSystem ρ) (twistedEtaleTopology ρ)
        (etaleRawInducedPointProduct L h ρ M) ((ι etale ρ).obj (openEtaleObject X U)) := by
    dsimp only [t]
    rw [etaleSpatialCutoff_restrict L h ρ M V (openEtaleToSelf X U) r, hr]
    exact etaleSpatialCutoff_mem_smoothSubmodule L h ρ M V H hV _ s hs
  have htW : (etaleRawInducedPointProduct L h ρ M).map
      ((ι etale ρ).map (openEtaleToSelf X (etaleCutoffOutside V))).op t = 0 := by
    dsimp only [t]
    rw [etaleSpatialCutoff_restrict L h ρ M V (openEtaleToSelf X (etaleCutoffOutside V)) r]
    exact etaleSpatialCutoff_eq_zero L h ρ M V (etaleCutoffOutside V)
      (Set.disjoint_left.2 fun y hy hyV => hy (subset_closure hyV)) _
  refine ⟨V, hVU', t, hCV, hVU, hVc, ?_, ?_, htW⟩
  · apply mem_smoothSubmodule_of_two_opens.{u, v, uL, z} ρ t U (etaleCutoffOutside V) _ htU
    · rw [htW]
      exact Submodule.zero_mem _
    · intro y
      by_cases hy : y ∈ U
      · exact Or.inl hy
      · exact Or.inr fun hyV => hy (hVU hyV)
  · dsimp only [t]
    rw [etaleSpatialCutoff_restrict L h ρ M V (openEtaleToSelf X V) r,
      etaleSpatialCutoff_eq_self L h ρ M V V subset_rfl]
    have he : openEtaleMap X (homOfLE hVU') ≫ openEtaleToSelf X U =
        openEtaleToSelf X V := by
      apply MorphismProperty.Over.Hom.ext
      apply (cancel_mono (𝟙 X)).1
      exact (MorphismProperty.Over.w
        (openEtaleMap X (homOfLE hVU') ≫ openEtaleToSelf X U)).trans
          (MorphismProperty.Over.w (openEtaleToSelf X V)).symm
    rw [← he, (ι etale ρ).map_comp, map_op_comp_apply, hr]

end Langlands.Sheaf.Equivariant.Analytic

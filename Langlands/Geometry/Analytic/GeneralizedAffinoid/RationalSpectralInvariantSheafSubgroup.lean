import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalSpectralInvariantSheafAction

/-! # Subgroup coherence for the actual invariant rational algebra sheaf action -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Opposite DomainAutomorphism
open Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction
  (openSubgroupInclusion)

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G A)

/-- Identity subgroup change retains the entire sheaf functor. -/
@[simp]
theorem spectralInvariantSheafRestriction_refl (H : OpenSubgroup G)
    (E : Type w) [Category.{w'} E] :
    spectralInvariantSheafRestriction ρ (le_refl H) E =
      𝟭 (Sheaf (SpectralInvariantChart.finiteRationalTopology ρ H) E) := rfl

/-- Nested subgroup changes compose by the same actual sheaf precomposition. -/
@[simp]
theorem spectralInvariantSheafRestriction_comp {H I J : OpenSubgroup G}
    (hHI : H ≤ I) (hIJ : I ≤ J) (E : Type w) [Category.{w'} E] :
    spectralInvariantSheafRestriction ρ hHI E ⋙ spectralInvariantSheafRestriction ρ hIJ E =
      spectralInvariantSheafRestriction ρ (hHI.trans hIJ) E := rfl

/-- Restricting chart indices and acting groups gives identical evaluated actions. -/
@[simp]
theorem spectralInvariantSheafSectionAction_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) :
    spectralInvariantSheafSectionAction ρ H ((spectralInvariantChartRestriction ρ h).obj d) =
      (Action.res (CommAlgCat K) (openSubgroupInclusion h).toMonoidHom).obj
        (spectralInvariantSheafSectionAction ρ J d) := rfl

/-- The original ambient algebra action is unchanged by subgroup restriction. -/
@[simp]
theorem spectralInvariantBaseAlgebraAction_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) :
    spectralInvariantBaseAlgebraAction ρ H =
      (Action.res (CommAlgCat K) (openSubgroupInclusion h).toMonoidHom).obj
        (spectralInvariantBaseAlgebraAction ρ J) := rfl

/-- Both subgroup-change routes retain the entire action on the ordinary sheaf. -/
@[simp]
theorem spectralInvariantSheafAction_subgroup {H J : OpenSubgroup G} (h : H ≤ J) :
    ((spectralInvariantSheafRestriction ρ h (CommAlgCat K)).mapAction H).obj
        (spectralInvariantSheafAction ρ H) =
      (Action.res
        (Sheaf (SpectralInvariantChart.finiteRationalTopology ρ J) (CommAlgCat K))
        (openSubgroupInclusion h).toMonoidHom).obj (spectralInvariantSheafAction ρ J) := rfl

/-- Sheaf precomposition and restriction of the acting group retain the same
ordinary sheaf with the same original section operators. -/
def spectralInvariantSheafActionSubgroupIso {H J : OpenSubgroup G} (h : H ≤ J) :
    ((spectralInvariantSheafRestriction ρ h (CommAlgCat K)).mapAction H).obj
        (spectralInvariantSheafAction ρ H) ≅
      (Action.res
        (Sheaf (SpectralInvariantChart.finiteRationalTopology ρ J) (CommAlgCat K))
        (openSubgroupInclusion h).toMonoidHom).obj (spectralInvariantSheafAction ρ J) :=
  Action.mkIso (ObjectProperty.isoMk _ (Iso.refl _)) (fun g => by
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext d
    rfl)

/-- The comparison is the identity under the equality of the complete actions. -/
@[simp]
theorem spectralInvariantSheafActionSubgroupIso_eqToIso {H J : OpenSubgroup G}
    (h : H ≤ J) :
    spectralInvariantSheafActionSubgroupIso ρ h =
      eqToIso (spectralInvariantSheafAction_subgroup ρ h) := by
  apply Iso.ext
  apply Action.Hom.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  rfl

/-- Changing a subgroup to itself gives the identity comparison isomorphism. -/
@[simp]
theorem spectralInvariantSheafActionSubgroupIso_refl (H : OpenSubgroup G) :
    spectralInvariantSheafActionSubgroupIso ρ (le_refl H) =
      Iso.refl (spectralInvariantSheafAction ρ H) := by
  apply Iso.ext
  apply Action.Hom.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  rfl

/-- For nested subgroups the two mapped comparison isomorphisms compose to the
direct comparison, as isomorphisms of the complete sheaf actions. -/
theorem spectralInvariantSheafActionSubgroupIso_comp {H I J : OpenSubgroup G}
    (hHI : H ≤ I) (hIJ : I ≤ J) :
    ((spectralInvariantSheafRestriction ρ hIJ (CommAlgCat K)).mapAction H).mapIso
        (spectralInvariantSheafActionSubgroupIso ρ hHI) ≪≫
      (Action.res
        (Sheaf (SpectralInvariantChart.finiteRationalTopology ρ J) (CommAlgCat K))
        (openSubgroupInclusion hHI).toMonoidHom).mapIso
          (spectralInvariantSheafActionSubgroupIso ρ hIJ) =
      spectralInvariantSheafActionSubgroupIso ρ (hHI.trans hIJ) := by
  apply Iso.ext
  apply Action.Hom.ext
  apply Sheaf.hom_ext
  apply NatTrans.ext
  funext d
  rfl

@[simp]
theorem spectralInvariantSheafActionSubgroupIso_hom_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) (a : d.obj.algebra) :
    (((spectralInvariantSheafActionSubgroupIso ρ h).hom.hom).hom.app (op d)).hom a = a := rfl

@[simp]
theorem spectralInvariantSheafActionSubgroupIso_inv_apply {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) (a : d.obj.algebra) :
    (((spectralInvariantSheafActionSubgroupIso ρ h).inv.hom).hom.app (op d)).hom a = a := rfl

/-- Every original equivariant restriction is retained by subgroup change. -/
@[simp]
theorem spectralInvariantSheafSectionRestriction_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) {d e : SpectralInvariantChart ρ J} (f : d ⟶ e) :
    spectralInvariantSheafSectionRestriction ρ H ((spectralInvariantChartRestriction ρ h).map f) =
      (Action.res (CommAlgCat K) (openSubgroupInclusion h).toMonoidHom).map
        (spectralInvariantSheafSectionRestriction ρ J f) := rfl

/-- The particular whole-section identification is retained in both directions. -/
@[simp]
theorem spectralInvariantWholeSectionIso_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) :
    spectralInvariantWholeSectionIso ρ H =
      (Action.res (CommAlgCat K) (openSubgroupInclusion h).toMonoidHom).mapIso
        (spectralInvariantWholeSectionIso ρ J) := rfl

/-- Subgroup change retains the entire equivariant structural homomorphism. -/
@[simp]
theorem spectralInvariantSheafBaseMap_subgroup {H J : OpenSubgroup G}
    (h : H ≤ J) (d : SpectralInvariantChart ρ J) :
    spectralInvariantSheafBaseMap ρ H ((spectralInvariantChartRestriction ρ h).obj d) =
      (Action.res (CommAlgCat K) (openSubgroupInclusion h).toMonoidHom).map
        (spectralInvariantSheafBaseMap ρ J d) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

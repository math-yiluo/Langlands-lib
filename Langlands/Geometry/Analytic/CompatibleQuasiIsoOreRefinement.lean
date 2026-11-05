import Langlands.Geometry.Analytic.CompatibleQuasiIsoReverseIdentities

/-! # Actual Ore refinements along compatible quasi-isomorphisms -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open CategoryTheory Set IndexedAffinoidAtlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace AffinoidAtlasPresentation

namespace StrongHom

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

/-- Subordinate source selections are downward closed for every target selection. -/
theorem sourceSelectionForTarget_downward (f : StrongHom A B)
    (P : B.atlas.Index → Prop) :
    A.atlas.IsDownwardClosedSelection (f.sourceSelectionForTarget P) := by
  intro i i' hi
  rintro ⟨j, hPj, hj⟩
  exact ⟨j, hPj, (Set.image_mono hi).trans hj⟩

/-- The constructed subordinate source retains all actual local domains. -/
theorem targetSubatlasSource_hasAllLocalDomains (f : StrongHom A B)
    (ha : A.atlas.HasAllLocalDomains) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P) :
    (f.targetSubatlasSource ha P hP).atlas.HasAllLocalDomains :=
  A.atlas.subatlas_hasAllLocalDomains ha (f.sourceSelectionForTarget P)
    (f.sourceSelectionForTarget_locallyRefining ha P hP)
    (f.sourceSelectionForTarget_downward P)

end StrongHom

namespace CompatibleStrongHom

variable {A B C : AffinoidAtlasPresentation.{u, v, w} K}

/-- Refine the original source so that its image charts lie in the constructed
reverse target selection of the given full quasi-isomorphism. -/
def quasiIsoOreSource (f : CompatibleStrongHom A C) (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hc : C.atlas.HasAllLocalDomains) : AffinoidAtlasPresentation.{u, v, w} K :=
  f.toStrongHom.targetSubatlasSource ha hs.reverseChartSelection
    (hs.reverseChartSelection_locallyRefining hc)

/-- The new source is full-domain closed by the proved downward-selection law. -/
theorem quasiIsoOreSource_hasAllLocalDomains (f : CompatibleStrongHom A C)
    (s : CompatibleStrongHom B C) (hs : s.toStrongHom.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreSource s hs ha hc).atlas.HasAllLocalDomains :=
  f.toStrongHom.targetSubatlasSource_hasAllLocalDomains ha hs.reverseChartSelection
    (hs.reverseChartSelection_locallyRefining hc)

/-- The full quasi-isomorphism into the original source uses exactly the
original bounded restrictions and the identity ambient map. -/
def quasiIsoOreInclusion (f : CompatibleStrongHom A C) (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hc : C.atlas.HasAllLocalDomains) :
    CompatibleStrongHom (f.quasiIsoOreSource s hs ha hc) A :=
  A.compatibleSubatlasInclusion (f.toStrongHom.sourceSelectionForTarget hs.reverseChartSelection)
    (f.toStrongHom.sourceSelectionForTarget_locallyRefining ha hs.reverseChartSelection
      (hs.reverseChartSelection_locallyRefining hc))

theorem isQuasiIso_quasiIsoOreInclusion (f : CompatibleStrongHom A C)
    (s : CompatibleStrongHom B C) (hs : s.toStrongHom.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreInclusion s hs ha hc).toStrongHom.IsQuasiIso :=
  A.isQuasiIso_compatibleSubatlasInclusion _ _

@[simp]
theorem quasiIsoOreInclusion_baseMap (f : CompatibleStrongHom A C)
    (s : CompatibleStrongHom B C) (hs : s.toStrongHom.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreInclusion s hs ha hc).baseMap = ContinuousMap.id A.space := rfl

/-- Compose the actual subordinate forward lift with the constructed reverse
map. Every admissible bounded pullback is retained by compatible composition. -/
def quasiIsoOreLift (f : CompatibleStrongHom A C) (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hc : C.atlas.HasAllLocalDomains) :
    CompatibleStrongHom (f.quasiIsoOreSource s hs ha hc) B :=
  (f.targetSubatlasLift ha hs.reverseChartSelection
    (hs.reverseChartSelection_locallyRefining hc)).comp
      (hs.reverseCompatibleStrongMap s.coherent hc)

@[simp]
theorem quasiIsoOreLift_baseMap (f : CompatibleStrongHom A C)
    (s : CompatibleStrongHom B C) (hs : s.toStrongHom.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreLift s hs ha hc).baseMap = hs.inverseBaseMap.comp f.baseMap := rfl

/-- The complete Ore square commutes, including the full bounded pullback families. -/
theorem quasiIsoOre_square (f : CompatibleStrongHom A C) (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreLift s hs ha hc).comp s =
      (f.quasiIsoOreInclusion s hs ha hc).comp f := by
  let L := f.targetSubatlasLift ha hs.reverseChartSelection
    (hs.reverseChartSelection_locallyRefining hc)
  let r := hs.reverseCompatibleStrongMap s.coherent hc
  exact (comp_assoc L r s).trans
    ((congrArg (fun g : CompatibleStrongHom (hs.reverseSubpresentation hc) C => L.comp g)
      (s.reverse_comp hs hc)).trans
        (f.targetSubatlasLift_square ha hs.reverseChartSelection
          (hs.reverseChartSelection_locallyRefining hc)))

/-- Full quasi-isomorphisms also remain full quasi-isomorphisms in the lifted leg. -/
theorem isQuasiIso_quasiIsoOreLift (f : CompatibleStrongHom A C)
    (hf : f.toStrongHom.IsQuasiIso) (s : CompatibleStrongHom B C)
    (hs : s.toStrongHom.IsQuasiIso) (ha : A.atlas.HasAllLocalDomains)
    (hc : C.atlas.HasAllLocalDomains) :
    (f.quasiIsoOreLift s hs ha hc).toStrongHom.IsQuasiIso :=
  isQuasiIso_comp (f.isQuasiIso_targetSubatlasLift hf ha hs.reverseChartSelection
    (hs.reverseChartSelection_locallyRefining hc))
      (hs.reverseStrongMap_isQuasiIso s.coherent hc)

/-- On the constructed source refinement, the full compatible lifted arrow is unique. -/
theorem quasiIsoOreLift_unique (f : CompatibleStrongHom A C)
    (s : CompatibleStrongHom B C) (hs : s.toStrongHom.IsQuasiIso)
    (ha : A.atlas.HasAllLocalDomains) (hc : C.atlas.HasAllLocalDomains)
    (g : CompatibleStrongHom (f.quasiIsoOreSource s hs ha hc) B)
    (hg : g.comp s = (f.quasiIsoOreInclusion s hs ha hc).comp f) :
    g = f.quasiIsoOreLift s hs ha hc :=
  cancel_comp hs (hg.trans (f.quasiIsoOre_square s hs ha hc).symm)

end CompatibleStrongHom
end AffinoidAtlasPresentation

namespace CompatibleAtlasPresentation

variable {A B C : CompatibleAtlasPresentation.{u, v, w} K}

/-- The constructed Ore square lives in the actual compatible morphism category. -/
theorem quasiIsoOre_commSq (f : A ⟶ C) (s : B ⟶ C)
    (hs : quasiIsomorphisms s) (ha : A.presentation.atlas.HasAllLocalDomains)
    (hc : C.presentation.atlas.HasAllLocalDomains) :
    CommSq (C := CompatibleAtlasPresentation.{u, v, w} K)
      (show (⟨f.quasiIsoOreSource s hs ha hc⟩ : CompatibleAtlasPresentation.{u, v, w} K) ⟶ B
        from f.quasiIsoOreLift s hs ha hc)
      (f.quasiIsoOreInclusion s hs ha hc) s f :=
  ⟨f.quasiIsoOre_square s hs ha hc⟩

end CompatibleAtlasPresentation
end Langlands.Analytic

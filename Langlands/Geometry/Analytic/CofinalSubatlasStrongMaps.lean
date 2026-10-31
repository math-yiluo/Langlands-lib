import Langlands.Geometry.Analytic.StrongAtlasQuasiIsomorphisms
import Langlands.Geometry.Analytic.DirectedAtlasComposition

/-! # Strong inverse maps for upper-cofinal original subatlases -/

noncomputable section

universe u v w

namespace Langlands.Analytic

open Set Topology CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

namespace IndexedAffinoidAtlas

variable {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)

/-- Every original chart lies in a selected original chart. This is separate
from the relative finite local witnesses making the selection an atlas. -/
def IsUpperCofinalSelection (P : a.Index → Prop) : Prop :=
  ∀ i : a.Index, ∃ j : {j : a.Index // P j},
    Set.range (a.chart i) ⊆ Set.range (a.chart j.val)

/-- Upper cofinality transfers directedness to the actual selected charts. -/
theorem hasDirectedCharts_subatlas (P : a.Index → Prop)
    (hP : a.IsLocallyRefiningSelection P) (hd : a.HasDirectedCharts)
    (hc : a.IsUpperCofinalSelection P) :
    (a.subatlas P hP).HasDirectedCharts := by
  intro i j
  obtain ⟨q, hiq, hjq⟩ := hd i.val j.val
  obtain ⟨r, hqr⟩ := hc q
  exact ⟨r, hiq.trans hqr, hjq.trans hqr⟩

end IndexedAffinoidAtlas

namespace AffinoidAtlasPresentation

variable {A B : AffinoidAtlasPresentation.{u, v, w} K}

namespace StrongHom

/-- Retain all original bounded pullbacks with selected target indices.
Upper cofinality constructs containing target witnesses for each source chart. -/
def restrictCofinalSubatlasTarget (f : StrongHom A B) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P)
    (hc : B.atlas.IsUpperCofinalSelection P) :
    StrongHom A (B.subpresentation P hP) where
  baseMap := f.baseMap
  target_exists i := by
    obtain ⟨j, hij⟩ := f.target_exists i
    obtain ⟨q, hjq⟩ := hc j
    exact ⟨q, hij.trans hjq⟩
  pullback i j h := f.pullback i j.val h
  chart_comm i j h x := f.chart_comm i j.val h x
  restriction_comm i i' j j' hi hj h h' :=
    f.restriction_comm i i' j.val j'.val hi hj h h'

@[simp]
theorem restrictCofinalSubatlasTarget_baseMap (f : StrongHom A B)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P)
    (hc : B.atlas.IsUpperCofinalSelection P) :
    (f.restrictCofinalSubatlasTarget P hP hc).baseMap = f.baseMap := rfl

@[simp]
theorem restrictCofinalSubatlasTarget_pullback (f : StrongHom A B)
    (P : B.atlas.Index → Prop) (hP : B.atlas.IsLocallyRefiningSelection P)
    (hc : B.atlas.IsUpperCofinalSelection P) (i : A.atlas.Index)
    (j : (B.subpresentation P hP).atlas.Index)
    (h : f.baseMap '' Set.range (A.atlas.chart i) ⊆
      Set.range (B.atlas.chart j.val)) :
    (f.restrictCofinalSubatlasTarget P hP hc).pullback i j h =
      f.pullback i j.val h := rfl

theorem IsQuasiIso.restrictCofinalSubatlasTarget {f : StrongHom A B}
    (hf : f.IsQuasiIso) (P : B.atlas.Index → Prop)
    (hP : B.atlas.IsLocallyRefiningSelection P)
    (hc : B.atlas.IsUpperCofinalSelection P) :
    (f.restrictCofinalSubatlasTarget P hP hc).IsQuasiIso :=
  ⟨hf.1, fun i j h => hf.2 i j.val h⟩

/-- Source and upper-cofinal target selection commute as full strong maps. -/
theorem restrictSubatlasSource_restrictCofinalSubatlasTarget (f : StrongHom A B)
    (P : A.atlas.Index → Prop) (hP : A.atlas.IsLocallyRefiningSelection P)
    (Q : B.atlas.Index → Prop) (hQ : B.atlas.IsLocallyRefiningSelection Q)
    (hc : B.atlas.IsUpperCofinalSelection Q) :
    (f.restrictSubatlasSource P hP).restrictCofinalSubatlasTarget Q hQ hc =
      (f.restrictCofinalSubatlasTarget Q hQ hc).restrictSubatlasSource P hP :=
  StrongHom.ext rfl (heq_of_eq (by funext i j h; rfl))

end StrongHom

variable (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The reverse full strong arrow to an upper-cofinal locally refining subatlas
uses only the original atlas restrictions, without a monotone chosen selection. -/
def strongCofinalSubatlasMap (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) :
    StrongHom A (A.subpresentation P hP) :=
  (StrongHom.id A).restrictCofinalSubatlasTarget P hP hc

@[simp]
theorem strongCofinalSubatlasMap_baseMap (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) :
    (A.strongCofinalSubatlasMap P hP hc).baseMap = ContinuousMap.id A.space := rfl

@[simp]
theorem strongCofinalSubatlasMap_pullback (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) (i : A.atlas.Index)
    (j : (A.subpresentation P hP).atlas.Index)
    (h : (A.strongCofinalSubatlasMap P hP hc).baseMap ''
      Set.range (A.atlas.chart i) ⊆
        Set.range ((A.subpresentation P hP).atlas.chart j)) :
    (A.strongCofinalSubatlasMap P hP hc).pullback i j h =
      A.atlas.restriction i j.val (fun x hx => h ⟨x, hx, rfl⟩) := rfl

theorem isQuasiIso_strongCofinalSubatlasMap (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) :
    (A.strongCofinalSubatlasMap P hP hc).IsQuasiIso :=
  (StrongHom.isQuasiIso_id A).restrictCofinalSubatlasTarget P hP hc

/-- The inclusion followed by the reverse arrow is the complete strong identity. -/
theorem strongSubatlasInclusion_comp_cofinal (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) (hd : A.atlas.HasDirectedCharts) :
    (A.strongSubatlasInclusion P hP).compOfDirected
      (A.strongCofinalSubatlasMap P hP hc) hd
        (A.atlas.hasDirectedCharts_subatlas P hP hd hc) =
      StrongHom.id (A.subpresentation P hP) := by
  let hdP := A.atlas.hasDirectedCharts_subatlas P hP hd hc
  refine StrongHom.ext_of_directed
    (f := (A.strongSubatlasInclusion P hP).compOfDirected
      (A.strongCofinalSubatlasMap P hP hc) hd hdP)
    (g := StrongHom.id (A.subpresentation P hP)) hdP rfl ?_
  intro i
  have hf : (A.strongSubatlasInclusion P hP).baseMap ''
      Set.range ((A.subpresentation P hP).atlas.chart i) ⊆
        Set.range (A.atlas.chart i.val) :=
    fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx
  have hg : (A.strongCofinalSubatlasMap P hP hc).baseMap ''
      Set.range (A.atlas.chart i.val) ⊆
        Set.range ((A.subpresentation P hP).atlas.chart i) :=
    fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx
  have h := (A.strongSubatlasInclusion P hP).comp_admissible
    (A.strongCofinalSubatlasMap P hP hc) i i.val i hf hg
  refine ⟨i, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback _ _ hd hdP i i.val i hf hg h]
  change (A.atlas.restriction i.val i.val _).comp
      (A.atlas.restriction i.val i.val _) = A.atlas.restriction i.val i.val _
  exact (A.atlas.restriction_comp i.val i.val i.val _ _ _).symm

/-- A cofinal selected containing chart detects each original source chart,
so the reverse arrow followed by inclusion is the full strong identity. -/
theorem strongCofinalSubatlasMap_comp_inclusion (P : A.atlas.Index → Prop)
    (hP : A.atlas.IsLocallyRefiningSelection P)
    (hc : A.atlas.IsUpperCofinalSelection P) (hd : A.atlas.HasDirectedCharts) :
    (A.strongCofinalSubatlasMap P hP hc).compOfDirected
      (A.strongSubatlasInclusion P hP)
        (A.atlas.hasDirectedCharts_subatlas P hP hd hc) hd = StrongHom.id A := by
  let hdP := A.atlas.hasDirectedCharts_subatlas P hP hd hc
  refine StrongHom.ext_of_directed
    (f := (A.strongCofinalSubatlasMap P hP hc).compOfDirected
      (A.strongSubatlasInclusion P hP) hdP hd)
    (g := StrongHom.id A) hd rfl ?_
  intro i
  obtain ⟨j, hij⟩ := hc i
  have hf : (A.strongCofinalSubatlasMap P hP hc).baseMap ''
      Set.range (A.atlas.chart i) ⊆
        Set.range ((A.subpresentation P hP).atlas.chart j) :=
    fun _ ⟨x, hx, hxy⟩ => hxy ▸ hij hx
  have hg : (A.strongSubatlasInclusion P hP).baseMap ''
      Set.range ((A.subpresentation P hP).atlas.chart j) ⊆
        Set.range (A.atlas.chart j.val) :=
    fun _ ⟨x, hx, hxy⟩ => hxy ▸ hx
  have h := (A.strongCofinalSubatlasMap P hP hc).comp_admissible
    (A.strongSubatlasInclusion P hP) i j j.val hf hg
  refine ⟨j.val, h, ?_⟩
  rw [StrongHom.compOfDirected_pullback _ _ hdP hd i j j.val hf hg h]
  change (A.atlas.restriction i j.val _).comp
      (A.atlas.restriction j.val j.val _) = A.atlas.restriction i j.val _
  rw [A.atlas.restriction_id, BoundedAlgHom.comp_id]

end AffinoidAtlasPresentation

namespace DirectedAtlasPresentation

variable (A : DirectedAtlasPresentation.{u, v, w} K)

/-- The original selected presentation with its proved directedness. -/
def cofinalSubpresentation (P : A.presentation.atlas.Index → Prop)
    (hP : A.presentation.atlas.IsLocallyRefiningSelection P)
    (hc : A.presentation.atlas.IsUpperCofinalSelection P) :
    DirectedAtlasPresentation.{u, v, w} K where
  presentation := A.presentation.subpresentation P hP
  directed := A.presentation.atlas.hasDirectedCharts_subatlas P hP A.directed hc

/-- An actual isomorphism of full directed strong-map presentations. -/
def cofinalSubatlasIso (P : A.presentation.atlas.Index → Prop)
    (hP : A.presentation.atlas.IsLocallyRefiningSelection P)
    (hc : A.presentation.atlas.IsUpperCofinalSelection P) :
    A.cofinalSubpresentation P hP hc ≅ A where
  hom := A.presentation.strongSubatlasInclusion P hP
  inv := A.presentation.strongCofinalSubatlasMap P hP hc
  hom_inv_id := A.presentation.strongSubatlasInclusion_comp_cofinal P hP hc A.directed
  inv_hom_id := A.presentation.strongCofinalSubatlasMap_comp_inclusion P hP hc A.directed

/-- The isomorphism retains exactly the original topological space and identity. -/
theorem spaceFunctor_mapIso_cofinalSubatlasIso (P : A.presentation.atlas.Index → Prop)
    (hP : A.presentation.atlas.IsLocallyRefiningSelection P)
    (hc : A.presentation.atlas.IsUpperCofinalSelection P) :
    (spaceFunctor (K := K)).mapIso (A.cofinalSubatlasIso P hP hc) =
      Iso.refl A.presentation.space := rfl

end DirectedAtlasPresentation

end Langlands.Analytic

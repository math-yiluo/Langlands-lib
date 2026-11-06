import Langlands.Geometry.Analytic.SubatlasDomainRecognition
import Langlands.Geometry.Analytic.FullRecognitionNaturality

/-! # Full bounded naturality of selected-atlas domain recognition -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] (a : IndexedAffinoidAtlas.{u, v, w} K X)
  {P : a.Index → Prop} (hP : a.IsLocallyRefiningSelection P)

namespace SelectedChartCover

variable {a} {parent : a.Index} (c : a.SelectedChartCover P parent)
  (U : Domain K (a.algebra parent))

/-- The realized section restriction to every contained selected-saturation
chart is its complete canonical original local-domain inclusion map. -/
theorem saturatedDomain_originalRestriction
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆
      (⟨parent, U⟩ : LocalDomain a).locus) :
    let d := c.saturatedDomainGluing hP U
    let r := c.saturatedDomainAffinoidRealization hP U
    letI : T2Space d.locus := r.locusHomeomorph.symm.t2Space
    (d.originalRestriction s
      (hs.trans (c.saturatedDomainGluing_locus hP U).symm.subset)).comp
        r.restrictFromParent =
      (a.subatlasSaturatedComponent P hP ⟨parent, U⟩ s hs).baseMap := by
  let b := a.subatlas P hP
  let d := c.saturatedDomainGluing hP U
  let r := c.saturatedDomainAffinoidRealization hP U
  let : T2Space d.locus := r.locusHomeomorph.symm.t2Space
  let hs' := hs.trans (c.saturatedDomainGluing_locus hP U).symm.subset
  let C := d.subordinateCoverOfHausdorff s hs'
  ext x
  apply C.domainCover.algebra_ext_of_restrict_eq
  intro t
  have hd := d.original_comp_originalRestriction s hs' (C.index t)
    (C.subset_parent t) (C.member t) (C.subset_member t)
  have hp := a.subatlasSaturatedComponent_naturality P hP ⟨parent, U⟩ (C.index t) s
    ((C.subset_parent t).trans hs) hs (C.subset_parent t)
  have hm := a.subatlasSaturatedComponent_naturality P hP ⟨parent, U⟩
    (C.index t) (d.index (C.member t)) ((C.subset_parent t).trans hs)
    (c.saturatedDomainIndex_subset hP U (C.member t)) (C.subset_member t)
  exact (congrArg
    (fun q : BoundedAlgHom K d.SectionAlgebra (b.saturatedAtlas.algebra (C.index t)) =>
      q (r.restrictFromParent x)) hd).trans
        ((congrArg
          (fun q : BoundedAlgHom K U.algebra (b.saturatedAtlas.algebra (C.index t)) =>
            q x) hm).trans
              (congrArg
                (fun q : BoundedAlgHom K U.algebra
                  (b.saturatedAtlas.algebra (C.index t)) => q x) hp).symm)

/-- The constructed recognized presentation recovers every contained
selected-saturation chart restriction on its entire algebra. -/
theorem saturatedDomainAlgebraEquiv_originalRestriction
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆
      (⟨parent, U⟩ : LocalDomain a).locus) :
    ((c.saturatedDomainRecognizedSubset hP U).originalRestriction s hs).comp
        (c.saturatedDomainAlgebraEquiv hP U).toBoundedAlgHom =
      (a.subatlasSaturatedComponent P hP ⟨parent, U⟩ s hs).baseMap := by
  let d := c.saturatedDomainGluing hP U
  let r := c.saturatedDomainAffinoidRealization hP U
  let : T2Space d.locus := r.locusHomeomorph.symm.t2Space
  exact ((c.saturatedDomainRecognizedSubset hP U).originalRestriction_comp_affinoidRealization
    d (c.saturatedDomainGluing_locus hP U) r s hs).trans
      (c.saturatedDomain_originalRestriction hP U s hs)

end SelectedChartCover

/-- Canonical relative components commute with every actual old local-domain
inclusion, by uniqueness of its entire bounded composite. -/
theorem subatlasSaturatedComponent_comp_restriction
    {U V : LocalDomain a} (f : U ⟶ V)
    (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ U.locus) :
    (a.subatlasSaturatedComponent P hP U s hs).baseMap.comp f.restriction =
      (a.subatlasSaturatedComponent P hP V s (hs.trans f.subset)).baseMap :=
  congrArg LocalDomain.Inclusion.restriction
    (@Subsingleton.elim (LocalDomain.Inclusion
      (a.subatlasLocalDomain P hP ((a.subatlas P hP).saturatedRepresentative s)) V)
      inferInstance (a.subatlasSaturatedInclusion P hP U s hs ≫ f)
        (a.subatlasSaturatedInclusion P hP V s (hs.trans f.subset)))

theorem subatlasRecognizedLocalDomainEquiv_originalRestriction
    (U : LocalDomain a) (s : (a.subatlas P hP).saturatedAtlas.Index)
    (hs : Set.range ((a.subatlas P hP).saturatedAtlas.chart s) ⊆ U.locus) :
    ((a.subatlasRecognizedLocalDomain hP U).originalRestriction s hs).comp
        (a.subatlasRecognizedLocalDomainEquiv hP U).toBoundedAlgHom =
      (a.subatlasSaturatedComponent P hP U s hs).baseMap :=
  (a.selectedChartCover P hP U.index).saturatedDomainAlgebraEquiv_originalRestriction
    hP U.domain s hs

/-- The domain recognition comparisons intertwine all actual bounded
restrictions, including their information on nilpotent elements. -/
theorem subatlasRecognizedLocalDomainEquiv_naturality
    {U V : LocalDomain a} (f : U ⟶ V) :
    (a.subatlasRecognizedLocalDomainEquiv hP U).toBoundedAlgHom.comp f.restriction =
      ((a.subatlasRecognizedLocalDomain hP U).restriction
        (a.subatlasRecognizedLocalDomain hP V) f.subset).comp
          (a.subatlasRecognizedLocalDomainEquiv hP V).toBoundedAlgHom := by
  let b := a.subatlas P hP
  let Y := a.subatlasRecognizedLocalDomain hP U
  let Z := a.subatlasRecognizedLocalDomain hP V
  ext x
  apply Y.componentCover.algebra_ext_of_restrict_eq
  intro i
  change (Y.property.componentDomain i).baseMap
      ((a.subatlasRecognizedLocalDomainEquiv hP U) (f.restriction x)) =
    (Y.property.componentDomain i).baseMap
      (Y.restriction Z f.subset ((a.subatlasRecognizedLocalDomainEquiv hP V) x))
  have hD := Y.componentDomain_baseMap i
  apply (congrArg
    (fun q : BoundedAlgHom K Y.algebra (b.saturatedAtlas.algebra (Y.property.cover.index i)) =>
      q ((a.subatlasRecognizedLocalDomainEquiv hP U) (f.restriction x))) hD).trans
  apply Eq.trans _ (congrArg
    (fun q : BoundedAlgHom K Y.algebra (b.saturatedAtlas.algebra (Y.property.cover.index i)) =>
      q (Y.restriction Z f.subset ((a.subatlasRecognizedLocalDomainEquiv hP V) x))) hD).symm
  have hU := a.subatlasRecognizedLocalDomainEquiv_originalRestriction hP U
    (Y.property.cover.index i) (Y.component_subset i)
  have hV := a.subatlasRecognizedLocalDomainEquiv_originalRestriction hP V
    (Y.property.cover.index i) ((Y.component_subset i).trans f.subset)
  have hO := a.subatlasSaturatedComponent_comp_restriction hP f
    (Y.property.cover.index i) (Y.component_subset i)
  have hY := Y.originalRestriction_comp_restriction Z f.subset
    (Y.property.cover.index i) (Y.component_subset i)
  exact (congrArg
    (fun q : BoundedAlgHom K U.algebra (b.saturatedAtlas.algebra (Y.property.cover.index i)) =>
      q (f.restriction x)) hU).trans
        ((congrArg
          (fun q : BoundedAlgHom K V.algebra
            (b.saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hO).trans
          ((congrArg
            (fun q : BoundedAlgHom K V.algebra
              (b.saturatedAtlas.algebra (Y.property.cover.index i)) => q x) hV).symm.trans
            (congrArg
              (fun q : BoundedAlgHom K Z.algebra
                (b.saturatedAtlas.algebra (Y.property.cover.index i)) =>
                  q ((a.subatlasRecognizedLocalDomainEquiv hP V) x)) hY).symm))

/-- Every actual original local domain has a constructed recognized selected
presentation, and literal containment supplies its actual recognized arrow. -/
def subatlasLocalDomainRecognitionFunctor :
    LocalDomain a ⥤ (a.subatlas P hP).saturatedAtlas.RecognizedSubset where
  obj := a.subatlasRecognizedLocalDomain hP
  map f := ⟨f.subset⟩
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Actual mutually inverse bounded maps compare each diagram object. -/
def subatlasLocalDomainRecognitionAffinoidIso (U : LocalDomain a) :
    Opposite.op (a.subatlasRecognizedLocalDomain hP U).algebra ≅ Opposite.op U.algebra where
  hom := Quiver.Hom.op
    (show U.algebra ⟶ (a.subatlasRecognizedLocalDomain hP U).algebra from
      (a.subatlasRecognizedLocalDomainEquiv hP U).toBoundedAlgHom)
  inv := Quiver.Hom.op
    (show (a.subatlasRecognizedLocalDomain hP U).algebra ⟶ U.algebra from
      (a.subatlasRecognizedLocalDomainEquiv hP U).symm.toBoundedAlgHom)
  hom_inv_id := congrArg
    (fun q : (a.subatlasRecognizedLocalDomain hP U).algebra ⟶
      (a.subatlasRecognizedLocalDomain hP U).algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (a.subatlasRecognizedLocalDomainEquiv hP U).apply_symm_apply x)
  inv_hom_id := congrArg (fun q : U.algebra ⟶ U.algebra => Quiver.Hom.op q)
    (BoundedAlgHom.ext fun x => (a.subatlasRecognizedLocalDomainEquiv hP U).symm_apply_apply x)

/-- The constructed recognized diagram is naturally isomorphic to the whole
original affinoid diagram, by full bounded restriction naturality. -/
def subatlasLocalDomainRecognitionAffinoidNatIso :
    a.subatlasLocalDomainRecognitionFunctor hP ⋙
        RecognizedSubset.toAffinoidSpace (a.subatlas P hP).saturatedAtlas ≅
      LocalDomain.toAffinoidSpace a :=
  NatIso.ofComponents (a.subatlasLocalDomainRecognitionAffinoidIso hP) (by
    intro U V f
    exact congrArg
      (fun q : V.algebra ⟶ (a.subatlasRecognizedLocalDomain hP U).algebra =>
        Quiver.Hom.op q)
      (a.subatlasRecognizedLocalDomainEquiv_naturality hP f).symm)

theorem subatlasLocalDomainRecognitionAffinoidNatIso_over_ambient (U : LocalDomain a)
    (x : BanachSpectrum (a.subatlasRecognizedLocalDomain hP U).algebra) :
    U.ambientMap ((affinoidSpectrumFunctor K).map
        ((a.subatlasLocalDomainRecognitionAffinoidNatIso hP).hom.app U) x) =
      (a.subatlasRecognizedLocalDomain hP U).chart x :=
  (a.subatlasRecognizedLocalDomain_chart hP U x).symm

end Langlands.Analytic.IndexedAffinoidAtlas

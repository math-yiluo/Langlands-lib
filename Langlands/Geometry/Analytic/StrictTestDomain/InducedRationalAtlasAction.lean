import Langlands.Geometry.Analytic.StrictTestDomain.InducedRationalAtlasTransport
import Langlands.Geometry.Analytic.GeneralizedAffinoid.StrictComparisonFunctor
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Bounded full-group action on the actual induced affinoid atlas -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

variable (X : ρ.OpenSubgroupTransport)

/-- The subgroup correction comparing the chosen representatives of c and g • c. -/
def actionChartElement (g : G) (c : G ⧸ X.subgroup.toSubgroup) : X.subgroup :=
  ⟨(g • c).out⁻¹ * (g * c.out), by
    apply QuotientGroup.eq.mp
    rw [QuotientGroup.out_eq']
    exact (MulAction.Quotient.coe_smul_out X.subgroup.toSubgroup g c).symm⟩

@[simp]
theorem actionChartElement_coe (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    (X.actionChartElement g c : G) = (g • c).out⁻¹ * (g * c.out) := rfl

theorem actionChartElement_spec (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    g * c.out = (g • c).out * (X.actionChartElement g c : G) := by
  simp

@[simp]
theorem actionChartElement_one (c : G ⧸ X.subgroup.toSubgroup) :
    X.actionChartElement 1 c = 1 := by
  apply Subtype.ext
  simp

/-- The representative correction is a cocycle with values in the stored subgroup. -/
theorem actionChartElement_mul (g h : G) (c : G ⧸ X.subgroup.toSubgroup) :
    X.actionChartElement (g * h) c =
      X.actionChartElement g (h • c) * X.actionChartElement h c := by
  apply Subtype.ext
  simp [mul_smul, mul_assoc]

/-- The point action uses the inverse of the forward bounded section operator. -/
def strictActionPullback (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    BoundedAlgHom K X.domain.obj.algebra X.domain.obj.algebra :=
  ((X.chartSectionAction (X.actionChartElement g c))⁻¹).hom

@[simp]
theorem strictActionPullback_one (c : G ⧸ X.subgroup.toSubgroup) :
    X.strictActionPullback 1 c = BoundedAlgHom.id K X.domain.obj.algebra := by
  simp only [strictActionPullback, actionChartElement_one, map_one]
  rfl

/-- Pullbacks reverse the order of the two point actions. -/
theorem strictActionPullback_mul (g h : G) (c : G ⧸ X.subgroup.toSubgroup) :
    X.strictActionPullback (g * h) c =
      (X.strictActionPullback h c).comp (X.strictActionPullback g (h • c)) := by
  unfold strictActionPullback
  rw [actionChartElement_mul, map_mul, mul_inv_rev]
  rfl

/-- Apply the published radius-one quotient comparison to the actual strict pullback. -/
def affinoidActionPullback (g : G) (c : G ⧸ X.subgroup.toSubgroup) :
    BoundedAlgHom K X.inducedChartAlgebra X.inducedChartAlgebra :=
  PresentedAffinoidAlgebra.ofStrictMap K (X.strictActionPullback g c)

@[simp]
theorem affinoidActionPullback_one (c : G ⧸ X.subgroup.toSubgroup) :
    X.affinoidActionPullback 1 c = BoundedAlgHom.id K X.inducedChartAlgebra := by
  unfold affinoidActionPullback
  rw [strictActionPullback_one]
  exact (PresentedAffinoidAlgebra.ofStrictFunctor K).map_id X.domain.obj.algebra

theorem affinoidActionPullback_mul (g h : G) (c : G ⧸ X.subgroup.toSubgroup) :
    X.affinoidActionPullback (g * h) c =
      (X.affinoidActionPullback h c).comp (X.affinoidActionPullback g (h • c)) := by
  unfold affinoidActionPullback
  rw [strictActionPullback_mul]
  exact (PresentedAffinoidAlgebra.ofStrictFunctor K).map_comp
    (X.strictActionPullback g (h • c)) (X.strictActionPullback h c)

/-- The actual bounded endomorphism uses left translation of cosets and its correction. -/
def affinoidActionMap (g : G) : X.inducedAffinoidObject ⟶ X.inducedAffinoidObject where
  indexMap := fun c : G ⧸ X.subgroup.toSubgroup => g • c
  pullback := X.affinoidActionPullback g

@[simp]
theorem affinoidActionMap_one :
    X.affinoidActionMap 1 = 𝟙 X.inducedAffinoidObject := by
  apply AffinoidFamily.Hom.ext
    (funext (fun c : G ⧸ X.subgroup.toSubgroup => one_smul G c))
  exact heq_of_eq (funext (X.affinoidActionPullback_one))

theorem affinoidActionMap_mul (g h : G) :
    X.affinoidActionMap (g * h) = X.affinoidActionMap h ≫ X.affinoidActionMap g := by
  apply AffinoidFamily.Hom.ext
    (funext (fun c : G ⧸ X.subgroup.toSubgroup => mul_smul g h c))
  exact heq_of_eq (funext (X.affinoidActionPullback_mul g h))

/-- A full-group action by constructed bounded morphisms of actual quotient families. -/
def inducedAffinoidAction : Action (AffinoidFamily.{u, v} K) G where
  V := X.inducedAffinoidObject
  ρ :=
    { toFun := X.affinoidActionMap
      map_one' := X.affinoidActionMap_one
      map_mul' := X.affinoidActionMap_mul }

/-- The inverse morphism is the map of the inverse group element. -/
def inducedAffinoidAutomorphisms : G →* Aut X.inducedAffinoidObject :=
  X.inducedAffinoidAction.ρAut

/-- The strict bounded pullback realizes the actual subgroup action on seminorms. -/
theorem strictActionPullback_spectrum (g : G) (c : G ⧸ X.subgroup.toSubgroup)
    (x : X.LocalSpectrum) :
    BanachSpectrum.comap (X.strictActionPullback g c).toBoundedRingHom x =
      X.actionChartElement g c • x := rfl

/-- The quotient comparison intertwines the generalized and strict action maps. -/
theorem affinoidActionPullback_spectrum (g : G) (c : G ⧸ X.subgroup.toSubgroup)
    (x : BanachSpectrum X.inducedChartAlgebra) :
    X.localAffinoidSpectrumHomeomorph.symm
        (BanachSpectrum.comap (X.affinoidActionPullback g c).toBoundedRingHom x) =
      X.actionChartElement g c • X.localAffinoidSpectrumHomeomorph.symm x := by
  rw [← X.strictActionPullback_spectrum]
  apply BanachSpectrum.ext
  intro a
  change x ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (X.strictActionPullback g c
        ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra)
          ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm a)))) =
    x ((PresentedAffinoidAlgebra.strictEquiv K X.domain.obj.algebra).symm
      (X.strictActionPullback g c a))
  rw [BoundedAlgEquiv.apply_symm_apply]

/-- The actual family action realizes left translation on the balanced quotient. -/
theorem affinoidActionMap_realization (g : G) (p : X.inducedAffinoidObject.Space) :
    g • X.inducedAffinoidHomeomorph p =
      X.inducedAffinoidHomeomorph ((X.affinoidActionMap g).spectrumMap p) := by
  change DisjointAffinoidAtlas.Space X.inducedAffinoidFamily at p
  rcases p with ⟨c, x⟩
  change BanachSpectrum X.inducedChartAlgebra at x
  change g • X.inducedCosetHomeomorph ⟨c, X.localAffinoidSpectrumHomeomorph.symm x⟩ =
    X.inducedCosetHomeomorph ⟨g • c, X.localAffinoidSpectrumHomeomorph.symm
      (BanachSpectrum.comap (X.affinoidActionPullback g c).toBoundedRingHom x)⟩
  rw [X.smul_inducedCosetHomeomorph g c (g • c) (X.actionChartElement g c)
    (X.actionChartElement_spec g c), X.affinoidActionPullback_spectrum]

/-- Realizing the bounded action yields the existing action on the actual quotient. -/
def inducedAffinoidSpectrumIso :
    ((AffinoidFamily.spectrumFunctor (K := K)).mapAction G).obj X.inducedAffinoidAction ≅
      X.inducedSpectrumAction :=
  Action.mkIso (TopCat.isoOfHomeo X.inducedAffinoidHomeomorph) (fun g => by
    apply TopCat.ext
    intro p
    exact (X.affinoidActionMap_realization g p).symm)

/-- Joint continuity holds for the actual spectrum realization of the bounded action. -/
theorem continuous_affinoidAction :
    Continuous (fun p : G × X.inducedAffinoidObject.Space =>
      (X.affinoidActionMap p.1).spectrumMap p.2) := by
  have h :
      (fun p : G × X.inducedAffinoidObject.Space =>
        (X.affinoidActionMap p.1).spectrumMap p.2) =
      (fun p => X.inducedAffinoidHomeomorph.symm
        (p.1 • X.inducedAffinoidHomeomorph p.2)) := by
    funext p
    exact (X.inducedAffinoidHomeomorph.symm_apply_apply _).symm.trans
      (congrArg X.inducedAffinoidHomeomorph.symm
        (X.affinoidActionMap_realization p.1 p.2).symm)
  rw [h]
  exact X.inducedAffinoidHomeomorph.symm.continuous.comp
    (continuous_fst.smul (X.inducedAffinoidHomeomorph.continuous.comp continuous_snd))

/-- Continuity is asserted on the constructed spectra, with no automorphism topology assumed. -/
def inducedAffinoidContinuousSpectrum : ContAction TopCat.{max u v} G :=
  ⟨((AffinoidFamily.spectrumFunctor (K := K)).mapAction G).obj X.inducedAffinoidAction,
    (Action.isContinuous_def _).mpr X.continuous_affinoidAction⟩

/-- The action carries each nonempty atlas component to a nonempty component. -/
def actionAtlasTarget (g : G) (c : X.inducedAffinoidAtlas.Index) :
    X.inducedAffinoidAtlas.Index :=
  (X.affinoidActionMap g).chartTarget c

@[simp]
theorem actionAtlasTarget_one (c : X.inducedAffinoidAtlas.Index) :
    X.actionAtlasTarget 1 c = c :=
  Subtype.ext (one_smul G c.val)

theorem actionAtlasTarget_mul (g h : G) (c : X.inducedAffinoidAtlas.Index) :
    X.actionAtlasTarget (g * h) c = X.actionAtlasTarget g (X.actionAtlasTarget h c) :=
  Subtype.ext (mul_smul g h c.val)

theorem image_actionAtlasChart_subset (g : G) (c : X.inducedAffinoidAtlas.Index) :
    (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart (X.actionAtlasTarget g c)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (X.affinoidActionPullback g c.val).toBoundedRingHom x,
    (X.affinoidActionMap_realization g ⟨c.val, x⟩).symm⟩

/-- Containment in any atlas chart identifies its index with the action target. -/
theorem actionAtlasTarget_eq (g : G)
    (c d : X.inducedAffinoidAtlas.Index)
    (h : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d)) : X.actionAtlasTarget g c = d := by
  apply (X.affinoidActionMap g).chartTarget_eq c d
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨y, X.inducedAffinoidHomeomorph.injective ?_⟩
  exact hy.trans (X.affinoidActionMap_realization g ⟨c.val, x⟩)

/-- The actual bounded pullback for every atlas pair satisfying action containment. -/
def actionAtlasPullback (g : G) (c d : X.inducedAffinoidAtlas.Index)
    (_h : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d)) :
    BoundedAlgHom K (X.inducedAffinoidAtlas.algebra d)
      (X.inducedAffinoidAtlas.algebra c) :=
  X.affinoidActionPullback g c.val

theorem actionAtlasPullback_chart (g : G) (c d : X.inducedAffinoidAtlas.Index)
    (h : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d))
    (x : BanachSpectrum (X.inducedAffinoidAtlas.algebra c)) :
    X.inducedAffinoidAtlas.chart d
        (BanachSpectrum.comap (X.actionAtlasPullback g c d h).toBoundedRingHom x) =
      g • X.inducedAffinoidAtlas.chart c x := by
  have hd := X.actionAtlasTarget_eq g c d h
  subst d
  exact (X.affinoidActionMap_realization g ⟨c.val, x⟩).symm

/-- Compatibility with restrictions in both copies of the actual atlas. -/
theorem actionAtlasPullback_naturality (g : G)
    (c c' d d' : X.inducedAffinoidAtlas.Index)
    (hcc' : Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart c'))
    (hdd' : Set.range (X.inducedAffinoidAtlas.chart d) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d'))
    (h : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d))
    (h' : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart c') ⊆
      Set.range (X.inducedAffinoidAtlas.chart d')) :
    (X.inducedAffinoidAtlas.restriction c c' hcc').comp (X.actionAtlasPullback g c' d' h') =
      (X.actionAtlasPullback g c d h).comp (X.inducedAffinoidAtlas.restriction d d' hdd') := by
  rw [X.inducedAffinoidAtlas_restriction_eq, X.inducedAffinoidAtlas_restriction_eq]
  have hc := X.inducedAffinoidAtlas_index_eq_of_subset c c' hcc'
  subst c'
  rfl

@[simp]
theorem actionAtlasPullback_one (c : X.inducedAffinoidAtlas.Index)
    (h : (fun z => (1 : G) • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart c)) :
    X.actionAtlasPullback 1 c c h =
      BoundedAlgHom.id K (X.inducedAffinoidAtlas.algebra c) :=
  X.affinoidActionPullback_one c.val

/-- The multiplication law holds on algebras for every compatible triple of charts. -/
theorem actionAtlasPullback_mul (g h : G) (c d e : X.inducedAffinoidAtlas.Index)
    (hhd : (fun z => h • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart d))
    (hge : (fun z => g • z) '' Set.range (X.inducedAffinoidAtlas.chart d) ⊆
      Set.range (X.inducedAffinoidAtlas.chart e))
    (hghe : (fun z => (g * h) • z) '' Set.range (X.inducedAffinoidAtlas.chart c) ⊆
      Set.range (X.inducedAffinoidAtlas.chart e)) :
    X.actionAtlasPullback (g * h) c e hghe =
      (X.actionAtlasPullback h c d hhd).comp (X.actionAtlasPullback g d e hge) := by
  have hd : d.val = h • c.val :=
    congrArg Subtype.val (X.actionAtlasTarget_eq h c d hhd).symm
  change X.affinoidActionPullback (g * h) c.val =
    (X.affinoidActionPullback h c.val).comp (X.affinoidActionPullback g d.val)
  rw [hd, X.affinoidActionPullback_mul]

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

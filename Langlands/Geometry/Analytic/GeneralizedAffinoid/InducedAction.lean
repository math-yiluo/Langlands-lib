import Langlands.Geometry.Analytic.GeneralizedAffinoid.NormContinuousAction
import Langlands.Geometry.Analytic.DisjointAffinoidMorphisms
import Langlands.Geometry.Analytic.DisjointAffinoidTransport
import Langlands.Topology.GroupAction.InducedCharts
import Mathlib.GroupTheory.GroupAction.Quotient

/-! # Induction of actual positive-polyradius affinoid actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra

open CategoryTheory Topology

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

namespace InducedAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {G : Type v} [Group G] (H : Subgroup G)

/-- The subgroup element comparing chosen representatives before and after translation. -/
def correction (g : G) (c : G ⧸ H) : H :=
  ⟨(g • c).out⁻¹ * (g * c.out), by
    apply QuotientGroup.eq.mp
    rw [QuotientGroup.out_eq']
    exact (MulAction.Quotient.coe_smul_out H g c).symm⟩

@[simp]
theorem correction_coe (g : G) (c : G ⧸ H) :
    (correction H g c : G) = (g • c).out⁻¹ * (g * c.out) := rfl

theorem correction_spec (g : G) (c : G ⧸ H) :
    g * c.out = (g • c).out * (correction H g c : G) := by
  simp

@[simp]
theorem correction_one (c : G ⧸ H) : correction H 1 c = 1 := by
  apply Subtype.ext
  simp

theorem correction_mul (g h : G) (c : G ⧸ H) :
    correction H (g * h) c = correction H g (h • c) * correction H h c := by
  apply Subtype.ext
  simp [mul_smul, mul_assoc]

variable [TopologicalSpace G] (X : NormContinuousAction K H)

/-- One copy of the original genuine positive-polyradius quotient for each coset. -/
def family : AffinoidFamily.{u, v} K :=
  ⟨G ⧸ H, fun _ => X.obj.V⟩

/-- The inverse of the forward subgroup operator is the geometric pullback. -/
def pullback (g : G) (c : G ⧸ H) : BoundedAlgHom K X.obj.V X.obj.V :=
  (X.actionAut (correction H g c)).inv

@[simp]
theorem pullback_one (c : G ⧸ H) :
    pullback H X 1 c = BoundedAlgHom.id K X.obj.V := by
  simp only [pullback, correction_one, map_one]
  rfl

theorem pullback_mul (g h : G) (c : G ⧸ H) :
    pullback H X (g * h) c =
      (pullback H X h c).comp (pullback H X g (h • c)) := by
  unfold pullback
  rw [correction_mul, map_mul]
  rfl

/-- A bounded map of genuine quotient families, with the translated coset index. -/
def actionMap (g : G) : family H X ⟶ family H X where
  indexMap := fun c : G ⧸ H => g • c
  pullback := pullback H X g

@[simp]
theorem actionMap_one : actionMap H X 1 = 𝟙 (family H X) := by
  apply AffinoidFamily.Hom.ext (funext fun c : G ⧸ H => one_smul G c)
  exact heq_of_eq (funext (pullback_one H X))

theorem actionMap_mul (g h : G) :
    actionMap H X (g * h) = actionMap H X h ≫ actionMap H X g := by
  apply AffinoidFamily.Hom.ext (funext fun c : G ⧸ H => mul_smul g h c)
  exact heq_of_eq (funext (pullback_mul H X g h))

/-- Induction acts on actual quotient families through bounded algebra pullbacks. -/
def action : Action (AffinoidFamily.{u, v} K) G where
  V := family H X
  ρ :=
    { toFun := actionMap H X
      map_one' := actionMap_one H X
      map_mul' := actionMap_mul H X }

/-- The inverses of the constructed bounded family maps are supplied by the group laws. -/
def automorphisms : G →* Aut (family H X) :=
  (action H X).ρAut

/-- The original bounded multiplicative spectrum with its specified subgroup action. -/
def LocalSpectrum := BanachSpectrum X.obj.V

instance : TopologicalSpace (LocalSpectrum H X) :=
  inferInstanceAs (TopologicalSpace (BanachSpectrum X.obj.V))

instance : MulAction H (LocalSpectrum H X) :=
  MulAction.compHom (BanachSpectrum X.obj.V) X.actionAut

theorem pullback_spectrum (g : G) (c : G ⧸ H) (x : LocalSpectrum H X) :
    BanachSpectrum.comap (pullback H X g c).toBoundedRingHom x =
      correction H g c • x := rfl

variable [IsTopologicalGroup G]

instance : ContinuousSMul H (LocalSpectrum H X) where
  continuous_smul := (Action.isContinuous_def _).mp (NormContinuousAction.spectrum X).property

/-- The actual balanced quotient of the subgroup's affinoid spectrum. -/
abbrev Spectrum := TopologicalInduction.Space H (LocalSpectrum H X)

/-- For an open subgroup, the family spectrum is the actual balanced quotient. -/
def spectrumHomeomorph (hH : IsOpen (H : Set G)) :
    (family H X).Space ≃ₜ Spectrum H X :=
  TopologicalInduction.cosetCopiesHomeomorph H (X := LocalSpectrum H X) hH

@[simp]
theorem spectrumHomeomorph_apply (hH : IsOpen (H : Set G))
    (c : G ⧸ H) (x : LocalSpectrum H X) :
    spectrumHomeomorph H X hH ⟨c, x⟩ = TopologicalInduction.mk H c.out x := rfl

/-- The algebraically constructed family action realizes the actual quotient action. -/
theorem actionMap_realization (hH : IsOpen (H : Set G))
    (g : G) (p : (family H X).Space) :
    g • spectrumHomeomorph H X hH p =
      spectrumHomeomorph H X hH ((actionMap H X g).spectrumMap p) := by
  rcases p with ⟨c, x⟩
  change G ⧸ H at c
  change LocalSpectrum H X at x
  change g • TopologicalInduction.cosetCopiesHomeomorph H (X := LocalSpectrum H X) hH
      ⟨c, x⟩ =
    TopologicalInduction.cosetCopiesHomeomorph H (X := LocalSpectrum H X) hH
      ⟨g • (c : G ⧸ H), correction H g c • (show LocalSpectrum H X from x)⟩
  exact TopologicalInduction.smul_cosetCopiesHomeomorph H (X := LocalSpectrum H X)
    hH g c (g • (c : G ⧸ H))
    (correction H g c) (correction_spec H g c) x

/-- Joint continuity of the realized bounded family action follows from the quotient. -/
theorem continuous_action (hH : IsOpen (H : Set G)) :
    Continuous (fun p : G × (family H X).Space =>
      (actionMap H X p.1).spectrumMap p.2) := by
  let e := spectrumHomeomorph H X hH
  have he :
      (fun p : G × (family H X).Space => (actionMap H X p.1).spectrumMap p.2) =
      (fun p => e.symm (p.1 • e p.2)) := by
    funext p
    exact (e.symm_apply_apply _).symm.trans
      (congrArg e.symm (actionMap_realization H X hH p.1 p.2).symm)
  rw [he]
  exact e.symm.continuous.comp
    (continuous_fst.smul (e.continuous.comp continuous_snd))

/-- The realized action is an actual continuous full-group action. -/
def continuousSpectrum (hH : IsOpen (H : Set G)) : ContAction TopCat.{max u v} G :=
  ⟨((AffinoidFamily.spectrumFunctor (K := K)).mapAction G).obj (action H X),
    (Action.isContinuous_def _).mpr (continuous_action H X hH)⟩

/-- The atlas is constructed on the balanced quotient from the genuine coset family. -/
def atlas [CompleteSpace K] (hH : IsOpen (H : Set G)) :
    IndexedAffinoidAtlas.{u, max u v, v} K (Spectrum H X) :=
  DisjointAffinoidAtlas.transportAtlas (family H X).algebra (spectrumHomeomorph H X hH)

@[simp]
theorem atlas_chart [CompleteSpace K] (hH : IsOpen (H : Set G))
    (c : (atlas H X hH).Index) (x : BanachSpectrum ((atlas H X hH).algebra c)) :
    (atlas H X hH).chart c x =
      TopologicalInduction.mk H c.val.out (show LocalSpectrum H X from x) := rfl

section AtlasAction

variable [CompleteSpace K] (hH : IsOpen (H : Set G))

/-- Translation carries a nonempty component to a nonempty component by actual pullback. -/
def chartTarget (g : G) (c : (atlas H X hH).Index) : (atlas H X hH).Index :=
  (actionMap H X g).chartTarget c

@[simp]
theorem chartTarget_one (c : (atlas H X hH).Index) :
    chartTarget H X hH 1 c = c := by
  change {c : G ⧸ H // Nonempty (BanachSpectrum X.obj.V)} at c
  apply Subtype.ext
  change (1 : G) • (c.val : G ⧸ H) = c.val
  exact one_smul G c.val

theorem chartTarget_mul (g h : G) (c : (atlas H X hH).Index) :
    chartTarget H X hH (g * h) c =
      chartTarget H X hH g (chartTarget H X hH h c) := by
  change {c : G ⧸ H // Nonempty (BanachSpectrum X.obj.V)} at c
  apply Subtype.ext
  change (g * h) • (c.val : G ⧸ H) = g • h • (c.val : G ⧸ H)
  exact mul_smul g h c.val

theorem image_chart_subset (g : G) (c : (atlas H X hH).Index) :
    (fun z => g • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart (chartTarget H X hH g c)) := by
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  exact ⟨BanachSpectrum.comap (pullback H X g c.val).toBoundedRingHom x,
    (actionMap_realization H X hH g ⟨c.val, x⟩).symm⟩

/-- Nonempty disjoint charts force every admissible target to be the translated coset. -/
theorem chartTarget_eq (g : G) (c d : (atlas H X hH).Index)
    (h : (fun z => g • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart d)) : chartTarget H X hH g c = d := by
  apply (actionMap H X g).chartTarget_eq c d
  rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
  obtain ⟨y, hy⟩ := h ⟨_, ⟨x, rfl⟩, rfl⟩
  refine ⟨y, (spectrumHomeomorph H X hH).injective ?_⟩
  exact hy.trans (actionMap_realization H X hH g ⟨c.val, x⟩)

/-- An actual bounded algebra map for every admissible pair of translated atlas charts. -/
def chartPullback (g : G) (c d : (atlas H X hH).Index)
    (_h : (fun z => g • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart d)) :
    BoundedAlgHom K ((atlas H X hH).algebra d) ((atlas H X hH).algebra c) :=
  pullback H X g c.val

theorem chartPullback_chart (g : G) (c d : (atlas H X hH).Index)
    (h : (fun z => g • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart d))
    (x : BanachSpectrum ((atlas H X hH).algebra c)) :
    (atlas H X hH).chart d
        (BanachSpectrum.comap (chartPullback H X hH g c d h).toBoundedRingHom x) =
      g • (atlas H X hH).chart c x := by
  have hd := chartTarget_eq H X hH g c d h
  subst d
  exact (actionMap_realization H X hH g ⟨c.val, x⟩).symm

/-- Restrictions commute with action pullbacks as bounded algebra maps. -/
theorem chartPullback_naturality (g : G) (c c' d d' : (atlas H X hH).Index)
    (hcc' : Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart c'))
    (hdd' : Set.range ((atlas H X hH).chart d) ⊆
      Set.range ((atlas H X hH).chart d'))
    (h : (fun z => g • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart d))
    (h' : (fun z => g • z) '' Set.range ((atlas H X hH).chart c') ⊆
      Set.range ((atlas H X hH).chart d')) :
    ((atlas H X hH).restriction c c' hcc').comp (chartPullback H X hH g c' d' h') =
      (chartPullback H X hH g c d h).comp ((atlas H X hH).restriction d d' hdd') := by
  have hc := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X).algebra
    (spectrumHomeomorph H X hH) c c' hcc'
  have hd := DisjointAffinoidAtlas.transportChart_eq_of_subset (family H X).algebra
    (spectrumHomeomorph H X hH) d d' hdd'
  subst c'
  subst d'
  rw [(atlas H X hH).restriction_id, (atlas H X hH).restriction_id]
  exact BoundedAlgHom.ext fun _ => rfl

@[simp]
theorem chartPullback_one (c : (atlas H X hH).Index)
    (h : (fun z => (1 : G) • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart c)) :
    chartPullback H X hH 1 c c h = BoundedAlgHom.id K ((atlas H X hH).algebra c) :=
  pullback_one H X c.val

/-- Multiplication reverses on the original algebras for every compatible chart triple. -/
theorem chartPullback_mul (g h : G) (c d e : (atlas H X hH).Index)
    (hhd : (fun z => h • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart d))
    (hge : (fun z => g • z) '' Set.range ((atlas H X hH).chart d) ⊆
      Set.range ((atlas H X hH).chart e))
    (hghe : (fun z => (g * h) • z) '' Set.range ((atlas H X hH).chart c) ⊆
      Set.range ((atlas H X hH).chart e)) :
    chartPullback H X hH (g * h) c e hghe =
      (chartPullback H X hH h c d hhd).comp (chartPullback H X hH g d e hge) := by
  change {c : G ⧸ H // Nonempty (BanachSpectrum X.obj.V)} at c d
  have hd : d.val = h • (c.val : G ⧸ H) :=
    congrArg Subtype.val (chartTarget_eq H X hH h c d hhd).symm
  change pullback H X (g * h) c.val =
    (pullback H X h c.val).comp (pullback H X g d.val)
  rw [hd, pullback_mul]

end AtlasAction

end InducedAction

end Langlands.Analytic.PresentedAffinoidAlgebra

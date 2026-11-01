import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormStabilizer
import Langlands.Topology.GroupAction.CompactLocallyConstantAction

/-! # Continuous rational point actions from norm-continuous base orbits -/

noncomputable section

universe u v w t

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology CompactAction

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K]
  {A : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- Restrict the actual ambient point operator to the weighted rational locus. -/
def normLocusOperator (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) : C(d.locus, d.locus) := by
  refine ⟨fun x => ⟨ρ g.val • x.val, ?_⟩, ?_⟩
  · have hg := (mem_normOpenStabilizer ρ hρ d g.val).mp g.property
    exact hg.subset ⟨x.val, x.property, rfl⟩
  · apply Continuous.subtype_mk
    exact ((BanachSpectrum.comapContinuous
      (ρ g.val).inv.toBoundedRingHom).continuous.comp continuous_subtype_val)

@[simp]
theorem normLocusOperator_coe (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) (x : d.locus) :
    (normLocusOperator ρ hρ d g x : BanachSpectrum A) = ρ g.val • x.val := rfl

/-- The full derived open stabilizer acts on the original locus subspace. -/
def normLocusAction (d : RationalChart K A) :
    Action TopCat.{u} (normOpenStabilizer ρ hρ d) where
  V := TopCat.of d.locus
  ρ :=
    { toFun := fun g => TopCat.ofHom (normLocusOperator ρ hρ d g)
      map_one' := by
        apply TopCat.ext
        intro x
        apply Subtype.ext
        change ρ 1 • (x : BanachSpectrum A) = x
        rw [map_one, one_smul]
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        apply Subtype.ext
        change ρ (g.val * h.val) • (x : BanachSpectrum A) =
          ρ g.val • (ρ h.val • (x : BanachSpectrum A))
        rw [map_mul, mul_smul] }

include hρ in
/-- The existing norm-orbit theorem supplies ambient joint point continuity. -/
theorem continuous_normAmbientSpectrumAction :
    Continuous (fun p : G × BanachSpectrum A => ρ p.1 • p.2) := by
  change Continuous (fun p : G × BanachSpectrum A =>
    BanachSpectrum.comap (ρ p.1).inv.toBoundedRingHom p.2)
  exact BanachSpectrum.continuous_comap_of_continuous_apply
    (fun g : G => (ρ g).inv.toBoundedRingHom)
    (fun a => by
      apply ((hρ a).comp continuous_inv).congr
      intro g
      change (ρ (g⁻¹)).hom.toAlgHom a = (ρ g).inv.toAlgHom a
      rw [map_inv]
      rfl)

/-- Joint continuity restricts to the preserved locus with its actual topology. -/
theorem normLocusAction_isContinuous (d : RationalChart K A) :
    (normLocusAction ρ hρ d).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  have hc : Continuous (fun p : normOpenStabilizer ρ hρ d × d.locus =>
      ρ p.1.val • p.2.val) :=
    (continuous_normAmbientSpectrumAction ρ hρ).comp
      ((continuous_subtype_val.comp continuous_fst).prodMk
        (continuous_subtype_val.comp continuous_snd))
  exact hc.subtype_mk _

/-- The locus action uses the inherited topology of the derived open subgroup. -/
def normLocusContinuousAction (d : RationalChart K A) :
    ContAction TopCat.{u} (normOpenStabilizer ρ hρ d) :=
  ⟨normLocusAction ρ hρ d, normLocusAction_isContinuous ρ hρ d⟩

variable [CompleteSpace K]

/-- Actual bounded section automorphisms intertwine the structural spectrum map. -/
theorem normSectionAction_spectrumMap (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) (x : BanachSpectrum d.algebra) :
    d.spectrumMap ((normSectionAction ρ hρ d g) • x) =
      ρ g.val • d.spectrumMap x :=
  DomainAutomorphism.stabilizerSectionAction_spectrumMap d.toDomain
    (normStabilizerHom ρ hρ d g) x

/-- The proved rational homeomorphism intertwines the two actual point actions. -/
theorem normSectionAction_locusHomeomorph (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) (x : BanachSpectrum d.algebra) :
    d.locusHomeomorph ((normSectionAction ρ hρ d g) • x) =
      normLocusOperator ρ hρ d g (d.locusHomeomorph x) := by
  apply Subtype.ext
  exact normSectionAction_spectrumMap ρ hρ d g x

/-- The spectrum action retains the actual bounded section operators. -/
def normSpectrumAction (d : RationalChart K A) :
    Action TopCat.{u} (normOpenStabilizer ρ hρ d) where
  V := TopCat.of (BanachSpectrum d.algebra)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (normSectionAction ρ hρ d g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change (normSectionAction ρ hρ d 1) • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change (normSectionAction ρ hρ d (g * h)) • x =
          (normSectionAction ρ hρ d g) • ((normSectionAction ρ hρ d h) • x)
        rw [map_mul, mul_smul] }

/-- Rational spectrum identification derives local joint point continuity.
No norm-continuity of the transported section orbits is assumed. -/
theorem normSpectrumAction_isContinuous (d : RationalChart K A) :
    (normSpectrumAction ρ hρ d).IsContinuous := by
  apply (Action.isContinuous_def _).mpr
  have hc : Continuous (fun p : normOpenStabilizer ρ hρ d × BanachSpectrum d.algebra =>
      normLocusOperator ρ hρ d p.1 (d.locusHomeomorph p.2)) :=
    ((Action.isContinuous_def _).mp (normLocusAction_isContinuous ρ hρ d)).comp
      (continuous_fst.prodMk (d.locusHomeomorph.continuous.comp continuous_snd))
  apply (d.locusHomeomorph.symm.continuous.comp hc).congr
  intro p
  apply d.locusHomeomorph.injective
  change d.locusHomeomorph (d.locusHomeomorph.symm
    (normLocusOperator ρ hρ d p.1 (d.locusHomeomorph p.2))) =
      d.locusHomeomorph ((normSectionAction ρ hρ d p.1) • p.2)
  rw [d.locusHomeomorph.apply_symm_apply]
  exact (normSectionAction_locusHomeomorph ρ hρ d p.1 p.2).symm

/-- Bundle the actual local spectrum action and its derived joint continuity. -/
def normSpectrumContinuousAction (d : RationalChart K A) :
    ContAction TopCat.{u} (normOpenStabilizer ρ hρ d) :=
  ⟨normSpectrumAction ρ hρ d, normSpectrumAction_isContinuous ρ hρ d⟩

@[simp]
theorem normSpectrumContinuousAction_apply (d : RationalChart K A)
    (g : normOpenStabilizer ρ hρ d) (x : BanachSpectrum d.algebra) (b : d.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((normSpectrumContinuousAction ρ hρ d).obj.ρ g) x) b =
        x ((normSectionAction ρ hρ d g).inv.toAlgHom b) := rfl

/-- Every entire locally constant function has an open stabilizer in the
original rational-locus preserving subgroup. -/
def normSpectrumFunctionStabilizer (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) :
    OpenSubgroup (normOpenStabilizer ρ hρ d) := by
  let H := normOpenStabilizer ρ hρ d
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H (BanachSpectrum d.algebra) :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      (normSpectrumAction ρ hρ d)))
  letI : ContinuousSMul H (BanachSpectrum d.algebra) :=
    normSpectrumAction_isContinuous ρ hρ d
  exact CompactAction.openStabilizer H f

@[simp]
theorem mem_normSpectrumFunctionStabilizer (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) (g : normOpenStabilizer ρ hρ d) :
    g ∈ normSpectrumFunctionStabilizer ρ hρ d f ↔
      ∀ x, f ((normSectionAction ρ hρ d g) • x) = f x := Iff.rfl

/-- Inverse precomposition gives a jointly continuous action on all locally
constant functions, with their discrete topology and unchanged coefficient set. -/
def normSpectrumLocallyConstantAction (d : RationalChart K A) (C : Type w) :
    ContAction TopCat.{max u w} (normOpenStabilizer ρ hρ d) := by
  let H := normOpenStabilizer ρ hρ d
  letI : IsTopologicalGroup H :=
    Topology.IsInducing.subtypeVal.isTopologicalGroup (SubgroupClass.subtype H)
  letI : MulAction H (BanachSpectrum d.algebra) :=
    inferInstanceAs (MulAction H ((forget₂ (Action TopCat.{u} H) TopCat.{u}).obj
      (normSpectrumAction ρ hρ d)))
  letI : ContinuousSMul H (BanachSpectrum d.algebra) :=
    normSpectrumAction_isContinuous ρ hρ d
  exact DiscreteLocallyConstant.continuousAction
    (X := BanachSpectrum d.algebra) (A := C) H

@[simp]
theorem normSpectrumLocallyConstantAction_apply (d : RationalChart K A) {C : Type w}
    (g : normOpenStabilizer ρ hρ d)
    (f : DiscreteLocallyConstant (BanachSpectrum d.algebra) C)
    (x : BanachSpectrum d.algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      (ConcreteCategory.hom ((normSpectrumLocallyConstantAction ρ hρ d C).obj.ρ g) f)) x =
        f ((normSectionAction ρ hρ d g⁻¹) • x) := rfl

/-- Openness of the locus stabilizer lifts the full function stabilizer into G. -/
def normAmbientFunctionStabilizer (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) : OpenSubgroup G where
  toSubgroup := (normSpectrumFunctionStabilizer ρ hρ d f).toSubgroup.map
    (normOpenStabilizer ρ hρ d).toSubgroup.subtype
  isOpen' := (normOpenStabilizer ρ hρ d).isOpen.isOpenMap_subtype_val _
    (normSpectrumFunctionStabilizer ρ hρ d f).isOpen

@[simp]
theorem mem_normAmbientFunctionStabilizer (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) (g : G) :
    g ∈ normAmbientFunctionStabilizer ρ hρ d f ↔
      ∃ hg : g ∈ normOpenStabilizer ρ hρ d,
        ∀ x, f ((normSectionAction ρ hρ d ⟨g, hg⟩) • x) = f x := by
  constructor
  · rintro ⟨h, hh, rfl⟩
    exact ⟨h.property, (mem_normSpectrumFunctionStabilizer ρ hρ d f h).mp hh⟩
  · rintro ⟨hg, hfix⟩
    exact ⟨⟨g, hg⟩, (mem_normSpectrumFunctionStabilizer ρ hρ d f ⟨g, hg⟩).mpr hfix, rfl⟩

theorem normAmbientFunctionStabilizer_le (d : RationalChart K A) {C : Type w}
    (f : LocallyConstant (BanachSpectrum d.algebra) C) :
    normAmbientFunctionStabilizer ρ hρ d f ≤ normOpenStabilizer ρ hρ d := by
  intro g hg
  obtain ⟨h, _, rfl⟩ := hg
  exact h.property

/-- A finite family on arbitrary actual rational quotient spectra has a
common original-group open stabilizer inside any prescribed open subgroup. -/
def finiteNormFunctionStabilizer {ι : Type t} [Finite ι] {C : Type w}
    (d : ι → RationalChart K A)
    (f : ∀ i, LocallyConstant (BanachSpectrum (d i).algebra) C) (U : OpenSubgroup G) :
    OpenSubgroup G :=
  U ⊓ OpenSubgroup.iInfOfFinite (fun i => normAmbientFunctionStabilizer ρ hρ (d i) (f i))

@[simp]
theorem mem_finiteNormFunctionStabilizer {ι : Type t} [Finite ι] {C : Type w}
    (d : ι → RationalChart K A)
    (f : ∀ i, LocallyConstant (BanachSpectrum (d i).algebra) C)
    (U : OpenSubgroup G) (g : G) :
    g ∈ finiteNormFunctionStabilizer ρ hρ d f U ↔
      g ∈ U ∧ ∀ i, ∃ hi : g ∈ normOpenStabilizer ρ hρ (d i),
        ∀ x, f i ((normSectionAction ρ hρ (d i) ⟨g, hi⟩) • x) = f i x := by
  change (g ∈ U ∧ g ∈
    (⨅ i, (normAmbientFunctionStabilizer ρ hρ (d i) (f i)).toSubgroup)) ↔ _
  simp only [Subgroup.mem_iInf, OpenSubgroup.mem_toSubgroup,
    mem_normAmbientFunctionStabilizer]

theorem finiteNormFunctionStabilizer_le {ι : Type t} [Finite ι] {C : Type w}
    (d : ι → RationalChart K A)
    (f : ∀ i, LocallyConstant (BanachSpectrum (d i).algebra) C) (U : OpenSubgroup G) :
    finiteNormFunctionStabilizer ρ hρ d f U ≤ U := inf_le_left

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

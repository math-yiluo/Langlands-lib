import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantAction
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantDescent
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainContinuousFiniteCover
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantCoverStabilizer

/-! # Continuous equivariant locally constant descent on finite spectrum covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

open CompactAction

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K} {d : Domain K P} (c : FiniteCover d)

/-- All component-spectrum function families with the complete original fiber equations. -/
abbrev DiscreteSpectrumCompatibleFamily (A : Type w) :=
  {f : ∀ i : Fin c.size, DiscreteLocallyConstant (BanachSpectrum (c.obj i).algebra) A //
    c.SpectrumLocallyConstantCompatible (fun i => (f i).toLocallyConstant)}

/-- Restriction to the unchanged component spectra with its full fiber equations. -/
def discreteSpectrumRestrict {A : Type w} (f : DiscreteLocallyConstant d.locus A) :
    c.DiscreteSpectrumCompatibleFamily A :=
  ⟨fun i => DiscreteLocallyConstant.pullback (c.componentMap i) f,
    c.spectrumLocallyConstantCompatible_restrict f.toLocallyConstant⟩

/-- Gluing uses the original disjoint-union quotient and the complete fiber equations. -/
def discreteSpectrumGlue {A : Type w} (f : c.DiscreteSpectrumCompatibleFamily A) :
    DiscreteLocallyConstant d.locus A :=
  ⟨c.spectrumLocallyConstantGlue (fun i => (f.val i).toLocallyConstant) f.property⟩

@[simp]
theorem discreteSpectrumGlue_apply {A : Type w}
    (f : c.DiscreteSpectrumCompatibleFamily A) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    c.discreteSpectrumGlue f (c.componentMap i x) = f.val i x :=
  c.spectrumLocallyConstantGlue_apply _ f.property i x

@[simp]
theorem discreteSpectrumGlue_restrict {A : Type w} (f : DiscreteLocallyConstant d.locus A) :
    c.discreteSpectrumGlue (c.discreteSpectrumRestrict f) = f := by
  apply DiscreteLocallyConstant.ext
  intro y
  obtain ⟨⟨i, x⟩, rfl⟩ := c.totalMap_surjective y
  exact c.discreteSpectrumGlue_apply (c.discreteSpectrumRestrict f) i x

@[simp]
theorem discreteSpectrumRestrict_glue {A : Type w}
    (f : c.DiscreteSpectrumCompatibleFamily A) :
    c.discreteSpectrumRestrict (c.discreteSpectrumGlue f) = f := by
  apply Subtype.ext
  funext i
  apply DiscreteLocallyConstant.ext
  intro x
  exact c.discreteSpectrumGlue_apply f i x

/-- The wrapper retains exactly the previously constructed complete-family equivalence. -/
def discreteSpectrumEquiv (A : Type w) :
    DiscreteLocallyConstant d.locus A ≃ c.DiscreteSpectrumCompatibleFamily A where
  toFun := c.discreteSpectrumRestrict
  invFun := c.discreteSpectrumGlue
  left_inv := c.discreteSpectrumGlue_restrict
  right_inv := c.discreteSpectrumRestrict_glue

end Langlands.Analytic.PresentedAffinoidAlgebra.Domain.FiniteCover

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology CompactAction

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P) (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
  (c : Domain.FiniteCover d.obj) (A : Type w)

local instance : IsTopologicalGroup (ρ.finiteFamilyOpenSubgroup H c.obj) :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup
    (SubgroupClass.subtype (ρ.finiteFamilyOpenSubgroup H c.obj))

local instance (i : Fin c.size) :
    MulAction (ρ.finiteFamilyOpenSubgroup H c.obj) (BanachSpectrum (c.obj i).algebra) :=
  inferInstanceAs (MulAction (ρ.finiteFamilyOpenSubgroup H c.obj)
    ((forget₂ (Action TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj)) TopCat.{u}).obj
      (ρ.finiteCoverComponentAction H d c i)))

local instance (i : Fin c.size) :
    ContinuousSMul (ρ.finiteFamilyOpenSubgroup H c.obj) (BanachSpectrum (c.obj i).algebra) :=
  ρ.invariantSpectrumAction_isContinuous (ρ.finiteFamilyOpenSubgroup H c.obj)
    (ρ.finiteInvariantFamily H c.obj i)

local instance : MulAction (ρ.finiteFamilyOpenSubgroup H c.obj) d.obj.locus :=
  inferInstanceAs (MulAction (ρ.finiteFamilyOpenSubgroup H c.obj)
    ((forget₂ (Action TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj)) TopCat.{u}).obj
      (ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj))))

local instance : ContinuousSMul (ρ.finiteFamilyOpenSubgroup H c.obj) d.obj.locus :=
  ρ.invariantLocusAction_isContinuous (ρ.finiteFamilyOpenSubgroup H c.obj)
    (ρ.finiteInvariantTarget H d c.obj)

/-- Restrict the original componentwise inverse-precomposition actions to all
families satisfying the complete quotient fiber equations. -/
def finiteCoverCompatibleLocallyConstantSmul
    (g : ρ.finiteFamilyOpenSubgroup H c.obj) (f : c.DiscreteSpectrumCompatibleFamily A) :
    c.DiscreteSpectrumCompatibleFamily A :=
  ⟨fun i => g • f.val i, fun i j x y h => by
    change f.val i (g⁻¹ • x) = f.val j (g⁻¹ • y)
    apply f.property
    change c.componentMap i (ρ.finiteCoverComponentSpectrumOperator H d c g⁻¹ i x) =
      c.componentMap j (ρ.finiteCoverComponentSpectrumOperator H d c g⁻¹ j y)
    rw [ρ.finiteCoverComponent_smul H d c g⁻¹ i x,
      ρ.finiteCoverComponent_smul H d c g⁻¹ j y, h]⟩

@[simp]
theorem finiteCoverCompatibleLocallyConstantSmul_apply
    (g : ρ.finiteFamilyOpenSubgroup H c.obj) (f : c.DiscreteSpectrumCompatibleFamily A)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    (ρ.finiteCoverCompatibleLocallyConstantSmul H d c A g f).val i x =
      f.val i (ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ g⁻¹) x) :=
  rfl

/-- The entire compatible-family action, with the inherited finite product topology. -/
def finiteCoverCompatibleLocallyConstantAction :
    ContAction TopCat.{max u w} (ρ.finiteFamilyOpenSubgroup H c.obj) := by
  let act : Action TopCat.{max u w} (ρ.finiteFamilyOpenSubgroup H c.obj) :=
    { V := TopCat.of (c.DiscreteSpectrumCompatibleFamily A)
      ρ :=
        { toFun := fun g => TopCat.ofHom
            ⟨ρ.finiteCoverCompatibleLocallyConstantSmul H d c A g,
              continuous_of_discreteTopology⟩
          map_one' := by
            apply TopCat.ext
            intro f
            apply Subtype.ext
            funext i
            exact one_smul _ (f.val i)
          map_mul' := by
            intro g h
            apply TopCat.ext
            intro f
            apply Subtype.ext
            funext i
            exact mul_smul g h (f.val i) } }
  refine ⟨act, (Action.isContinuous_def _).mpr ?_⟩
  change Continuous (fun p : (ρ.finiteFamilyOpenSubgroup H c.obj) ×
    c.DiscreteSpectrumCompatibleFamily A =>
      ρ.finiteCoverCompatibleLocallyConstantSmul H d c A p.1 p.2)
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_smul.comp
    (continuous_fst.prodMk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

/-- The original restriction and constructed quotient gluing are continuous
equivariant inverse maps for the unchanged common open acting subgroup. -/
def finiteCoverLocallyConstantDescentIso :
    ρ.invariantLocusLocallyConstantAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) A ≅
      ρ.finiteCoverCompatibleLocallyConstantAction H d c A :=
  ObjectProperty.isoMk _ (Action.mkIso
    { hom := TopCat.ofHom ⟨c.discreteSpectrumRestrict, continuous_of_discreteTopology⟩
      inv := TopCat.ofHom ⟨c.discreteSpectrumGlue, continuous_of_discreteTopology⟩
      hom_inv_id := by
        apply TopCat.ext
        intro f
        exact c.discreteSpectrumGlue_restrict f
      inv_hom_id := by
        apply TopCat.ext
        intro f
        exact c.discreteSpectrumRestrict_glue f }
    (fun g => by
      apply TopCat.ext
      intro f
      let f' : DiscreteLocallyConstant d.obj.locus A := f
      apply Subtype.ext
      funext i
      apply DiscreteLocallyConstant.ext
      intro x
      exact congrArg f' (ρ.finiteCoverComponent_smul H d c g⁻¹ i x).symm))

@[simp]
theorem finiteCoverLocallyConstantDescentIso_hom_apply
    (f : DiscreteLocallyConstant d.obj.locus A) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    ((ρ.finiteCoverLocallyConstantDescentIso H d c A).hom.hom.hom f).val i x =
      f (c.componentMap i x) := rfl

@[simp]
theorem finiteCoverLocallyConstantDescentIso_inv_apply
    (f : c.DiscreteSpectrumCompatibleFamily A) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((ρ.finiteCoverLocallyConstantDescentIso H d c A).inv.hom.hom f))
        (c.componentMap i x) = f.val i x :=
  c.discreteSpectrumGlue_apply f i x

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

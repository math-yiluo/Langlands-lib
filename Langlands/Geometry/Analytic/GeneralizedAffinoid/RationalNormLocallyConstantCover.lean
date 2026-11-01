import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormLocallyConstantPresheaf
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormInvariantOverBase
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartCovering
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainLocallyConstantCoverAction

/-! # Continuous equivariant locally constant descent for finite weighted rational covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory Topology CompactAction

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : PresentedAffinoidAlgebra K}

/-- Actual rational charts, their original bounded restrictions, and point coverage.
The finite index type may be empty. -/
structure FiniteCover (d : RationalChart K A) where
  size : ℕ
  obj : Fin size → RationalChart K A
  map : ∀ i, obj i ⟶ d
  covers : ∀ x ∈ d.locus, ∃ i, x ∈ (obj i).locus

namespace FiniteCover

variable {d : RationalChart K A} (c : FiniteCover d)

/-- The represented-domain cover retains every quotient algebra and bounded map. -/
def toDomainCover : Domain.FiniteCover d.toDomain where
  size := c.size
  obj i := (c.obj i).toDomain
  map i := (toDomainFunctor K A).map (c.map i)
  covers := c.covers

@[simp]
theorem toDomainCover_map_restriction (i : Fin c.size) :
    (c.toDomainCover.map i).restriction = (c.map i).restriction := rfl

@[simp]
theorem componentMap_coe (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ((c.toDomainCover.componentMap i x : d.locus) : BanachSpectrum A) =
      (c.obj i).spectrumMap x := rfl

/-- The component map is the original bounded spectrum restriction followed
by the original target spectrum-locus homeomorphism. -/
theorem componentMap_eq (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    c.toDomainCover.componentMap i x = d.locusHomeomorph ((c.map i).spectrumMap x) :=
  Subtype.ext ((c.map i).spectrumMap_over_base x).symm

/-- Full compatibility includes every pair of equal-image points, also within
a single component spectrum. -/
abbrev DiscreteCompatibleFamily (C : Type w) :=
  {f : ∀ i : Fin c.size, DiscreteLocallyConstant (BanachSpectrum (c.obj i).algebra) C //
    ∀ (i j : Fin c.size) (x : BanachSpectrum (c.obj i).algebra)
      (y : BanachSpectrum (c.obj j).algebra),
      c.toDomainCover.componentMap i x = c.toDomainCover.componentMap j y → f i x = f j y}

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : G →* Aut A)
  (hρ : ∀ a : A, Continuous (fun g : G => (ρ g).hom.toAlgHom a))

/-- The largest open subgroup inside U preserving the target and every component. -/
def normOpenSubgroup (U : OpenSubgroup G) : OpenSubgroup G :=
  finiteNormFamilyOpenSubgroup ρ hρ (U ⊓ normOpenStabilizer ρ hρ d) c.obj

omit [CompleteSpace K] in
@[simp]
theorem mem_normOpenSubgroup (U : OpenSubgroup G) (g : G) :
    g ∈ c.normOpenSubgroup ρ hρ U ↔
      g ∈ U ∧ g ∈ normOpenStabilizer ρ hρ d ∧
        ∀ i, g ∈ normOpenStabilizer ρ hρ (c.obj i) := by
  simp only [normOpenSubgroup, mem_finiteNormFamilyOpenSubgroup,
    OpenSubgroup.mem_inf]
  exact and_assoc

omit [CompleteSpace K] in
theorem le_normOpenSubgroup_iff (U V : OpenSubgroup G) :
    V ≤ c.normOpenSubgroup ρ hρ U ↔
      V ≤ U ∧ V ≤ normOpenStabilizer ρ hρ d ∧
        ∀ i, V ≤ normOpenStabilizer ρ hρ (c.obj i) := by
  rw [normOpenSubgroup, le_finiteNormFamilyOpenSubgroup_iff, le_inf_iff, and_assoc]

/-- The original target with its derived common-subgroup invariance witness. -/
def normInvariantTarget (U : OpenSubgroup G) :
    NormInvariantChart ρ hρ (c.normOpenSubgroup ρ hρ U) :=
  ⟨d, (finiteNormFamilyOpenSubgroup_le ρ hρ
    (U ⊓ normOpenStabilizer ρ hρ d) c.obj).trans inf_le_right⟩

/-- Every original component becomes invariant for that same common subgroup. -/
def normInvariantComponent (U : OpenSubgroup G) (i : Fin c.size) :
    NormInvariantChart ρ hρ (c.normOpenSubgroup ρ hρ U) :=
  ⟨c.obj i, finiteNormFamilyOpenSubgroup_le_stabilizer ρ hρ
    (U ⊓ normOpenStabilizer ρ hρ d) c.obj i⟩

/-- No additional arrow condition is imposed on the original bounded restriction. -/
def normInvariantMap (U : OpenSubgroup G) (i : Fin c.size) :
    c.normInvariantComponent ρ hρ U i ⟶ c.normInvariantTarget ρ hρ U :=
  ObjectProperty.homMk (c.map i)

local instance (U : OpenSubgroup G) : IsTopologicalGroup (c.normOpenSubgroup ρ hρ U) :=
  Topology.IsInducing.subtypeVal.isTopologicalGroup
    (SubgroupClass.subtype (c.normOpenSubgroup ρ hρ U))

/-- The unchanged component-spectrum map to the target locus is equivariant,
by composing the original rational homeomorphism and original locus restriction. -/
def normComponentToLocus (U : OpenSubgroup G) (i : Fin c.size) :
    (normInvariantSpectrumFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
        (c.normInvariantComponent ρ hρ U i) ⟶
      (normInvariantLocusFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
        (c.normInvariantTarget ρ hρ U) :=
  (normInvariantSpectrumLocusIso ρ hρ (c.normOpenSubgroup ρ hρ U)).hom.app
      (c.normInvariantComponent ρ hρ U i) ≫
    (normInvariantLocusFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).map
      (c.normInvariantMap ρ hρ U i)

@[simp]
theorem normComponentToLocus_apply (U : OpenSubgroup G) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (c.normComponentToLocus ρ hρ U i).hom.hom x =
      c.toDomainCover.componentMap i x := rfl

/-- The actual point operators commute with the original component map. -/
theorem normComponentToLocus_equivariant (U : OpenSubgroup G)
    (g : c.normOpenSubgroup ρ hρ U) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    c.toDomainCover.componentMap i
        (ConcreteCategory.hom
          (((normInvariantSpectrumFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
            (c.normInvariantComponent ρ hρ U i)).obj.ρ g) x) =
      ConcreteCategory.hom
        (((normInvariantLocusFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
          (c.normInvariantTarget ρ hρ U)).obj.ρ g)
        (c.toDomainCover.componentMap i x) :=
  congrArg (fun f => f x) ((c.normComponentToLocus ρ hρ U i).hom.comm g)

local instance (U : OpenSubgroup G) (i : Fin c.size) :
    MulAction (c.normOpenSubgroup ρ hρ U) (BanachSpectrum (c.obj i).algebra) :=
  inferInstanceAs (MulAction (c.normOpenSubgroup ρ hρ U)
    ((forget₂ (Action TopCat.{u} (c.normOpenSubgroup ρ hρ U)) TopCat.{u}).obj
      ((normInvariantSpectrumFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
        (c.normInvariantComponent ρ hρ U i)).obj))

local instance (U : OpenSubgroup G) (i : Fin c.size) :
    ContinuousSMul (c.normOpenSubgroup ρ hρ U) (BanachSpectrum (c.obj i).algebra) :=
  ((normInvariantSpectrumFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
    (c.normInvariantComponent ρ hρ U i)).property

/-- Restrict the actual inverse-precomposition operators to the entire
compatible-family subtype, retaining all equal-image fiber equations. -/
def normCompatibleSmul (U : OpenSubgroup G) (C : Type w)
    (g : c.normOpenSubgroup ρ hρ U) (f : c.DiscreteCompatibleFamily C) :
    c.DiscreteCompatibleFamily C :=
  ⟨fun i => g • f.val i, fun i j x y h => by
    change f.val i (g⁻¹ • x) = f.val j (g⁻¹ • y)
    apply f.property
    exact (c.normComponentToLocus_equivariant ρ hρ U g⁻¹ i x).trans
      ((congrArg (ConcreteCategory.hom
        (((normInvariantLocusFunctor ρ hρ (c.normOpenSubgroup ρ hρ U)).obj
          (c.normInvariantTarget ρ hρ U)).obj.ρ g⁻¹)) h).trans
        (c.normComponentToLocus_equivariant ρ hρ U g⁻¹ j y).symm)⟩

@[simp]
theorem normCompatibleSmul_apply (U : OpenSubgroup G) {C : Type w}
    (g : c.normOpenSubgroup ρ hρ U) (f : c.DiscreteCompatibleFamily C)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    (c.normCompatibleSmul ρ hρ U C g f).val i x =
      f.val i (BanachSpectrum.comap
        ((normInvariantSectionAction ρ hρ (c.normOpenSubgroup ρ hρ U)
          (c.normInvariantComponent ρ hρ U i)).actionAut g⁻¹).inv.toBoundedRingHom x) := rfl

/-- The compatible families carry the inherited finite product topology and
a jointly continuous action of the original common open subgroup. -/
def normCompatibleAction (U : OpenSubgroup G) (C : Type w) :
    ContAction TopCat.{max u w} (c.normOpenSubgroup ρ hρ U) := by
  let act : Action TopCat.{max u w} (c.normOpenSubgroup ρ hρ U) :=
    { V := TopCat.of (c.DiscreteCompatibleFamily C)
      ρ :=
        { toFun := fun g => TopCat.ofHom
            ⟨c.normCompatibleSmul ρ hρ U C g, continuous_of_discreteTopology⟩
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
  change Continuous (fun p : (c.normOpenSubgroup ρ hρ U) ×
    c.DiscreteCompatibleFamily C => c.normCompatibleSmul ρ hρ U C p.1 p.2)
  apply Continuous.subtype_mk
  exact continuous_pi fun i => continuous_smul.comp
    (continuous_fst.prodMk
      ((continuous_apply i).comp (continuous_subtype_val.comp continuous_snd)))

/-- Original restriction and quotient gluing give inverse continuous equivariant
maps on the complete locally constant function sets. -/
def normLocallyConstantDescentIso (U : OpenSubgroup G) (C : Type w) :
    (normInvariantLocusLocallyConstantPresheaf ρ hρ (c.normOpenSubgroup ρ hρ U) C).obj
        (Opposite.op (c.normInvariantTarget ρ hρ U)) ≅
      c.normCompatibleAction ρ hρ U C :=
  ObjectProperty.isoMk _ (Action.mkIso
    { hom := TopCat.ofHom
        ⟨c.toDomainCover.discreteSpectrumRestrict, continuous_of_discreteTopology⟩
      inv := TopCat.ofHom
        ⟨c.toDomainCover.discreteSpectrumGlue, continuous_of_discreteTopology⟩
      hom_inv_id := by
        apply TopCat.ext
        intro f
        exact c.toDomainCover.discreteSpectrumGlue_restrict f
      inv_hom_id := by
        apply TopCat.ext
        intro f
        exact c.toDomainCover.discreteSpectrumRestrict_glue f }
    (fun g => by
      apply TopCat.ext
      intro f
      let f' : DiscreteLocallyConstant d.locus C := f
      apply Subtype.ext
      funext i
      apply DiscreteLocallyConstant.ext
      intro x
      exact congrArg f' (c.normComponentToLocus_equivariant ρ hρ U g⁻¹ i x).symm))

@[simp]
theorem normLocallyConstantDescentIso_hom_apply (U : OpenSubgroup G) {C : Type w}
    (f : DiscreteLocallyConstant d.locus C) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    ((c.normLocallyConstantDescentIso ρ hρ U C).hom.hom.hom f).val i x =
      f (c.toDomainCover.componentMap i x) := rfl

@[simp]
theorem normLocallyConstantDescentIso_inv_apply (U : OpenSubgroup G) {C : Type w}
    (f : c.DiscreteCompatibleFamily C) (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((c.normLocallyConstantDescentIso ρ hρ U C).inv.hom.hom f))
        (c.toDomainCover.componentMap i x) = f.val i x :=
  c.toDomainCover.discreteSpectrumGlue_apply f i x

/-- The same descent on the target quotient spectrum, using the unchanged
equivariant rational spectrum-locus homeomorphism. -/
def normSpectrumLocallyConstantDescentIso (U : OpenSubgroup G) (C : Type w) :
    (normInvariantSpectrumLocallyConstantPresheaf ρ hρ (c.normOpenSubgroup ρ hρ U) C).obj
        (Opposite.op (c.normInvariantTarget ρ hρ U)) ≅
      c.normCompatibleAction ρ hρ U C :=
  ((normInvariantLocallyConstantPresheafIso ρ hρ (c.normOpenSubgroup ρ hρ U) C).app
    (Opposite.op (c.normInvariantTarget ρ hρ U))).symm ≪≫
      c.normLocallyConstantDescentIso ρ hρ U C

@[simp]
theorem normSpectrumLocallyConstantDescentIso_hom_apply (U : OpenSubgroup G)
    {C : Type w} (f : DiscreteLocallyConstant (BanachSpectrum d.algebra) C)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ((c.normSpectrumLocallyConstantDescentIso ρ hρ U C).hom.hom.hom f).val i x =
      f ((c.map i).spectrumMap x) := by
  change f (d.locusHomeomorph.symm (c.toDomainCover.componentMap i x)) = _
  rw [c.componentMap_eq, d.locusHomeomorph.symm_apply_apply]

@[simp]
theorem normSpectrumLocallyConstantDescentIso_inv_apply (U : OpenSubgroup G)
    {C : Type w} (f : c.DiscreteCompatibleFamily C)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    (DiscreteLocallyConstant.toLocallyConstant
      ((c.normSpectrumLocallyConstantDescentIso ρ hρ U C).inv.hom.hom f))
        ((c.map i).spectrumMap x) = f.val i x := by
  change c.toDomainCover.discreteSpectrumGlue f
    (d.locusHomeomorph ((c.map i).spectrumMap x)) = _
  rw [← c.componentMap_eq]
  exact c.toDomainCover.discreteSpectrumGlue_apply f i x

end FiniteCover
end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

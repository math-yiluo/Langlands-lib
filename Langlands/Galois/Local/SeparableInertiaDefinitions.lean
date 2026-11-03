import Langlands.Galois.Local.AbsoluteDefinitions
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Galois.Infinite

noncomputable section

open IsLocalRing ValuativeRel
open scoped NNReal Topology

namespace Langlands.LocalGalois.Separable

universe u

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := localNormedField F
local instance : IsUltrametricDist F := localNormedField_ultrametric F
local instance : CompleteSpace F := localNormedField_complete F
local instance : Finite (ResidueField (baseIntegers F)) := localResidue_finite F

/-! ### The inertia subgroup of `Gal(SeparableClosure F/F)` and its fixed field -/

def separableResidueHom :
    Gal(SeparableClosure F/F) →*
      Gal(ResidueField (extensionIntegers F (SeparableClosure F))/
        ResidueField (baseIntegers F)) :=
  residueHom F (SeparableClosure F)

def separableInertia : Subgroup Gal(SeparableClosure F/F) :=
  inertia F (SeparableClosure F)

theorem separableInertia_eq_ker : separableInertia F = (separableResidueHom F).ker := rfl

instance separableInertia_normal : (separableInertia F).Normal :=
  inertia_normal F (SeparableClosure F)

theorem mem_separableInertia_iff (σ : Gal(SeparableClosure F/F)) :
    σ ∈ separableInertia F ↔ ∀ x : extensionIntegers F (SeparableClosure F),
      residue _ (integerAut F (SeparableClosure F) σ x) = residue _ x :=
  mem_inertia_iff F (SeparableClosure F) σ

theorem separableInertia_isClosed :
    IsClosed (separableInertia F : Set Gal(SeparableClosure F/F)) :=
  inertia_isClosed F (SeparableClosure F)

def inertiaFixedField : IntermediateField F (SeparableClosure F) :=
  IntermediateField.fixedField (separableInertia F)

theorem mem_inertiaFixedField_iff (x : SeparableClosure F) :
    x ∈ inertiaFixedField F ↔ ∀ σ ∈ separableInertia F, σ x = x :=
  ⟨fun hx σ hσ => hx ⟨σ, hσ⟩, fun hx σ => hx σ σ.property⟩

instance inertiaFixedField_isGalois : IsGalois F (inertiaFixedField F) :=
  IsGalois.of_fixedField_normal_subgroup (separableInertia F)

theorem fixingSubgroup_inertiaFixedField :
    (inertiaFixedField F).fixingSubgroup = separableInertia F :=
  InfiniteGalois.fixingSubgroup_fixedField ⟨separableInertia F, separableInertia_isClosed F⟩

/-! ### The field maps `F → U → SeparableClosure F` -/

def baseToFixedField : F →ₐ[F] inertiaFixedField F := Algebra.ofId F _

def fixedFieldToSepClosure : inertiaFixedField F →ₐ[F] SeparableClosure F :=
  (inertiaFixedField F).val

theorem fixedFieldToSepClosure_apply (x : inertiaFixedField F) :
    fixedFieldToSepClosure F x = (x : SeparableClosure F) := rfl

theorem fixedFieldToSepClosure_comp_baseToFixedField :
    (fixedFieldToSepClosure F).comp (baseToFixedField F) = Algebra.ofId F (SeparableClosure F) :=
  AlgHom.ext fun _ => rfl

/-! ### Valuations and integer rings -/

def sepClosureValuation : Valuation (SeparableClosure F) ℝ≥0 :=
  spectralValuation F (SeparableClosure F)

abbrev sepClosureIntegers : ValuationSubring (SeparableClosure F) :=
  (sepClosureValuation F).valuationSubring

theorem sepClosureIntegers_eq :
    sepClosureIntegers F = extensionIntegers F (SeparableClosure F) := rfl

theorem sepClosureValuation_apply (x : SeparableClosure F) :
    (sepClosureValuation F x : ℝ) = spectralNorm F (SeparableClosure F) x := rfl

instance sepClosureValuation_extends :
    (valuation F).HasExtension (sepClosureValuation F) where
  val_isEquiv_comap x y := by
    change valuation F x ≤ valuation F y ↔
      spectralNorm F (SeparableClosure F) (algebraMap F (SeparableClosure F) x) ≤
        spectralNorm F (SeparableClosure F) (algebraMap F (SeparableClosure F) y)
    simp only [spectralNorm_extends]
    exact (localNormedField_le F x y).symm

def fixedFieldValuation : Valuation (inertiaFixedField F) ℝ≥0 :=
  (sepClosureValuation F).comap (algebraMap (inertiaFixedField F) (SeparableClosure F))

theorem fixedFieldValuation_apply (x : inertiaFixedField F) :
    fixedFieldValuation F x = sepClosureValuation F (x : SeparableClosure F) := rfl

theorem fixedFieldValuation_eq_spectralValuation :
    fixedFieldValuation F = spectralValuation F (inertiaFixedField F) := by
  ext x
  change spectralNorm F (SeparableClosure F) (algebraMap (inertiaFixedField F) _ x) =
    spectralNorm F (inertiaFixedField F) x
  exact (spectralNorm.eq_of_tower x).symm

abbrev fixedFieldIntegers : ValuationSubring (inertiaFixedField F) :=
  (fixedFieldValuation F).valuationSubring

theorem fixedFieldIntegers_eq :
    fixedFieldIntegers F = extensionIntegers F (inertiaFixedField F) := by
  rw [fixedFieldIntegers, fixedFieldValuation_eq_spectralValuation]

instance fixedFieldValuation_extends :
    (valuation F).HasExtension (fixedFieldValuation F) where
  val_isEquiv_comap x y :=
    (sepClosureValuation_extends F).val_isEquiv_comap x y

instance sepClosureValuation_extends_fixedField :
    (fixedFieldValuation F).HasExtension (sepClosureValuation F) where
  val_isEquiv_comap _ _ := Iff.rfl

def fixedFieldIntegersEquiv :
    fixedFieldIntegers F ≃+* extensionIntegers F (inertiaFixedField F) :=
  RingEquiv.subringCongr (congrArg ValuationSubring.toSubring (fixedFieldIntegers_eq F))

theorem coe_fixedFieldIntegersEquiv (x : fixedFieldIntegers F) :
    ((fixedFieldIntegersEquiv F x : extensionIntegers F (inertiaFixedField F)) :
      inertiaFixedField F) = x := rfl

/-! ### Integer maps -/

def integerToFixedField : 𝒪[F] →+* fixedFieldIntegers F :=
  algebraMap (valuation F).valuationSubring (fixedFieldValuation F).valuationSubring

def fixedFieldIntegerInclusion : fixedFieldIntegers F →+* sepClosureIntegers F :=
  algebraMap (fixedFieldValuation F).valuationSubring (sepClosureValuation F).valuationSubring

def integerToSepClosure : 𝒪[F] →+* sepClosureIntegers F :=
  algebraMap (valuation F).valuationSubring (sepClosureValuation F).valuationSubring

theorem coe_integerToFixedField (x : 𝒪[F]) :
    (integerToFixedField F x : inertiaFixedField F) = algebraMap F _ (x : F) := rfl

theorem coe_fixedFieldIntegerInclusion (x : fixedFieldIntegers F) :
    (fixedFieldIntegerInclusion F x : SeparableClosure F) = ((x : inertiaFixedField F) :
      SeparableClosure F) := rfl

theorem coe_integerToSepClosure (x : 𝒪[F]) :
    (integerToSepClosure F x : SeparableClosure F) = algebraMap F _ (x : F) := rfl

theorem fixedFieldIntegerInclusion_comp_integerToFixedField :
    (fixedFieldIntegerInclusion F).comp (integerToFixedField F) = integerToSepClosure F :=
  RingHom.ext fun _ => rfl

instance integerToFixedField_isLocalHom : IsLocalHom (integerToFixedField F) :=
  inferInstanceAs (IsLocalHom (algebraMap (valuation F).valuationSubring
    (fixedFieldValuation F).valuationSubring))

instance fixedFieldIntegerInclusion_isLocalHom : IsLocalHom (fixedFieldIntegerInclusion F) :=
  inferInstanceAs (IsLocalHom (algebraMap (fixedFieldValuation F).valuationSubring
    (sepClosureValuation F).valuationSubring))

instance integerToSepClosure_isLocalHom : IsLocalHom (integerToSepClosure F) :=
  inferInstanceAs (IsLocalHom (algebraMap (valuation F).valuationSubring
    (sepClosureValuation F).valuationSubring))

theorem integerInclusion_fixedFieldIntegersEquiv (x : fixedFieldIntegers F) :
    integerInclusion F (SeparableClosure F) (inertiaFixedField F) (fixedFieldIntegersEquiv F x) =
      fixedFieldIntegerInclusion F x := rfl

theorem integerToFixedField_localNormedField (x : baseIntegers F) :
    integerToFixedField F (RingEquiv.subringCongr (localNormedField_integer F) x) =
      (fixedFieldIntegersEquiv F).symm
        (algebraMap (baseIntegers F) (extensionIntegers F (inertiaFixedField F)) x) := rfl

theorem integerToSepClosure_localNormedField (x : baseIntegers F) :
    integerToSepClosure F (RingEquiv.subringCongr (localNormedField_integer F) x) =
      algebraMap (baseIntegers F) (extensionIntegers F (SeparableClosure F)) x := rfl

/-! ### Residue maps -/

def residueToFixedField : 𝓀[F] →+* ResidueField (fixedFieldIntegers F) :=
  ResidueField.map (integerToFixedField F)

def fixedFieldResidueInclusion :
    ResidueField (fixedFieldIntegers F) →+* ResidueField (sepClosureIntegers F) :=
  ResidueField.map (fixedFieldIntegerInclusion F)

def residueToSepClosure : 𝓀[F] →+* ResidueField (sepClosureIntegers F) :=
  ResidueField.map (integerToSepClosure F)

theorem residueToFixedField_residue (x : 𝒪[F]) :
    residueToFixedField F (residue _ x) = residue _ (integerToFixedField F x) := rfl

theorem fixedFieldResidueInclusion_residue (x : fixedFieldIntegers F) :
    fixedFieldResidueInclusion F (residue _ x) = residue _ (fixedFieldIntegerInclusion F x) := rfl

theorem residueToSepClosure_residue (x : 𝒪[F]) :
    residueToSepClosure F (residue _ x) = residue _ (integerToSepClosure F x) := rfl

theorem fixedFieldResidueInclusion_comp_residueToFixedField :
    (fixedFieldResidueInclusion F).comp (residueToFixedField F) = residueToSepClosure F := by
  ext x
  obtain ⟨x, rfl⟩ := residue_surjective x
  rfl

theorem residueInclusion_fixedFieldIntegersEquiv (x : ResidueField (fixedFieldIntegers F)) :
    residueInclusion F (SeparableClosure F) (inertiaFixedField F)
        (ResidueField.mapEquiv (fixedFieldIntegersEquiv F) x) =
      fixedFieldResidueInclusion F x := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rw [ResidueField.mapEquiv_apply, ResidueField.map_residue, residueInclusion,
    ResidueField.mapAlgHom'_residue, fixedFieldResidueInclusion_residue]
  exact congrArg (residue _) (integerInclusion_fixedFieldIntegersEquiv F x)

theorem residueToFixedField_localResidueEquiv (x : ResidueField (baseIntegers F)) :
    residueToFixedField F (localResidueEquiv F x) =
      (ResidueField.mapEquiv (fixedFieldIntegersEquiv F)).symm
        (algebraMap (ResidueField (baseIntegers F))
          (ResidueField (extensionIntegers F (inertiaFixedField F))) x) := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rfl

theorem residueToSepClosure_localResidueEquiv (x : ResidueField (baseIntegers F)) :
    residueToSepClosure F (localResidueEquiv F x) =
      algebraMap (ResidueField (baseIntegers F))
        (ResidueField (extensionIntegers F (SeparableClosure F))) x := by
  obtain ⟨x, rfl⟩ := residue_surjective x
  rfl

/-! ### Topologies -/

@[instance_reducible]
def sepClosureNormedField : NontriviallyNormedField (SeparableClosure F) :=
  spectralNorm.nontriviallyNormedField F (SeparableClosure F)

theorem sepClosureNormedField_norm (x : SeparableClosure F) :
    (sepClosureNormedField F).norm x = spectralNorm F (SeparableClosure F) x := rfl

@[instance_reducible]
def sepClosureTopology : TopologicalSpace (SeparableClosure F) :=
  (sepClosureNormedField F).toUniformSpace.toTopologicalSpace

@[instance_reducible]
def fixedFieldValued : Valued (inertiaFixedField F) ℝ≥0 :=
  Valued.mk' (fixedFieldValuation F)

@[instance_reducible]
def fixedFieldTopology : TopologicalSpace (inertiaFixedField F) :=
  (fixedFieldValued F).toUniformSpace.toTopologicalSpace

theorem fixedFieldTopology_eq_induced :
    fixedFieldTopology F =
      (sepClosureTopology F).induced ((↑) : inertiaFixedField F → SeparableClosure F) := by
  have h₁ : @IsTopologicalAddGroup (inertiaFixedField F) (fixedFieldTopology F) _ := by
    let := fixedFieldValued F
    exact inferInstance
  have h₂ : @IsTopologicalAddGroup (inertiaFixedField F)
      ((sepClosureTopology F).induced ((↑) : inertiaFixedField F → SeparableClosure F)) _ := by
    let := sepClosureNormedField F
    exact isTopologicalAddGroup_induced (algebraMap (inertiaFixedField F) (SeparableClosure F))
  refine IsTopologicalAddGroup.ext h₁ h₂ ?_
  have hb₁ := @Valued.hasBasis_nhds_zero (inertiaFixedField F) _ ℝ≥0 _ (fixedFieldValued F)
  have hb₂ := (@Metric.nhds_basis_ball (SeparableClosure F)
    (sepClosureNormedField F).toPseudoMetricSpace 0).comap
      ((↑) : inertiaFixedField F → SeparableClosure F)
  refine (hb₁.ext hb₂ ?_ ?_).trans (@nhds_induced _ _ (sepClosureTopology F) _ 0).symm
  · intro γ _
    let e := MonoidWithZeroHom.ValueGroup₀.embedding
      (f := MonoidWithZeroHom.ofClass (fixedFieldValued F).v)
    have hγ : e γ.1 ≠ 0 := by
      intro h
      apply γ.ne_zero
      rw [← map_zero e] at h
      exact MonoidWithZeroHom.ValueGroup₀.embedding_injective h
    refine ⟨e γ.1, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ), ?_⟩
    intro x hx
    change spectralNorm F (SeparableClosure F) ((x : SeparableClosure F) - 0) < _ at hx
    rw [sub_zero] at hx
    have hx' : (fixedFieldValued F).v x < e γ.1 := NNReal.coe_lt_coe.mp hx
    exact (Valuation.restrict_lt_iff_lt_embedding (fixedFieldValued F).v).mpr hx'
  · intro ε hε
    obtain ⟨a, ha₀, haε⟩ := NormedField.exists_norm_lt F hε
    have hva : (fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) : ℝ) = ‖a‖ :=
      spectralNorm_extends a
    have hne : (fixedFieldValued F).v.restrict (algebraMap F (inertiaFixedField F) a) ≠ 0 := by
      rw [Ne, Valuation.restrict_eq_zero_iff]
      intro h
      change fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) = 0 at h
      rw [h, NNReal.coe_zero] at hva
      exact ha₀.ne hva
    refine ⟨Units.mk0 _ hne, trivial, ?_⟩
    intro x hx
    have hx' : fixedFieldValuation F x < fixedFieldValuation F (algebraMap F _ a) :=
      (Valuation.restrict_lt_iff (fixedFieldValued F).v).mp hx
    change spectralNorm F (SeparableClosure F) ((x : SeparableClosure F) - 0) < ε
    rw [sub_zero]
    change (fixedFieldValuation F x : ℝ) < ε
    exact ((NNReal.coe_lt_coe.mpr hx').trans_eq hva).trans haε

end Langlands.LocalGalois.Separable

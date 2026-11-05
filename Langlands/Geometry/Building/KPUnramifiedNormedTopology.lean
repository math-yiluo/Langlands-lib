import Langlands.Geometry.Building.KPZeroSubgroups
import Langlands.Galois.Local.SeparableHenselian
import Langlands.AlgebraicGeometry.PointTopology.HenselianSmoothOpenMapStatement
import Mathlib.Topology.Algebra.Valued.NormedValued

/-! # The actual maximal unramified field as a Henselian normed field -/

noncomputable section

universe u

open CategoryTheory _root_.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped NNReal Topology

namespace Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance kpUnramifiedBaseNormedField : NontriviallyNormedField F := localNormedField F
local instance kpUnramifiedBaseUltrametric : IsUltrametricDist F := localNormedField_ultrametric F
local instance kpUnramifiedBaseComplete : CompleteSpace F := localNormedField_complete F

/-- For a field embedded in `F^sep` and containing elements of arbitrarily small positive
spectral norm, the topology of the restricted spectral valuation is the subspace topology. -/
theorem comapValuedTopology_eq_induced {E : Type u} [Field E] (ι : E →+* SeparableClosure F)
    (hι : ∀ ε : ℝ, 0 < ε → ∃ x : E, 0 < spectralNorm F (SeparableClosure F) (ι x) ∧
      spectralNorm F (SeparableClosure F) (ι x) < ε) :
    (Valued.mk' ((sepClosureValuation F).comap ι)).toUniformSpace.toTopologicalSpace =
      (sepClosureTopology F).induced ι := by
  let v : Valuation E ℝ≥0 := (sepClosureValuation F).comap ι
  let V : Valued E ℝ≥0 := Valued.mk' v
  have h₁ : @IsTopologicalAddGroup E V.toUniformSpace.toTopologicalSpace _ := by
    let := V
    exact inferInstance
  have h₂ : @IsTopologicalAddGroup E ((sepClosureTopology F).induced ι) _ := by
    let := sepClosureNormedField F
    exact isTopologicalAddGroup_induced ι
  refine IsTopologicalAddGroup.ext h₁ h₂ ?_
  have hb₁ := @Valued.hasBasis_nhds_zero E _ ℝ≥0 _ V
  have hb₂ := (@Metric.nhds_basis_ball (SeparableClosure F)
    (sepClosureNormedField F).toPseudoMetricSpace 0).comap ι
  have hn : @nhds E ((sepClosureTopology F).induced ι) 0 =
      Filter.comap ι (@nhds (SeparableClosure F) (sepClosureTopology F) 0) := by
    rw [@nhds_induced _ _ (sepClosureTopology F) ι 0, map_zero]
  refine (hb₁.ext hb₂ ?_ ?_).trans hn.symm
  · intro γ _
    let e := MonoidWithZeroHom.ValueGroup₀.embedding (f := MonoidWithZeroHom.ofClass V.v)
    have hγ : e γ.1 ≠ 0 := by
      intro h
      apply γ.ne_zero
      rw [← map_zero e] at h
      exact MonoidWithZeroHom.ValueGroup₀.embedding_injective h
    refine ⟨e γ.1, NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hγ), ?_⟩
    intro x hx
    change spectralNorm F (SeparableClosure F) (ι x - 0) < _ at hx
    rw [sub_zero] at hx
    have hx' : V.v x < e γ.1 := NNReal.coe_lt_coe.mp hx
    exact (Valuation.restrict_lt_iff_lt_embedding V.v).mpr hx'
  · intro ε hε
    obtain ⟨a, ha₀, haε⟩ := hι ε hε
    have hva : (v a : ℝ) = spectralNorm F (SeparableClosure F) (ι a) := rfl
    have hne : V.v.restrict a ≠ 0 := by
      rw [Ne, Valuation.restrict_eq_zero_iff]
      intro h
      change v a = 0 at h
      rw [h, NNReal.coe_zero] at hva
      exact ha₀.ne hva
    refine ⟨Units.mk0 _ hne, trivial, ?_⟩
    intro x hx
    have hx' : v x < v a := (Valuation.restrict_lt_iff V.v).mp hx
    change spectralNorm F (SeparableClosure F) (ι x - 0) < ε
    rw [sub_zero]
    change (v x : ℝ) < ε
    exact ((NNReal.coe_lt_coe.mpr hx').trans_eq hva).trans haε

/-- The normed field structure on the actual inertia fixed field restricted from the
spectral norm on `F^sep`. -/
@[instance_reducible]
def fixedFieldNormedField : NontriviallyNormedField (inertiaFixedField F) :=
  letI : NontriviallyNormedField (SeparableClosure F) := sepClosureNormedField F
  { SubfieldClass.toNormedField (inertiaFixedField F) with
    non_trivial := by
      obtain ⟨x, hx⟩ := NontriviallyNormedField.non_trivial (α := F)
      refine ⟨algebraMap F (inertiaFixedField F) x, ?_⟩
      change 1 < spectralNorm F (SeparableClosure F) (algebraMap F (SeparableClosure F) x)
      rw [spectralNorm_extends]
      exact hx }

theorem fixedFieldNormedField_norm (x : inertiaFixedField F) :
    (fixedFieldNormedField F).norm x =
      spectralNorm F (SeparableClosure F) (x : SeparableClosure F) := rfl

/-- The norm topology is the published fixed-field topology. -/
theorem fixedFieldNormedField_topology :
    (fixedFieldNormedField F).toUniformSpace.toTopologicalSpace = fixedFieldTopology F := by
  rw [fixedFieldTopology_eq_induced]
  rfl

/-- The restricted spectral norm is ultrametric. -/
theorem fixedFieldNormedField_isUltrametricDist :
    @IsUltrametricDist (inertiaFixedField F) (fixedFieldNormedField F).toDist := by
  let : NontriviallyNormedField (inertiaFixedField F) := fixedFieldNormedField F
  apply IsUltrametricDist.isUltrametricDist_of_isNonarchimedean_norm
  intro x y
  exact isNonarchimedean_spectralNorm (K := F) (L := SeparableClosure F)
    (x : SeparableClosure F) (y : SeparableClosure F)

/-- The norm valuation is the published fixed-field valuation. -/
theorem fixedFieldNormedField_valuation :
    letI : NontriviallyNormedField (inertiaFixedField F) := fixedFieldNormedField F
    letI : IsUltrametricDist (inertiaFixedField F) := fixedFieldNormedField_isUltrametricDist F
    NormedField.valuation (K := inertiaFixedField F) = fixedFieldValuation F := by
  let : NontriviallyNormedField (inertiaFixedField F) := fixedFieldNormedField F
  let : IsUltrametricDist (inertiaFixedField F) := fixedFieldNormedField_isUltrametricDist F
  ext x
  rfl

/-- The norm valuation ring is the Henselian published fixed-field integer ring. -/
theorem fixedFieldNormedField_henselian :
    letI : NontriviallyNormedField (inertiaFixedField F) := fixedFieldNormedField F
    letI : IsUltrametricDist (inertiaFixedField F) := fixedFieldNormedField_isUltrametricDist F
    HenselianLocalRing (NormedField.valuation (K := inertiaFixedField F)).valuationSubring := by
  let : NontriviallyNormedField (inertiaFixedField F) := fixedFieldNormedField F
  let : IsUltrametricDist (inertiaFixedField F) := fixedFieldNormedField_isUltrametricDist F
  rw [fixedFieldNormedField_valuation F]
  exact fixedFieldIntegersIsHenselian F

end Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

open LocalGalois LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance kpUnramifiedBaseNormedField' : NontriviallyNormedField F := localNormedField F
local instance kpUnramifiedBaseUltrametric' : IsUltrametricDist F := localNormedField_ultrametric F
local instance kpUnramifiedBaseComplete' : CompleteSpace F := localNormedField_complete F

/-- The topology of the actual intermediate valuation is the subspace topology from `F^sep`. -/
theorem intermediateValuationTopology_eq_induced
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    (Valued.mk' (intermediateValuation F L)).toUniformSpace.toTopologicalSpace =
      (sepClosureTopology F).induced ((↑) : L → SeparableClosure F) := by
  refine comapValuedTopology_eq_induced F (algebraMap L (SeparableClosure F)) ?_
  intro ε hε
  obtain ⟨a, ha₀, haε⟩ := NormedField.exists_norm_lt F hε
  refine ⟨algebraMap (UnramifiedClosure F) L (algebraMap F (UnramifiedClosure F) a), ?_, ?_⟩
  · change 0 < spectralNorm F (SeparableClosure F) (algebraMap F (SeparableClosure F) a)
    rwa [spectralNorm_extends]
  · change spectralNorm F (SeparableClosure F) (algebraMap F (SeparableClosure F) a) < ε
    rwa [spectralNorm_extends]

/-- Scalar multiplication by the maximal unramified field on an intermediate field of
`F^sep/K` is continuous for the published fixed-field topology and the topology of the
actual intermediate valuation. -/
theorem intermediateValuation_continuousSMul
    (L : IntermediateField (UnramifiedClosure F) (SeparableClosure F)) :
    @ContinuousSMul (UnramifiedClosure F) L _ (fixedFieldTopology F)
      (Valued.mk' (intermediateValuation F L)).toUniformSpace.toTopologicalSpace := by
  rw [intermediateValuationTopology_eq_induced, fixedFieldTopology_eq_induced]
  let : NontriviallyNormedField (SeparableClosure F) := sepClosureNormedField F
  let : TopologicalSpace (UnramifiedClosure F) :=
    (sepClosureTopology F).induced ((↑) : UnramifiedClosure F → SeparableClosure F)
  let : TopologicalSpace L := (sepClosureTopology F).induced ((↑) : L → SeparableClosure F)
  refine ⟨continuous_induced_rng.mpr ?_⟩
  have h : Continuous fun p : UnramifiedClosure F × L =>
      ((p.1 : SeparableClosure F) * (p.2 : SeparableClosure F)) :=
    (continuous_induced_dom.comp continuous_fst).mul (continuous_induced_dom.comp continuous_snd)
  exact h

/-- The Henselian smooth-openness statement applied to the actual maximal unramified field
with its published topology. -/
theorem isOpenMap_rationalPoint_of_smooth
    (hH : HenselianSmoothRationalPointOpenMapStatement.{u})
    (X Y : Over (Spec (CommRingCat.of (UnramifiedClosure F)))) [IsAffine X.left]
    [IsAffine Y.left] (f : X ⟶ Y) [Smooth f.left] :
    letI : TopologicalSpace (UnramifiedClosure F) := fixedFieldTopology F
    letI : TopologicalSpace (RationalPoint (UnramifiedClosure F) X) :=
      rationalPointTopology (UnramifiedClosure F) X
    letI : TopologicalSpace (RationalPoint (UnramifiedClosure F) Y) :=
      rationalPointTopology (UnramifiedClosure F) Y
    IsOpenMap (fun p : RationalPoint (UnramifiedClosure F) X => p ≫ f) := by
  let : NontriviallyNormedField (UnramifiedClosure F) := fixedFieldNormedField F
  let : IsUltrametricDist (UnramifiedClosure F) := fixedFieldNormedField_isUltrametricDist F
  let : HenselianLocalRing (NormedField.valuation (K := UnramifiedClosure F)).valuationSubring :=
    fixedFieldNormedField_henselian F
  have h := hH (UnramifiedClosure F) X Y f
  rw [← fixedFieldNormedField_topology F]
  exact h

end Langlands.Geometry.Building

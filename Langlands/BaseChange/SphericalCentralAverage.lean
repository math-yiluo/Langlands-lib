import Langlands.BaseChange.CyclicNormDeterminant
import Langlands.BaseChange.OrbitalIntegral
import Langlands.BaseChange.SatakeCharacterStatement
import Langlands.ClassFieldTheory.Local.NormExistenceClosedSupport
import Langlands.Group.GL.UnramifiedCharacter
import Langlands.LocalField.CanonicalTransport

/-! # Removing central averages at a fixed determinant order -/

noncomputable section

namespace Langlands.BaseChange

open ClassFieldTheory.Local Correspondence HarmonicAnalysis MeasureTheory TraceFormula Unramified

universe u v

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel
attribute [local instance high] leftQuotientMeasurableSpace

section SingleField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)

private theorem scalar_mem_spherical_of_mem_unitSubgroup {r : ℕ} {z : F.Carrierˣ}
    (hz : z ∈ F.canonicalTopologicalData.unitSubgroup) :
    GeneralLinear.scalar (n := r + 1) z ∈ sphericalSubgroup F r := by
  let vF := ValuativeRel.valuation F.Carrier
  change GeneralLinear.scalar z ∈ Conductor.integralSubgroup vF.integer r
  have hval (a : F.Carrierˣ) (ha : a ∈ F.canonicalTopologicalData.unitSubgroup) :
      vF (a : F.Carrier) = 1 := (Valuation.mem_unitGroup_iff F.Carrier vF a).mp ha
  have hent (a : F.Carrierˣ) (ha : a ∈ F.canonicalTopologicalData.unitSubgroup) (i j : Fin (r + 1)) :
      GeneralLinear.scalar (n := r + 1) a i j ∈ vF.integer := by
    change Matrix.scalar (Fin (r + 1)) (a : F.Carrier) i j ∈ vF.integer
    by_cases hij : i = j
    · subst j
      rw [Matrix.scalar_apply, Matrix.diagonal_apply_eq]
      change vF (a : F.Carrier) ≤ 1
      exact (hval a ha).le
    · rw [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
      exact vF.integer.zero_mem
  apply (Conductor.mem_integralSubgroup vF.integer r _).mpr
  refine ⟨hent z hz, ?_⟩
  rw [← map_inv]
  exact hent z⁻¹ (F.canonicalTopologicalData.unitSubgroup.inv_mem hz)

private theorem ord_determinant_scalar_mul {r : ℕ} (a : F.Carrierˣ)
    (g : GeneralLinear (r + 1) F.Carrier) :
    F.canonicalTopologicalData.ord (GeneralLinear.determinant (GeneralLinear.scalar a * g) : F.Carrier) =
      (r + 1 : ℕ) * F.canonicalTopologicalData.ord (a : F.Carrier) +
        F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) := by
  let T := F.canonicalTopologicalData
  have h : GeneralLinear.determinant (GeneralLinear.scalar (n := r + 1) a * g) =
      a ^ (r + 1) * GeneralLinear.determinant g := by
    rw [map_mul, GeneralLinear.determinant, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin]
  rw [h, Units.val_mul, T.ord_mul (Units.ne_zero _) (Units.ne_zero _)]
  rw [Units.val_pow_eq_pow_val, ← zpow_natCast, T.ord_zpow]

/-- At the supported determinant order, central averaging with a weight trivial
on integral units and mass one on those units has the original value. -/
theorem centralAverage_apply_of_det_order {r : ℕ} (f : SphericalHeckeAlgebra F r) (m : ℤ)
    (hf : ∀ x : GeneralLinear (r + 1) F.Carrier,
      F.canonicalTopologicalData.ord (GeneralLinear.determinant x : F.Carrier) ≠ m → f x = 0)
    (C : Subgroup F.Carrierˣ) [MeasurableSpace C] [BorelSpace C] (μ : Measure C)
    (hμ : μ {z : C | z.val ∈ F.canonicalTopologicalData.unitSubgroup} = 1)
    (χ : C → ℂ) (hχ : ∀ z : C, z.val ∈ F.canonicalTopologicalData.unitSubgroup → χ z = 1)
    (g : GeneralLinear (r + 1) F.Carrier)
    (hg : F.canonicalTopologicalData.ord (GeneralLinear.determinant g : F.Carrier) = m) :
    (∫ z : C, χ z * f (GeneralLinear.scalar z.val * g) ∂μ) = f g := by
  classical
  let T := F.canonicalTopologicalData
  let U : Set C := {z | z.val ∈ T.unitSubgroup}
  have hU : MeasurableSet U :=
    ((isOpen_unitSubgroup F T).preimage continuous_subtype_val).measurableSet
  have hfun : (fun z : C => χ z * f (GeneralLinear.scalar z.val * g)) =
      U.indicator (fun _ => f g) := by
    funext z
    by_cases hz : z ∈ U
    · rw [Set.indicator_of_mem hz, hχ z hz, one_mul]
      exact f.property.1 ⟨GeneralLinear.scalar z.val, scalar_mem_spherical_of_mem_unitSubgroup F hz⟩ g
    · rw [Set.indicator_of_notMem hz]
      rw [hf, mul_zero]
      rw [ord_determinant_scalar_mul F, hg, add_ne_right]
      exact mul_ne_zero (by positivity) (fun h => hz ((mem_unitSubgroup_iff_ord_eq_zero F T z.val).mpr h))
  rw [hfun, integral_indicator_const _ hU]
  change (μ U).toReal • f g = f g
  rw [hμ, ENNReal.toReal_one, one_smul]

end SingleField

section Pair

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) (E : PadicField.{v} p)
  [Algebra F.Carrier E.Carrier] [IsScalarTower (Padic p) F.Carrier E.Carrier]
  (σ : E.Carrier ≃ₐ[F.Carrier] E.Carrier) {l r : ℕ}

private theorem determinant_order_twistedConj (δ x : GeneralLinear (r + 1) E.Carrier) :
    E.canonicalTopologicalData.ord
      (GeneralLinear.determinant (x⁻¹ * δ * entrywiseAut σ (r + 1) x) : E.Carrier) =
      E.canonicalTopologicalData.ord (GeneralLinear.determinant δ : E.Carrier) := by
  let T := E.canonicalTopologicalData
  have hσ : T.ord (GeneralLinear.determinant (entrywiseAut σ (r + 1) x) : E.Carrier) =
      T.ord (GeneralLinear.determinant x : E.Carrier) := by
    have hdet : (GeneralLinear.determinant (entrywiseAut σ (r + 1) x) : E.Carrier) =
        σ (GeneralLinear.determinant x : E.Carrier) := (σ.map_det x.val).symm
    rw [hdet]
    exact PadicField.CanonicalTransport.ord_map E E (σ.restrictScalars (Padic p)) _
  change (T.ordUnits (GeneralLinear.determinant (x⁻¹ * δ * entrywiseAut σ (r + 1) x))).toAdd = _
  simp only [map_mul, map_inv]
  change -T.ord (GeneralLinear.determinant x : E.Carrier) +
    T.ord (GeneralLinear.determinant δ : E.Carrier) +
    T.ord (GeneralLinear.determinant (entrywiseAut σ (r + 1) x) : E.Carrier) = _
  rw [hσ]
  ring

private theorem determinant_order_conj (γ x : GeneralLinear (r + 1) F.Carrier) :
    F.canonicalTopologicalData.ord (GeneralLinear.determinant (x⁻¹ * γ * x) : F.Carrier) =
      F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier) := by
  have h : GeneralLinear.determinant (x⁻¹ * γ * x) = GeneralLinear.determinant γ := by
    rw [map_mul, map_mul, map_inv, mul_right_comm, inv_mul_cancel, one_mul]
  exact congrArg (fun a : F.Carrierˣ => F.canonicalTopologicalData.ord (a : F.Carrier)) h

/-- If the two tests are supported at associated determinant orders, concordance
of their central averages at a norm pair implies concordance of the tests. -/
def SphericalCentralAverageReductionStatement : Prop :=
  ∀ {δ : GeneralLinear (r + 1) E.Carrier} {γ : GeneralLinear (r + 1) F.Carrier},
    IsNormAssociated σ l δ γ → IsCyclicAlgebra σ l →
    E.canonicalTopologicalData.ramificationIndex = F.canonicalTopologicalData.ramificationIndex →
    ∀ (φ : SphericalHeckeAlgebra E r) (f : SphericalHeckeAlgebra F r) (m : ℤ),
    (∀ x : GeneralLinear (r + 1) E.Carrier,
      E.canonicalTopologicalData.ord (GeneralLinear.determinant x : E.Carrier) ≠ m → φ x = 0) →
    (∀ x : GeneralLinear (r + 1) F.Carrier,
      F.canonicalTopologicalData.ord (GeneralLinear.determinant x : F.Carrier) ≠
        (l : ℤ) * m → f x = 0) →
    ∀ (CE : Subgroup E.Carrierˣ) [MeasurableSpace CE] [BorelSpace CE] (μCE : Measure CE)
    (χE : CE → ℂ)
    (CF : Subgroup F.Carrierˣ) [MeasurableSpace CF] [BorelSpace CF] (μCF : Measure CF)
    (χF : CF → ℂ),
    μCE {z : CE | z.val ∈ E.canonicalTopologicalData.unitSubgroup} = 1 →
    (∀ z : CE, z.val ∈ E.canonicalTopologicalData.unitSubgroup → χE z = 1) →
    μCF {z : CF | z.val ∈ F.canonicalTopologicalData.unitSubgroup} = 1 →
    (∀ z : CF, z.val ∈ F.canonicalTopologicalData.unitSubgroup → χF z = 1) →
    ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r)
      (fun x => ∫ z : CE, χE z * φ (GeneralLinear.scalar z.val * x) ∂μCE)
      (fun x => ∫ z : CF, χF z * f (GeneralLinear.scalar z.val * x) ∂μCF) δ γ →
    ConcordAt σ l (sphericalHaar F r) (sphericalHaar E r) ⇑φ ⇑f δ γ

theorem sphericalCentralAverageReduction :
    SphericalCentralAverageReductionStatement F E σ (l := l) (r := r) := by
  intro δ γ hAssoc hcyc he φ f m hφ hf CE _ _ μCE χE CF _ _ μCF χF hμCE hχE hμCF hχF hAvg
    μδ _ _ μγ _ _ νδ νγ hνδ hνγ hmeasure
  let θ := entrywiseAut σ (r + 1)
  let φAvg := fun x : GeneralLinear (r + 1) E.Carrier =>
    ∫ z : CE, χE z * φ (GeneralLinear.scalar z.val * x) ∂μCE
  let fAvg := fun x : GeneralLinear (r + 1) F.Carrier =>
    ∫ z : CF, χF z * f (GeneralLinear.scalar z.val * x) ∂μCF
  have hdeg := hAssoc.ord_determinant_eq hcyc he
  by_cases hδ : E.canonicalTopologicalData.ord (GeneralLinear.determinant δ : E.Carrier) = m
  · have hγ : F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier) = (l : ℤ) * m :=
      hdeg.trans (congrArg ((l : ℤ) * ·) hδ)
    have hE : twistedOrbitFunction θ δ φAvg = twistedOrbitFunction θ δ ⇑φ := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        simp only [twistedOrbitFunction_mk]
        exact centralAverage_apply_of_det_order E φ m hφ CE μCE hμCE χE hχE _
          ((determinant_order_twistedConj F E σ δ x).trans hδ)
    have hF : twistedOrbitFunction (MonoidHom.id _) γ fAvg =
        twistedOrbitFunction (MonoidHom.id _) γ ⇑f := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        simp only [twistedOrbitFunction_mk, MonoidHom.id_apply]
        exact centralAverage_apply_of_det_order F f _ hf CF μCF hμCF χF hχF _
          ((determinant_order_conj F γ x).trans hγ)
    have h := hAvg μδ μγ νδ νγ hνδ hνγ hmeasure
    change (∫ x, twistedOrbitFunction θ δ φAvg x ∂νδ) =
      (∫ x, twistedOrbitFunction (MonoidHom.id _) γ fAvg x ∂νγ) at h
    rw [hE, hF] at h
    exact h
  · have hγ : F.canonicalTopologicalData.ord (GeneralLinear.determinant γ : F.Carrier) ≠ (l : ℤ) * m := by
      rw [hdeg]
      exact fun h => hδ (mul_left_cancel₀ (by exact_mod_cast hcyc.pos.ne') h)
    have hE : twistedOrbitFunction θ δ ⇑φ = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        simp only [twistedOrbitFunction_mk, Pi.zero_apply]
        exact hφ _ (fun h => hδ ((determinant_order_twistedConj F E σ δ x).symm.trans h))
    have hF : twistedOrbitFunction (MonoidHom.id _) γ ⇑f = 0 := by
      funext q
      induction q using Quotient.inductionOn with
      | h x =>
        simp only [twistedOrbitFunction_mk, MonoidHom.id_apply, Pi.zero_apply]
        exact hf _ (fun h => hγ ((determinant_order_conj F γ x).symm.trans h))
    change (∫ x, twistedOrbitFunction θ δ ⇑φ x ∂νδ) =
      (∫ x, twistedOrbitFunction (MonoidHom.id _) γ ⇑f x ∂νγ)
    rw [hE, hF]
    simp

end Pair

end Langlands.BaseChange

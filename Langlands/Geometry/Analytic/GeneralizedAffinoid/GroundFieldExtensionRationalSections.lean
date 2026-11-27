import Langlands.Geometry.Analytic.GeneralizedAffinoid.GroundFieldExtensionCoefficientNorm
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalChartRingEvaluation
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalNormSectionContinuity

/-! # Semilinear section operators on weighted rational charts -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

open Set Filter GeneralizedTateAlgebra
open scoped Topology

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type v) [NormedField L] [IsUltrametricDist L] [CompleteSpace L] [NormedAlgebra K L]
  (A : PresentedAffinoidAlgebra K)

private abbrev CoefficientGroup : Type v := ↥(isometricAutomorphisms K L)

local notation "B" => algebra K L A
local notation "Γ" => CoefficientGroup K L

variable (d : RationalChart L (algebra K L A))

private def movedBase (σ : Γ) : BoundedRingHom B d.algebra :=
  d.baseMap.toBoundedRingHom.comp (coefficientHom K L A σ).toBoundedRingHom

private theorem norm_movedBase_le (σ : Γ) (b : B) : ‖movedBase K L A d σ b‖ ≤ ‖b‖ := by
  change ‖d.baseMap (coefficientHom K L A σ b)‖ ≤ ‖b‖
  exact (RationalPresentation.norm_baseMap_le L B d.radii d.denominator d.numerators
    _).trans (norm_coefficientHom_le K L A σ b)

private theorem movedBase_one (b : B) : movedBase K L A d 1 b = d.baseMap b := by
  change d.baseMap (coefficientHom K L A 1 b) = _
  rw [coefficientHom_one, BoundedAlgHom.id_apply]

private def movedFraction (σ : Γ) (j : Fin d.arity) : d.algebra :=
  Ring.inverse (movedBase K L A d σ d.denominatorClass) *
    movedBase K L A d σ (d.numeratorClass j)

private theorem movedFraction_one (j : Fin d.arity) :
    movedFraction K L A d 1 j = d.fractionCoordinate j := by
  unfold movedFraction
  rw [movedBase_one, movedBase_one]
  exact (d.map_fractionCoordinate_eq_inverse_mul (BoundedAlgHom.id L d.algebra) j).symm

private def HasRationalLift (σ : Γ) : Prop :=
  ∃ φ : BoundedRingHom d.algebra d.algebra,
    (∀ b : B, φ (d.baseMap b) = movedBase K L A d σ b) ∧ ∀ t, ‖φ t‖ ≤ ‖t‖

private theorem hasRationalLift_one : HasRationalLift K L A d 1 :=
  ⟨BoundedRingHom.id d.algebra, fun b => (movedBase_one K L A d b).symm, fun _ => le_rfl⟩

private theorem HasRationalLift.mul {σ τ : Γ} (hσ : HasRationalLift K L A d σ)
    (hτ : HasRationalLift K L A d τ) : HasRationalLift K L A d (σ * τ) := by
  obtain ⟨φ, hφ, hφnorm⟩ := hσ
  obtain ⟨ψ, hψ, hψnorm⟩ := hτ
  refine ⟨φ.comp ψ, fun b => ?_, fun t => (hφnorm (ψ t)).trans (hψnorm t)⟩
  change φ (ψ (d.baseMap b)) = d.baseMap (coefficientHom K L A (σ * τ) b)
  rw [hψ]
  change φ (d.baseMap (coefficientHom K L A τ b)) = _
  rw [hφ, coefficientHom_mul, BoundedAlgHom.comp_apply]
  rfl

private theorem hasRationalLift_of_fraction_bounds (σ : Γ)
    (hu : IsUnit (movedBase K L A d σ d.denominatorClass))
    (hbound : ∀ j, ‖movedFraction K L A d σ j‖ ≤ d.radii j) :
    HasRationalLift K L A d σ := by
  have hmul (j : Fin d.arity) :
      movedBase K L A d σ d.denominatorClass * movedFraction K L A d σ j =
        movedBase K L A d σ (d.numeratorClass j) := by
    rw [movedFraction, ← mul_assoc, Ring.mul_inverse_cancel _ hu, one_mul]
  exact ⟨d.ringEvaluate d.algebra (movedBase K L A d σ) (norm_movedBase_le K L A d σ)
      (movedFraction K L A d σ) hbound hmul,
    d.ringEvaluate_baseMap _ _ _ _ _ _, d.norm_ringEvaluate_le _ _ _ _ _ _⟩

/-- Coefficient automorphisms admitting contractive lifts to the same weighted
rational quotient in both directions. -/
def rationalSectionIsometrySubgroup : Subgroup Γ where
  carrier := {σ | HasRationalLift K L A d σ ∧ HasRationalLift K L A d σ⁻¹}
  one_mem' := ⟨hasRationalLift_one K L A d, by rw [inv_one]; exact hasRationalLift_one K L A d⟩
  mul_mem' := fun hσ hτ => ⟨HasRationalLift.mul K L A d hσ.1 hτ.1,
    by rw [mul_inv_rev]; exact HasRationalLift.mul K L A d hτ.2 hσ.2⟩
  inv_mem' := fun hσ => ⟨hσ.2, by rw [inv_inv]; exact hσ.1⟩

variable {G : Type w} [Group G] [TopologicalSpace G]
variable (ρ : G →* ↥(isometricAutomorphisms K L))
variable (hρ : ∀ c : L, Continuous (fun g : G => ((ρ g).val c : L)))

include ρ hρ in
private theorem continuous_movedBase (b : B) :
    Continuous (fun g : G => movedBase K L A d (ρ g) b) := by
  exact d.baseMap.continuous.comp (continuous_coefficientOrbit K L A ρ hρ b)

omit [CompleteSpace L] in
private theorem isUnit_baseDenominator : IsUnit (d.baseMap d.denominatorClass) :=
  RationalPresentation.isUnit_baseMap_denominator L B d.radii d.denominator d.numerators d.generates

include ρ hρ in
private theorem continuousAt_movedFraction_one (j : Fin d.arity) :
    ContinuousAt (fun g : G => movedFraction K L A d (ρ g) j) 1 := by
  have hu : IsUnit (movedBase K L A d (ρ 1) d.denominatorClass) := by
    rw [map_one, movedBase_one]
    exact isUnit_baseDenominator K L A d
  obtain ⟨v, hv⟩ := hu
  have hc : ContinuousAt Ring.inverse (movedBase K L A d (ρ 1) d.denominatorClass) :=
    hv ▸ NormedRing.inverse_continuousAt v
  exact (hc.comp (f := fun g : G => movedBase K L A d (ρ g) d.denominatorClass)
    (continuous_movedBase K L A d ρ hρ d.denominatorClass).continuousAt).mul
    (continuous_movedBase K L A d ρ hρ (d.numeratorClass j)).continuousAt

include ρ hρ in
private theorem eventually_hasRationalLift :
    ∀ᶠ g in 𝓝 (1 : G), HasRationalLift K L A d (ρ g) := by
  have hu : ∀ᶠ g in 𝓝 (1 : G), IsUnit (movedBase K L A d (ρ g) d.denominatorClass) := by
    apply (continuous_movedBase K L A d ρ hρ d.denominatorClass).continuousAt.eventually
    apply Units.isOpen.mem_nhds
    change IsUnit (movedBase K L A d (ρ 1) d.denominatorClass)
    rw [map_one, movedBase_one]
    exact isUnit_baseDenominator K L A d
  have hf (j : Fin d.arity) : ∀ᶠ g in 𝓝 (1 : G),
      ‖movedFraction K L A d (ρ g) j‖ ≤ d.radii j := by
    have hsmall : ∀ᶠ g in 𝓝 (1 : G),
        ‖movedFraction K L A d (ρ g) j - d.fractionCoordinate j‖ < d.radii j := by
      have hc : ContinuousAt (fun g : G =>
          ‖movedFraction K L A d (ρ g) j - d.fractionCoordinate j‖) 1 :=
        ((continuousAt_movedFraction_one K L A d ρ hρ j).sub
        continuousAt_const).norm
      have hzero : ‖movedFraction K L A d (ρ 1) j - d.fractionCoordinate j‖ <
          d.radii j := by
        rw [map_one, movedFraction_one, sub_self, norm_zero]
        exact d.radii.positive j
      exact hc.eventually (gt_mem_nhds hzero)
    filter_upwards [hsmall] with g hg
    simpa only [sub_add_cancel] using (IsUltrametricDist.norm_add_le_max
        (movedFraction K L A d (ρ g) j - d.fractionCoordinate j)
        (d.fractionCoordinate j)).trans (max_le hg.le
          (RationalPresentation.norm_fraction_le L B d.radii d.denominator d.numerators j))
  filter_upwards [hu, Filter.eventually_all.mpr hf] with g hg hf
  exact hasRationalLift_of_fraction_bounds K L A d (ρ g) hg hf

section Openness

variable [IsTopologicalGroup G]

include ρ hρ in
private theorem isOpen_rationalSectionIsometrySubgroup :
    IsOpen ((rationalSectionIsometrySubgroup K L A d).comap ρ : Set G) := by
  apply Subgroup.isOpen_of_mem_nhds
  have hi : Tendsto (fun g : G => g⁻¹) (𝓝 (1 : G)) (𝓝 (1 : G)) := by
    simpa only [inv_one] using (continuous_inv.continuousAt (x := (1 : G))).tendsto
  have h := eventually_hasRationalLift K L A d ρ hρ
  filter_upwards [h, hi.eventually h] with g hg hg'
  exact ⟨hg, map_inv ρ g ▸ hg'⟩

/-- An open subgroup on which the actual rational section algebra carries
isometric semilinear operators. -/
def rationalSectionOpenSubgroup : OpenSubgroup G :=
  ⟨(rationalSectionIsometrySubgroup K L A d).comap ρ,
    isOpen_rationalSectionIsometrySubgroup K L A d ρ hρ⟩

end Openness

variable (H : Subgroup (CoefficientGroup K L))
  (hH : H ≤ rationalSectionIsometrySubgroup K L A d)

/-- The unique bounded section operator restricting the given coefficient
automorphism to this actual weighted rational quotient. -/
def rationalSectionMap (σ : H) : BoundedRingHom d.algebra d.algebra :=
  ((hH σ.property).1 : HasRationalLift K L A d σ).choose

include hH in
@[simp] theorem rationalSectionMap_baseMap (σ : H) (b : B) :
    rationalSectionMap K L A d H hH σ (d.baseMap b) =
      d.baseMap (coefficientHom K L A σ b) :=
  ((hH σ.property).1 : HasRationalLift K L A d σ).choose_spec.1 b

theorem norm_rationalSectionMap_le (σ : H) (a : d.algebra) :
    ‖rationalSectionMap K L A d H hH σ a‖ ≤ ‖a‖ :=
  ((hH σ.property).1 : HasRationalLift K L A d σ).choose_spec.2 a

@[simp] theorem rationalSectionMap_one :
    rationalSectionMap K L A d H hH 1 = BoundedRingHom.id d.algebra := by
  apply d.ringHom_ext_over_base d.algebra (movedBase K L A d 1) (norm_movedBase_le K L A d 1)
  · exact rationalSectionMap_baseMap K L A d H hH 1
  · intro b
    exact (movedBase_one K L A d b).symm

theorem rationalSectionMap_mul (σ τ : H) :
    rationalSectionMap K L A d H hH (σ * τ) =
      (rationalSectionMap K L A d H hH σ).comp (rationalSectionMap K L A d H hH τ) := by
  apply d.ringHom_ext_over_base d.algebra (movedBase K L A d (σ.val * τ.val))
    (norm_movedBase_le K L A d (σ.val * τ.val))
  · exact rationalSectionMap_baseMap K L A d H hH (σ * τ)
  · intro b
    change rationalSectionMap K L A d H hH σ (rationalSectionMap K L A d H hH τ
      (d.baseMap b)) = d.baseMap (coefficientHom K L A (σ.val * τ.val) b)
    rw [rationalSectionMap_baseMap, rationalSectionMap_baseMap, coefficientHom_mul,
      BoundedAlgHom.comp_apply]

theorem norm_rationalSectionMap (σ : H) (a : d.algebra) :
    ‖rationalSectionMap K L A d H hH σ a‖ = ‖a‖ := by
  refine le_antisymm (norm_rationalSectionMap_le K L A d H hH σ a) ?_
  have h := norm_rationalSectionMap_le K L A d H hH σ⁻¹
    (rationalSectionMap K L A d H hH σ a)
  change ‖((rationalSectionMap K L A d H hH σ⁻¹).comp
    (rationalSectionMap K L A d H hH σ)) a‖ ≤ _ at h
  rwa [← rationalSectionMap_mul, inv_mul_cancel, rationalSectionMap_one] at h

/-- On the scalars of the rational quotient the operator is the original
coefficient automorphism. -/
theorem rationalSectionMap_scalar (σ : H) (c : L) :
    rationalSectionMap K L A d H hH σ (algebraMap L d.algebra c) =
      algebraMap L d.algebra (σ.val.val c) := by
  rw [← d.baseMap.toAlgHom.commutes c, rationalSectionMap_baseMap]
  change d.baseMap (coefficientHom K L A σ (scalarMap K L A c)) = _
  rw [coefficientHom_scalar, scalarMap_apply]
  exact d.baseMap.toAlgHom.commutes _

/-- Actual rational restrictions commute with section operators on their
common isometry subgroup. -/
theorem rationalSectionMap_restriction {e : RationalChart L B}
    (f : d.toDomain.Inclusion e.toDomain)
    (he : H ≤ rationalSectionIsometrySubgroup K L A e) (σ : H) :
    f.restriction.toBoundedRingHom.comp (rationalSectionMap K L A e H he σ) =
      (rationalSectionMap K L A d H hH σ).comp f.restriction.toBoundedRingHom := by
  have hbase (b : B) : f.restriction (e.baseMap b) = d.baseMap b :=
    congrArg (fun φ : BoundedAlgHom L B d.algebra => φ b) f.comp_baseMap
  apply e.ringHom_ext_over_base d.algebra
    (movedBase K L A d σ) (norm_movedBase_le K L A d σ)
  · intro b
    change f.restriction (rationalSectionMap K L A e H he σ (e.baseMap b)) = _
    rw [rationalSectionMap_baseMap, hbase]
    rfl
  · intro b
    change rationalSectionMap K L A d H hH σ (f.restriction (e.baseMap b)) = _
    rw [hbase, rationalSectionMap_baseMap]
    rfl

private theorem rationalSectionMap_fraction (σ : H) (j : Fin d.arity) :
    rationalSectionMap K L A d H hH σ (d.fractionCoordinate j) =
      movedFraction K L A d σ j := by
  let φ := rationalSectionMap K L A d H hH σ
  have hu : IsUnit (φ (d.baseMap d.denominatorClass)) :=
    (isUnit_baseDenominator K L A d).map φ.toRingHom
  have he := φ.toRingHom.congr_arg (d.baseMap_denominator_mul_fractionCoordinate j)
  rw [map_mul] at he
  change φ (d.fractionCoordinate j) =
    Ring.inverse (d.baseMap (coefficientHom K L A σ d.denominatorClass)) *
      d.baseMap (coefficientHom K L A σ (d.numeratorClass j))
  rw [← rationalSectionMap_baseMap K L A d H hH σ d.denominatorClass,
    ← rationalSectionMap_baseMap K L A d H hH σ (d.numeratorClass j), ← he]
  exact (Ring.inverse_mul_cancel_left _ _ hu).symm

variable (hLift : ∀ g : G, ρ g ∈ H)

local notation "operator" => fun g : G =>
  rationalSectionMap K L A d H hH (Subtype.mk (ρ g) (hLift g))

include hρ in
private theorem continuous_operator_baseMap (b : B) :
    Continuous (fun g : G => operator g (d.baseMap b)) := by
  simp only [rationalSectionMap_baseMap]
  exact continuous_movedBase K L A d ρ hρ b

include hρ in
private theorem continuous_operator_fraction (j : Fin d.arity) :
    Continuous (fun g : G => operator g (d.fractionCoordinate j)) := by
  apply continuous_iff_continuousAt.mpr
  intro g
  simp only [rationalSectionMap_fraction, movedFraction]
  have hu : IsUnit (movedBase K L A d (ρ g) d.denominatorClass) := by
    change IsUnit (d.baseMap (coefficientHom K L A (ρ g) d.denominatorClass))
    rw [← rationalSectionMap_baseMap K L A d H hH ⟨ρ g, hLift g⟩ d.denominatorClass]
    exact (isUnit_baseDenominator K L A d).map (operator g).toRingHom
  obtain ⟨v, hv⟩ := hu
  have hc : ContinuousAt Ring.inverse (movedBase K L A d (ρ g) d.denominatorClass) :=
    hv ▸ NormedRing.inverse_continuousAt v
  exact (hc.comp (f := fun g : G => movedBase K L A d (ρ g) d.denominatorClass)
    (continuous_movedBase K L A d ρ hρ d.denominatorClass).continuousAt).mul
    (continuous_movedBase K L A d ρ hρ (d.numeratorClass j)).continuousAt

include hρ in
private theorem continuous_operator_coordinate (i : Fin d.algebra.arity) :
    Continuous (fun g : G => operator g (coordinate L d.algebra i)) := by
  change Fin ((B).arity + d.arity) at i
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have he : d.baseMap (coordinate L B j) =
        coordinate L d.algebra (Fin.castAdd d.arity j) :=
      RationalPresentation.baseMap_coordinate L B d.radii d.denominator d.numerators j
    exact (continuous_operator_baseMap K L A d ρ hρ H hH hLift (coordinate L B j)).congr
      (fun g => congrArg (operator g) he)
  · exact continuous_operator_fraction K L A d ρ hρ H hH hLift j

private abbrev polynomialEvaluation :
    MvPolynomial (Fin d.algebra.arity) L →ₐ[L] d.algebra :=
  (presentationMap L d.algebra).toAlgHom.comp (polynomialMap d.algebra.polyradius L)

omit [CompleteSpace L] in
@[simp]
private theorem polynomialEvaluation_C (c : L) :
    polynomialEvaluation K L A d (MvPolynomial.C c) = algebraMap L d.algebra c :=
  (polynomialEvaluation K L A d).commutes c

omit [CompleteSpace L] in
@[simp]
private theorem polynomialEvaluation_X (i : Fin d.algebra.arity) :
    polynomialEvaluation K L A d (MvPolynomial.X i) = coordinate L d.algebra i := by
  change presentationMap L d.algebra
    (MvPolynomial.aeval (fun j => monomial d.algebra.polyradius L (Finsupp.single j 1) 1)
      (MvPolynomial.X i)) = _
  rw [MvPolynomial.aeval_X]
  rfl

include hρ in
private theorem continuous_operator_polynomial (p : MvPolynomial (Fin d.algebra.arity) L) :
    Continuous (fun g : G => operator g (polynomialEvaluation K L A d p)) := by
  induction p using MvPolynomial.induction_on with
  | C c =>
    simp only [polynomialEvaluation_C]
    simp_rw [← d.baseMap.toAlgHom.commutes]
    exact continuous_operator_baseMap K L A d ρ hρ H hH hLift (algebraMap L B c)
  | add p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  | mul_X p i hp =>
    simp only [map_mul, polynomialEvaluation_X]
    exact hp.mul (continuous_operator_coordinate K L A d ρ hρ H hH hLift i)

include hρ in
/-- Norm-continuous coefficient orbits give continuous orbits on every
section under the actual norm-isometric rational operators. -/
theorem continuous_rationalSectionMap (b : d.algebra) :
    Continuous (fun g : G => operator g b) := by
  have hd : DenseRange (polynomialEvaluation K L A d) :=
    (presentationMap_surjective L d.algebra).denseRange.comp
      (denseRange_polynomialMap d.algebra.polyradius L) (presentationMap L d.algebra).continuous
  apply continuous_iff_continuousAt.mpr
  intro g
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  have hthird : 0 < ε / 3 := by positivity
  obtain ⟨p, hp⟩ := hd.exists_dist_lt b hthird
  let q := polynomialEvaluation K L A d p
  change dist b q < ε / 3 at hp
  have hq : Continuous (fun h : G => operator h q) :=
    continuous_operator_polynomial K L A d ρ hρ H hH hLift p
  have hiso (h : G) : Isometry (operator h) := by
    apply Isometry.of_dist_eq
    intro a b
    rw [dist_eq_norm, dist_eq_norm, ← map_sub (operator h).toRingHom]
    exact norm_rationalSectionMap K L A d H hH ⟨ρ h, hLift h⟩ (a - b)
  filter_upwards [Metric.continuousAt_iff'.mp hq.continuousAt (ε / 3) hthird] with h hh
  exact (dist_triangle4 _ (operator h q) (operator g q) _).trans_lt (by
    change dist (operator h q) (operator g q) < ε / 3 at hh
    rw [(hiso h).dist_eq, (hiso g).dist_eq, dist_comm q b]
    linarith only [hp, hh])

section OpenSubgroup

variable [IsTopologicalGroup G]

/-- The actual semilinear rational section operator on the derived open subgroup. -/
def openRationalSectionMap (g : rationalSectionOpenSubgroup K L A d ρ hρ) :
    BoundedRingHom d.algebra d.algebra :=
  rationalSectionMap K L A d _ le_rfl ⟨ρ g.val, g.property⟩

/-- Orbits of every rational section on the derived open subgroup are norm continuous. -/
theorem continuous_openRationalSectionMap (b : d.algebra) :
    Continuous (fun g : rationalSectionOpenSubgroup K L A d ρ hρ =>
      openRationalSectionMap K L A d ρ hρ g b) := by
  let U := rationalSectionOpenSubgroup K L A d ρ hρ
  let ρ' := ρ.comp U.toSubgroup.subtype
  exact continuous_rationalSectionMap K L A d ρ'
    (fun c => (hρ c).comp continuous_subtype_val) _ le_rfl (fun g => g.property) b

end OpenSubgroup

end Langlands.Analytic.PresentedAffinoidAlgebra.GroundFieldExtension

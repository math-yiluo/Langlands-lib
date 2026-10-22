import Langlands.Geometry.Analytic.GeneralizedAffinoid.Definitions
import Langlands.Geometry.Analytic.BoundedEquivalence.Definitions

/-! # Radius-one comparison of actual quotient presentations -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- Regard a strict presentation as a positive-polyradius presentation by
pulling back its actual closed ideal through the radius-one isometry. -/
def ofStrict (P : PresentedStrictAffinoidAlgebra K) : PresentedAffinoidAlgebra K where
  arity := P.arity
  polyradius := PositivePolyradius.unit (Fin P.arity)
  ideal := P.ideal.comap (GeneralizedTateAlgebra.unitAlgEquiv K).toRingEquiv.toRingHom
  ideal_closed := P.ideal_closed.preimage
    (GeneralizedTateAlgebra.isometry_unitAlgEquiv K).continuous

/-- The quotient equivalence induced by keeping all formal coefficients. -/
def strictAlgEquiv (P : PresentedStrictAffinoidAlgebra K) : ofStrict K P ≃ₐ[K] P :=
  Ideal.quotientEquivAlg (ofStrict K P).ideal P.ideal
    (GeneralizedTateAlgebra.unitAlgEquiv K) (by
      exact (Ideal.map_comap_of_equiv
        (GeneralizedTateAlgebra.unitAlgEquiv K).toRingEquiv).symm)

@[simp] theorem strictAlgEquiv_presentationMap (P : PresentedStrictAffinoidAlgebra K)
    (f : GeneralizedTateAlgebra (PositivePolyradius.unit (Fin P.arity)) K) :
    strictAlgEquiv K P (presentationMap K (ofStrict K P) f) =
      PresentedStrictAffinoidAlgebra.presentationMap K P
        (GeneralizedTateAlgebra.unitAlgEquiv K f) := rfl

@[simp] theorem strictAlgEquiv_symm_presentationMap (P : PresentedStrictAffinoidAlgebra K)
    (f : StrictTateAlgebra (Fin P.arity) K) :
    (strictAlgEquiv K P).symm
        (PresentedStrictAffinoidAlgebra.presentationMap K P f) =
      presentationMap K (ofStrict K P) (GeneralizedTateAlgebra.unitAlgEquiv K |>.symm f) :=
  rfl

theorem norm_strictAlgEquiv_le (P : PresentedStrictAffinoidAlgebra K) (x : ofStrict K P) :
    ‖strictAlgEquiv K P x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ := exists_representative_norm_lt K (ofStrict K P) x hε
  rw [strictAlgEquiv_presentationMap]
  calc
    _ ≤ ‖GeneralizedTateAlgebra.unitAlgEquiv K a‖ := Ideal.Quotient.norm_mk_le P.ideal _
    _ = ‖a‖ := GeneralizedTateAlgebra.norm_unitAlgEquiv K a
    _ ≤ ‖presentationMap K (ofStrict K P) a‖ + ε := ha.le

theorem norm_strictAlgEquiv_symm_le (P : PresentedStrictAffinoidAlgebra K) (x : P) :
    ‖(strictAlgEquiv K P).symm x‖ ≤ ‖x‖ := by
  apply le_of_forall_pos_le_add
  intro ε hε
  obtain ⟨a, rfl, ha⟩ :=
    PresentedStrictAffinoidAlgebra.exists_representative_norm_lt K P x hε
  rw [strictAlgEquiv_symm_presentationMap]
  calc
    _ ≤ ‖(GeneralizedTateAlgebra.unitAlgEquiv K).symm a‖ :=
      norm_presentationMap_le K (ofStrict K P) _
    _ = ‖a‖ := by
      simpa only [AlgEquiv.apply_symm_apply] using
        (GeneralizedTateAlgebra.norm_unitAlgEquiv K
          ((GeneralizedTateAlgebra.unitAlgEquiv K).symm a)).symm
    _ ≤ ‖PresentedStrictAffinoidAlgebra.presentationMap K P a‖ + ε := ha.le

/-- The comparison preserves the actual quotient norm, not just its topology. -/
theorem norm_strictAlgEquiv (P : PresentedStrictAffinoidAlgebra K) (x : ofStrict K P) :
    ‖strictAlgEquiv K P x‖ = ‖x‖ := by
  apply le_antisymm (norm_strictAlgEquiv_le K P x)
  simpa only [AlgEquiv.symm_apply_apply] using
    norm_strictAlgEquiv_symm_le K P (strictAlgEquiv K P x)

/-- The explicit comparison is bounded in both directions, with bound one. -/
def strictEquiv (P : PresentedStrictAffinoidAlgebra K) : BoundedAlgEquiv K (ofStrict K P) P where
  toAlgEquiv := strictAlgEquiv K P
  bounded := ⟨1, zero_lt_one, fun x => by
    simpa only [one_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom] using norm_strictAlgEquiv_le K P x⟩
  inverse_bounded := ⟨1, zero_lt_one, fun x => by
    simpa only [one_mul, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
      AlgEquiv.coe_toAlgHom] using norm_strictAlgEquiv_symm_le K P x⟩

theorem isometry_strictEquiv (P : PresentedStrictAffinoidAlgebra K) :
    Isometry (strictEquiv K P) :=
  AddMonoidHomClass.isometry_of_norm (strictAlgEquiv K P) (norm_strictAlgEquiv K P)

/-- The actual multiplicative spectra agree by pullback along the comparison. -/
def strictSpectrumHomeomorph (P : PresentedStrictAffinoidAlgebra K) :
    BanachSpectrum P ≃ₜ BanachSpectrum (ofStrict K P) :=
  (strictEquiv K P).spectrumHomeomorph

end Langlands.Analytic.PresentedAffinoidAlgebra

import Langlands.Geometry.Analytic.RationalLocalization
import Langlands.Geometry.Analytic.RationalIdentity.Statement

/-! # Rational quotients with an already bounded fraction tuple -/

noncomputable section

universe u

namespace Langlands.Analytic.RationalIdentity

open StrictTateAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (P : PresentedStrictAffinoidAlgebra K) (m : ℕ) (g : Pˣ) (f : Fin m → P)

omit [CompleteSpace K] in
/-- An actual unit denominator generates the unit ideal, without any
spectrum nonvanishing-to-invertibility principle. -/
theorem generatesUnitIdeal :
    RationalLocalization.GeneratesUnitIdeal K P m (g : P) f := by
  apply (Ideal.eq_top_iff_one _).mpr
  have h : (g : P) ∈ Ideal.span (insert (g : P) (Set.range f)) :=
    Ideal.subset_span (Set.mem_insert _ _)
  have h' := Ideal.mul_mem_left (Ideal.span (insert (g : P) (Set.range f)))
    (↑g⁻¹ : P) h
  simpa only [Units.inv_mul] using h'

omit [CompleteSpace K] in
theorem fraction_equation (i : Fin m) :
    (g : P) * fractions K P m g f i = f i := by
  simp [fractions, ← mul_assoc]

variable (hb : HasBoundedMonomials (Fin m) P (fractions K P m g f))

/-- Evaluation at the original fractions constructs a bounded retraction. -/
def retraction :
    BoundedAlgHom K (RationalLocalization.algebra K P m (g : P) f) P :=
  RationalLocalization.liftFromBase K P m (g : P) f P
    (BoundedAlgHom.id K P) (fractions K P m g f) hb
    (fraction_equation K P m g f)

theorem retraction_comp_baseMap :
    (retraction K P m g f hb).comp
      (RationalLocalization.baseMap K P m (g : P) f) = BoundedAlgHom.id K P :=
  RationalLocalization.liftFromBase_comp_baseMap K P m (g : P) f P
    (BoundedAlgHom.id K P) (fractions K P m g f) hb
    (fraction_equation K P m g f)

/-- Uniqueness over the base proves that the reverse composite is also
the identity on the actual quotient. -/
theorem baseMap_comp_retraction :
    (RationalLocalization.baseMap K P m (g : P) f).comp
      (retraction K P m g f hb) =
        BoundedAlgHom.id K (RationalLocalization.algebra K P m (g : P) f) := by
  apply RationalLocalization.hom_ext_base K P m (g : P) f
    (RationalLocalization.algebra K P m (g : P) f) (generatesUnitIdeal K P m g f)
  rw [BoundedAlgHom.comp_assoc, retraction_comp_baseMap,
    BoundedAlgHom.comp_id, BoundedAlgHom.id_comp]

/-- The rational quotient is boundedly equivalent to the original algebra
when its actual fractions already have bounded monomials there. -/
def equiv :
    BoundedAlgEquiv K P (RationalLocalization.algebra K P m (g : P) f) :=
  BoundedAlgEquiv.ofHomInv
    (RationalLocalization.baseMap K P m (g : P) f) (retraction K P m g f hb)
    (fun a => congrArg (fun φ => φ a) (retraction_comp_baseMap K P m g f hb))
    (fun a => congrArg (fun φ => φ a) (baseMap_comp_retraction K P m g f hb))

@[simp]
theorem equiv_apply (a : P) :
    equiv K P m g f hb a = RationalLocalization.baseMap K P m (g : P) f a := rfl

/-- The equivalence is over the original affinoid algebra on spectra. -/
theorem spectrumHomeomorph_apply
    (x : BanachSpectrum (RationalLocalization.algebra K P m (g : P) f)) :
    (equiv K P m g f hb).spectrumHomeomorph x =
      BanachSpectrum.comap (RationalLocalization.baseMap K P m (g : P) f).toBoundedRingHom x :=
  rfl

include hb in
theorem locus_eq_univ :
    RationalLocalization.locus K P m (g : P) f = Set.univ := by
  rw [← RationalLocalization.range_comap_baseMap K P m (g : P) f
    (generatesUnitIdeal K P m g f)]
  exact Set.range_eq_univ.mpr (equiv K P m g f hb).spectrumHomeomorph.surjective

omit [CompleteSpace K] in
/-- Unit-ball tuples have bounded powers even when the original quotient is
the zero ring and has no `NormOneClass` instance. -/
theorem bounded_of_norm_le_one (h : ∀ i, ‖f i‖ ≤ 1) :
    HasBoundedMonomials (Fin m) P f := by
  apply (hasBoundedMonomials_iff_pow_bound (Fin m) P f).mpr
  intro i
  refine ⟨max 1 ‖(1 : P)‖, lt_of_lt_of_le zero_lt_one (le_max_left _ _), ?_⟩
  intro n
  induction n with
  | zero => simpa only [pow_zero] using le_max_right (1 : ℝ) ‖(1 : P)‖
  | succ n ih =>
    rw [pow_succ]
    calc
      ‖f i ^ n * f i‖ ≤ ‖f i ^ n‖ * ‖f i‖ := norm_mul_le _ _
      _ ≤ max 1 ‖(1 : P)‖ * 1 :=
        mul_le_mul ih (h i) (norm_nonneg _)
          (zero_le_one.trans (le_max_left _ _))
      _ = max 1 ‖(1 : P)‖ := mul_one _

/-- Adding equations `Y_i = f_i` for actual unit-ball elements does not
change the bounded algebra. -/
def unitRadiusEquiv (h : ∀ i, ‖f i‖ ≤ 1) :
    BoundedAlgEquiv K P (RationalLocalization.algebra K P m 1 f) :=
  equiv K P m 1 f (by
    have hf : fractions K P m (1 : Pˣ) f = f := by
      funext i
      simp [fractions]
    rw [hf]
    exact bounded_of_norm_le_one K P m f h)

/-- The empty rational presentation with denominator one gives an
unconditional identity chart, including for the zero algebra. -/
def emptyEquiv :
    BoundedAlgEquiv K P
      (RationalLocalization.algebra K P 0 1 (fun i => Fin.elim0 i)) :=
  unitRadiusEquiv K P 0 (fun i => Fin.elim0 i) (fun i => Fin.elim0 i)

/-- The constructed equivalences and spectrum identification prove the
identity-chart target. -/
theorem identity : IdentityStatement.{u} := by
  intro K _ _ _ P
  refine ⟨?_, ?_, ?_⟩
  · intro m g f hb
    exact ⟨equiv K P m g f hb, equiv_apply K P m g f hb,
      spectrumHomeomorph_apply K P m g f hb, locus_eq_univ K P m g f hb⟩
  · intro m f h
    exact ⟨unitRadiusEquiv K P m f h, fun _ => rfl⟩
  · exact ⟨emptyEquiv K P, fun _ => rfl⟩

end Langlands.Analytic.RationalIdentity

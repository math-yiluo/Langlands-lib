import Langlands.Representation.Geometric.LeadingOppositeFiltration
import Langlands.Representation.Exponents.FilteredCentralRetraction
import Langlands.Representation.Parabolic.IrreducibleOppositeJacquetUnitProof
import Langlands.Representation.Classification.RelativeCosocleAdmissibilityProof
import Langlands.Representation.Filtration.CentralEigenspaceSplitting

/-! Whole-induction isolation from actual geometry and finite generation. -/

noncomputable section

namespace Langlands.WholeInductionGeometricIsolation

open GeneralLinear Geometric RelativeRegularComparison
open CuspidalJacquetMultiplicity FilteredCentralRetraction
open scoped BigOperators

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  (T : F.TopologicalData) {n : ℕ} (B : BlockShape n)

set_option maxHeartbeats 4000000 in
/-- The upper geometric lemma, actual leading-piece exclusion and finite
generation of the actual whole induction construct its actual leading-block
retraction under the stated geometric and finite-generation hypotheses. -/
theorem wholeRetractionOfGeometricInputs
    (hexclusion : GLRelativeGeometricLeadingCharacterExclusionStatement.{uF, uV})
    (hupper : GeometricLemmaTheorem.{uF, uV} T B B.reverse) (hn : 0 < n)
    (π : Rep.{uV} ℂ (B.Levi F.Carrier)) (hπ : Representation.IsIrreducible π.ρ)
    (htemp : IsLeviTempered T B π) (t : Fin B.length → ℝ) (ht : StrictAnti t)
    (hfg : Module.Finite (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      (induced T B (Rep.of (T.leviRealPowerTwist B t π.ρ))).ρ.asModule) :
    letI := T.topology
    let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
    let E := oppositeJacquet T B (induced T B πt)
    ∃ (i : πt.ρ.IntertwiningMap E.ρ) (r : E.ρ.IntertwiningMap πt.ρ),
      (∀ w, r (i w) = w) ∧
      ∀ (χ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ),
        T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
          (fun k => (B.size k : ℝ) * t k) →
        ∀ v : E, v ∈ generalizedCentralCharacterSpace E.ρ χ → i (r v) = v := by
  classical
  let := T.topology
  let := T.leviTopologicalGroup B
  let Z := B.Levi F.Carrier ⧸ Subgroup.center (B.Levi F.Carrier)
  let := borel Z
  have : BorelSpace Z := ⟨rfl⟩
  obtain ⟨μ, hμ⟩ := T.exists_isHaarMeasure_leviCentralQuotient B
  have hπadm := htemp.isAdmissible
  obtain ⟨c, -⟩ := (htemp μ).2
  let A := SmoothRep.of π.ρ hπadm.1
  let At := SmoothRep.of (T.leviRealPowerTwist B t A.representation)
    ((T.isSmooth_leviRealPowerTwist_iff B t A.representation).mpr A.isSmooth)
  let πt := Rep.of (T.leviRealPowerTwist B t π.ρ)
  let X := induced T B πt
  let E := oppositeJacquet T B X
  let D := leadingOppositeFiltrationOfUpper T B hupper At
  let j₀ := D.identityIndex T B
  let egrade := D.identityGradeEquiv T B
  let χ₀ : Subgroup.center (B.Levi F.Carrier) →* ℂˣ :=
    c.character * (T.leviRealPowerCharacter B t).comp
      (Subgroup.center (B.Levi F.Carrier)).subtype
  have hscalar : ∀ (z : Subgroup.center (B.Levi F.Carrier)) (w : πt),
      πt.ρ (z : B.Levi F.Carrier) w = (χ₀ z : ℂ) • w := by
    intro z w
    change (T.leviRealPowerCharacter B t z : ℂ) • π.ρ z w = (χ₀ z : ℂ) • w
    rw [c.acts z w]
    simp only [χ₀, MonoidHom.mul_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
      Units.val_mul, smul_smul]
    rw [mul_comm]
  have hreal : T.IsRealPartOf (χ₀.comp (B.blockScalarToCenter F.Carrier))
      (fun k => (B.size k : ℝ) * t k) := by
    intro a
    change ‖(c.character (B.blockScalarToCenter F.Carrier a) : ℂ) *
      (T.leviRealPowerCharacter B t (B.blockScalarLevi F.Carrier a) : ℂ)‖ = _
    rw [norm_mul, c.norm_eq_one, one_mul, T.coe_leviRealPowerCharacter_blockScalar B,
      Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Finset.prod_nonneg fun k _ =>
        Real.rpow_nonneg (T.normalizedAbs_nonneg _) _)]
  have hπti : Representation.IsIrreducible πt.ρ :=
    (T.isIrreducible_leviRealPowerTwist_iff B t π.ρ).mpr hπ
  have hπta : IsAdmissible πt.ρ :=
    (T.isAdmissible_leviRealPowerTwist_iff B t π.ρ).mpr hπadm
  have hXa : IsAdmissible X.ρ :=
    Parabolic.normalizedInductionAdmissibility F T B πt πt.ρ hπta
  have hfin := (oppositeJacquetCentralAction
    T B X hXa hfg).1
  obtain ⟨i, hi⟩ := Parabolic.irreducibleOppositeJacquetUnit.1 p F T n hn B πt hπti hπta
  have hi₀ : i ≠ 0 := by
    let := hπti
    let : Nontrivial πt := IsSimpleModule.nontrivial
      (MonoidAlgebra ℂ (B.Levi F.Carrier)) πt.ρ.asModule
    intro hzero
    obtain ⟨w, hw⟩ := exists_ne (0 : πt)
    apply hw
    apply hi
    rw [hzero]
    rfl
  let P : (Subgroup.center (B.Levi F.Carrier) →* ℂˣ) → Prop :=
    fun χ => T.IsRealPartOf (χ.comp (B.blockScalarToCenter F.Carrier))
      (fun k => (B.size k : ℝ) * t k)
  have hother : ∀ χ, P χ → ∀ j : Fin D.length, j ≠ j₀ →
      ¬ IsGeneralizedEigencharacter
        ((D.filtration.gradedRepresentation j).ρ.comp
          (Subgroup.center (B.Levi F.Carrier)).subtype) χ := by
    intro χ hχ j hj hocc
    exact hj (D.leadingGrade_eq_identity T B hexclusion μ A (htemp μ) t ht j χ hχ hocc)
  have hgrade : Representation.IsIrreducible (D.filtration.gradedRepresentation j₀).ρ :=
    (CentralEigenspaceSplitting.isIrreducible_iff_of_equiv egrade).mpr hπti
  have hgradescalar : ∀ (z : Subgroup.center (B.Levi F.Carrier))
      (v : D.filtration.gradedRepresentation j₀),
      (D.filtration.gradedRepresentation j₀).ρ z v = (χ₀ z : ℂ) • v := by
    intro z v
    apply egrade.injective
    rw [map_smul]
    exact (LinearMap.congr_fun (egrade.isIntertwining' z) v).trans (hscalar z (egrade v))
  obtain ⟨r, hri, hir⟩ := retractionOfIsolatedGrade hfin D.filtration χ₀ j₀ P
    hreal hother hgrade hgradescalar hscalar i hi hi₀
  exact ⟨i, r, hri, hir⟩

end Langlands.WholeInductionGeometricIsolation

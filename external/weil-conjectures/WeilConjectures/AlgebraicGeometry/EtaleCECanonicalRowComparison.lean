/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.EtaleCETotalSections
public import WeilConjectures.CategoryTheory.SecondFiltrationRowCycleComparison
import WeilConjectures.CategoryTheory.SecondFiltrationRowGradedCycles

/-! # Canonical comparisons for the cycles of CE rows

Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison).
-/

@[expose] public section

universe uNatural
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Etale
namespace EtaleTermwiseHypercohomology

variable {X : Scheme.{uNatural}}
  {K : CochainComplex.Plus (Sheaf X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})}

/-- The row comparison normalized by diagonal inclusion and the homology projection.
The source theorem is proved. Its equations determine the step lift and cycle lift
by monicity, and the quotient comparison by epimorphic cancellation.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
noncomputable def rowComparison (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    filteredComplexPageObject D.sectionsTotal D.L 1 (q, (p : ℤ)) ≅
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).homology p :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose p q

/-- The unique lift of row cycles to the filtration step.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
noncomputable def rowCycleStep (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q)).cycles p ⟶
        (D.L.step q : CochainComplex AddCommGrpCat.{uNatural + 1} ℤ).X (q + (p : ℤ)) :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose_spec.choose p q

/-- The unique graded class of the lifted row cycle.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
noncomputable def rowCycleClass (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q)).cycles p ⟶
        (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}) :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose_spec.choose_spec.choose p q

/-- The diagonal normalization of the step lift.
Source: Stacks Project, Tag 0130.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
theorem rowCycleStep_arrow (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    D.rowCycleStep p q ≫ (D.L.step q).arrow.f (q + (p : ℤ)) =
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).iCycles p ≫
      Functor.secondFiltrationRowι
        (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}) D.I p q :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose_spec.choose_spec.choose_spec.1 p q

/-- The cycle normalization of the graded class.
Source: Stacks Project, Tag 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
theorem rowCycleClass_arrow (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    D.rowCycleClass p q ≫ (D.L.complexCycles q (q + (p : ℤ)) 1).arrow =
      D.rowCycleStep p q ≫ (D.L.complexQuotientπ q (q + 1) (by omega)).f (q + (p : ℤ)) :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose_spec.choose_spec.choose_spec.2.1 p q

/-- The quotient normalization of row homology.
Source: Stacks Project, Tag 0130.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
theorem rowCycleClass_comparison (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    D.rowCycleClass p q ≫ filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
        (D.rowComparison p q).hom =
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).homologyπ p :=
  (Functor.secondFiltration_row_cycle_comparison
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.below D.L D.filtration_formula).choose_spec.choose_spec.choose_spec.2.2 p q

/-- Row cycles and filtered first-page cycles are isomorphic, before taking homology.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
theorem rowCycleClass_isIso (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    IsIso (D.rowCycleClass p q) := by
  obtain ⟨c, hc⟩ := Functor.secondFiltration_row_graded_cycles
    (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1})
    D.I D.L D.filtration_formula p q (D.rowCycleStep p q) (D.rowCycleStep_arrow p q)
  have h : D.rowCycleClass p q = c.hom := by
    apply (cancel_mono (D.L.complexCycles q (q + (p : ℤ)) 1).arrow).1
    exact (D.rowCycleClass_arrow p q).trans hc.symm
  rw [h]
  infer_instance

/-- The inverse cycle comparison, used on individual filtered representatives.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
noncomputable def rowCyclesIso (D : EtaleTermwiseHypercohomology X K) (p : ℕ) (q : ℤ) :
    (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
      (ComplexShape.up ℕ)).obj (D.I.X q)).cycles p ≅
        (D.L.complexCycles q (q + (p : ℤ)) 1 : AddCommGrpCat.{uNatural + 1}) :=
  letI := D.rowCycleClass_isIso p q
  asIso (D.rowCycleClass p q)

/-- The signed first-page comparison, constructed from the normalized row comparison.
Source: Stacks Project, Tag 0130.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
noncomputable def signedRowComparison (D : EtaleTermwiseHypercohomology X K)
    (p : ℕ) (q : ℤ) :
    filteredComplexPageObject D.sectionsTotal D.L 1 (q, (p : ℤ)) ≅
      (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj (D.I.X q)).homology p :=
  ((p : ℤ) * q).negOnePow • D.rowComparison p q

/-- Computing a class through row cycles.
Source: Stacks Project, Tags 0130 and 012K.
(blueprint: def-weil-pbc-ce-canonical-row-comparison). -/
theorem rowComparison_projection (D : EtaleTermwiseHypercohomology X K)
    (p : ℕ) (q : ℤ) :
    filteredComplexPageπ D.sectionsTotal D.L 1 (q, (p : ℤ)) ≫
        (D.rowComparison p q).hom =
      (D.rowCyclesIso p q).inv ≫
        (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{uNatural + 1}).mapHomologicalComplex
          (ComplexShape.up ℕ)).obj (D.I.X q)).homologyπ p := by
  let _ := D.rowCycleClass_isIso p q
  have h := D.rowCycleClass_comparison p q
  change (D.rowCyclesIso p q).hom ≫ _ = _ at h
  have hh := congrArg (fun t ↦ (D.rowCyclesIso p q).inv ≫ t) h
  simpa only [Category.assoc, Iso.inv_hom_id_assoc] using hh

end EtaleTermwiseHypercohomology
end AlgebraicGeometry.Etale

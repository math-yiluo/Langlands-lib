/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Mathlib.FieldTheory.IsSepClosed
public import Mathlib.FieldTheory.KrullTopology
public import Mathlib.Topology.Algebra.Group.Quotient
import Mathlib.FieldTheory.Galois.Infinite
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.Topology.Algebra.OpenSubgroup

/-!
# Open subgroups and finite separable fixed fields

Source: Stacks Project, Tags 03QR and 03SF, with the Galois correspondence in Tag 0BML
(blueprint: lem-exc-etale-open-subgroup-fixed-field).
-/

@[expose] public section

universe u v w

/-- (blueprint: lem-exc-etale-open-subgroup-fixed-field) Stacks, Tags 03QR and 0BML.
For an open subgroup of the absolute Galois group, the fixed field is finite and separable,
and its fixing subgroup is the original subgroup. The quotient is finite and discrete;
its left translation action is continuous. Conversely, a point in a finite transitive
discrete continuous G-set has open stabilizer, whose fixed field is finite separable.

For the first clause, apply the fixed-field Galois correspondence to the open (hence closed)
subgroup, as in `lem-exc-etale-open-subgroup-fixed-field-galois`. Compactness of the Krull
topology makes its coset space finite, while openness makes that space discrete, as in
`lem-exc-etale-open-subgroup-quotient-finite-discrete`. For the converse, continuity on a
discrete set makes the point stabilizer open; apply the fixed-field correspondence again. -/
theorem openSubgroup_fixedField_finite_separable
    (K : Type u) (Ks : Type v) [Field K] [Field Ks] [Algebra K Ks]
    [IsSepClosure K Ks] :
    (∀ H : Subgroup Gal(Ks/K), IsOpen (H : Set Gal(Ks/K)) →
      FiniteDimensional K (IntermediateField.fixedField H) ∧
      Algebra.IsSeparable K (IntermediateField.fixedField H) ∧
      (IntermediateField.fixedField H).fixingSubgroup = H ∧
      Finite (Gal(Ks/K) ⧸ H) ∧ DiscreteTopology (Gal(Ks/K) ⧸ H) ∧
      ContinuousSMul Gal(Ks/K) (Gal(Ks/K) ⧸ H)) ∧
    (∀ (X : Type w) [TopologicalSpace X] [DiscreteTopology X] [Finite X]
      [MulAction Gal(Ks/K) X] [ContinuousSMul Gal(Ks/K) X]
      [MulAction.IsPretransitive Gal(Ks/K) X] (x : X),
      IsOpen (MulAction.stabilizer Gal(Ks/K) x : Set Gal(Ks/K)) ∧
      FiniteDimensional K
        (IntermediateField.fixedField (MulAction.stabilizer Gal(Ks/K) x)) ∧
      Algebra.IsSeparable K
        (IntermediateField.fixedField (MulAction.stabilizer Gal(Ks/K) x))) := by
  have forward : ∀ H : Subgroup Gal(Ks/K), IsOpen (H : Set Gal(Ks/K)) →
      FiniteDimensional K (IntermediateField.fixedField H) ∧
      Algebra.IsSeparable K (IntermediateField.fixedField H) ∧
      (IntermediateField.fixedField H).fixingSubgroup = H ∧
      Finite (Gal(Ks/K) ⧸ H) ∧ DiscreteTopology (Gal(Ks/K) ⧸ H) ∧
      ContinuousSMul Gal(Ks/K) (Gal(Ks/K) ⧸ H) := by
    intro H hH
    have hfix : (IntermediateField.fixedField H).fixingSubgroup = H :=
      InfiniteGalois.fixingSubgroup_fixedField ⟨H, H.isClosed_of_isOpen hH⟩
    have hfinite : FiniteDimensional K (IntermediateField.fixedField H) :=
      (InfiniteGalois.isOpen_iff_finite _).mp (by rw [hfix]; exact hH)
    exact ⟨hfinite, inferInstance, hfix, H.quotient_finite_of_isOpen hH,
      QuotientGroup.discreteTopology hH, inferInstance⟩
  refine ⟨forward, ?_⟩
  intro X _ _ _ _ _ _ x
  have hopen := stabilizer_isOpen Gal(Ks/K) x
  exact ⟨hopen, (forward _ hopen).1, (forward _ hopen).2.1⟩

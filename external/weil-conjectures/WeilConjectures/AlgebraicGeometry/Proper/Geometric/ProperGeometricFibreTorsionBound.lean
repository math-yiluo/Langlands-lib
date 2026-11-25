/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import Mathlib.Topology.Defs.Filter
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.CategoryTheory.Sites.Sheaf
public import WeilConjectures.AlgebraicGeometry.BaseChangeConventions
public import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Additive
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeFibreDimensionBound
import WeilConjectures.AlgebraicGeometry.SmoothPurity.DimensionExtension
import WeilConjectures.AlgebraicGeometry.SmoothPurity.SeparablyClosedTorsionCohomologicalDimension
import WeilConjectures.AlgebraicGeometry.Finite.Type.FiniteTypeTorsionCohomologicalDimension

/-!
# Uniform torsion cohomology bound for proper geometric fibres

## References

* Stacks Project, paragraph (1)
* Stacks Project, Tags 0A3V, 00P3 and 0F0V
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

/-- A proper morphism with quasi-compact target has a uniform cohomology bound for
sectionwise torsion abelian sheaves on all its geometric fibres. Each section has its
own nonzero integer annihilator; no common annihilator is part of the hypothesis.
Empty bases and empty fibres are included. -/
theorem exists_proper_geometricFibre_torsion_cohomology_bound
    {X Y : Scheme.{u}} (p : X ⟶ Y) [IsProper p] [CompactSpace Y] :
    ∃ c : ℕ, ∀ (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
      (ybar : Spec (.of Ω) ⟶ Y)
      (F : Sheaf (pullback p ybar).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (U : (pullback p ybar).Etaleᵒᵖ) (s : F.obj.obj U),
        ∃ n : ℤ, n ≠ 0 ∧ n • s = 0) →
      ∀ i : ℤ, (c : ℤ) < i →
        Subsingleton ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback p ybar) i).obj
          ((DerivedCategory.singleFunctor _ 0).obj F)) := by
  classical
  obtain ⟨e, he⟩ := exists_fibre_dimension_bound p
  refine ⟨2 * e, ?_⟩
  intro Ω _ _ ybar F hF i hi
  have hdim : topologicalKrullDim (pullback p ybar : Scheme.{u}) ≤
      (e : WithBot ℕ∞) := by
    obtain ⟨⟨y, t⟩, rfl⟩ := (Scheme.SpecToEquivOfField Ω Y).symm.surjective ybar
    let : Algebra (Y.residueField y) Ω := t.hom.toAlgebra
    have : LocallyOfFiniteType (p.fiberToSpecResidueField y) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    have : QuasiCompact (p.fiberToSpecResidueField y) := by
      dsimp [Scheme.Hom.fiberToSpecResidueField]
      infer_instance
    let : (p.fiber y).Over (Spec (.of (Y.residueField y))) :=
      ⟨p.fiberToSpecResidueField y⟩
    have : LocallyOfFiniteType (p.fiber y ↘ Spec (.of (Y.residueField y))) :=
      inferInstanceAs (LocallyOfFiniteType (p.fiberToSpecResidueField y))
    have : QuasiCompact (p.fiber y ↘ Spec (.of (Y.residueField y))) :=
      inferInstanceAs (QuasiCompact (p.fiberToSpecResidueField y))
    calc
      topologicalKrullDim
          (pullback p (Spec.map t ≫ Y.fromSpecResidueField y) : Scheme.{u}) =
          topologicalKrullDim
            (pullback (p.fiberToSpecResidueField y) (Spec.map t) : Scheme.{u}) :=
        (IsHomeomorph.topologicalKrullDim_eq _ (pullbackLeftPullbackSndIso p
          (Y.fromSpecResidueField y) (Spec.map t)).hom.homeomorph.isHomeomorph).symm
      _ = topologicalKrullDim (p.fiber y) :=
        (topologicalKrullDim_fieldExtension_and_denseOpen
          (X := p.fiber y) (K := Y.residueField y)).1 Ω
      _ ≤ _ := he y
  cases isEmpty_or_nonempty (pullback p ybar : Scheme.{u}) with
  | inl h =>
    let := h
    have : (Etale.rightDerivedGlobalSections AddCommGrpCat.{u + 1}
        (pullback p ybar)).Additive := by
      dsimp [Etale.rightDerivedGlobalSections]
      infer_instance
    have : (Etale.cohomology AddCommGrpCat.{u + 1} (pullback p ybar) i).Additive := by
      dsimp [Etale.cohomology]
      infer_instance
    exact AddCommGrpCat.isZero_iff_subsingleton.mp
      ((Etale.cohomology AddCommGrpCat.{u + 1} (pullback p ybar) i).map_isZero
        ((DerivedCategory.singleFunctor _ 0).map_isZero
          (Scheme.Etale.isZero_sheaf_of_isEmpty F)))
  | inr h =>
    have hnonneg : 0 ≤ topologicalKrullDim (pullback p ybar : Scheme.{u}) := by
      apply Order.krullDim_nonneg_iff.mpr
      obtain ⟨x⟩ := h
      exact ⟨⟨closure {x}, isIrreducible_singleton.closure, isClosed_closure⟩⟩
    have hnat : ∃ d : ℕ,
        topologicalKrullDim (pullback p ybar : Scheme.{u}) = (d : WithBot ℕ∞) := by
      generalize topologicalKrullDim (pullback p ybar : Scheme.{u}) = n at *
      induction n using WithBot.recBotCoe with
      | bot => exact False.elim (not_le_of_gt (by decide : (⊥ : WithBot ℕ∞) < 0) hnonneg)
      | coe n =>
        induction n using ENat.recTopCoe with
        | top => exact False.elim (not_le_of_gt
            (WithBot.coe_lt_coe.mpr (ENat.natCast_lt_top e)) hdim)
        | coe n => exact ⟨n, rfl⟩
    obtain ⟨d, hd⟩ := hnat
    have hde : d ≤ e := by exact_mod_cast hd ▸ hdim
    have htor : F.IsTorsion := Sheaf.IsTorsion.of_forall_isAddTorsion fun U s ↦
      isOfFinAddOrder_iff_zsmul_eq_zero.mpr (hF U s)
    let : (pullback p ybar).Over (Spec (.of Ω)) := ⟨pullback.snd p ybar⟩
    have : LocallyOfFiniteType (pullback p ybar ↘ Spec (.of Ω)) :=
      inferInstanceAs (LocallyOfFiniteType (pullback.snd p ybar))
    have : QuasiCompact (pullback p ybar ↘ Spec (.of Ω)) :=
      inferInstanceAs (QuasiCompact (pullback.snd p ybar))
    have hcd := Scheme.hasTorsionEtaleCohomologicalDimensionLE_of_finiteType Ω 0 d
      (Scheme.hasTorsionEtaleCohomologicalDimensionLE_zero_of_isSepClosed Ω)
      (pullback p ybar) hd
    have hn : i = (i.toNat : ℤ) := by omega
    rw [hn]
    exact hcd F htor i.toNat (by omega)

end AlgebraicGeometry

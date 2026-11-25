/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Geometrically.Irreducible
public import Mathlib.AlgebraicGeometry.Morphisms.SchemeTheoreticallyDominant
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Mathlib.FieldTheory.IntermediateField.Adjoin.Algebra
import Mathlib.AlgebraicGeometry.FunctionField

/-! # Affine steps in the radicial generic field construction

Source: Stacks Project, Tags 0559 and 030R. -/

@[expose] public section

set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Topology
namespace AlgebraicGeometry

/-- The generic fibre is reduced because its affine ring is a localization of the
reduced source ring. The residue field at the generic point identifies with the actual
function field of the integral base. Source: Stacks Project, Tag 0559, second proof. -/
private theorem reduced_generic_fibre
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) (η : S) (hη : IsGenericPoint η Set.univ) :
    IsReduced (g.fiber η) := by
  classical
  have heq : η = genericPoint S := hη.eq (genericPoint_spec S)
  subst η
  have : Nonempty (⊤ : S.Opens) := ⟨⟨genericPoint S, trivial⟩⟩
  have hr : IsIso (S.residue (genericPoint S)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).mpr
    exact ⟨(show S.functionField →+* S.residueField (genericPoint S) from
      (S.residue (genericPoint S)).hom).injective, S.residue_surjective _⟩
  let A := Γ(S, ⊤)
  let B := Γ(Z, ⊤)
  let C := Γ(Spec (S.residueField (genericPoint S)), ⊤)
  let D := Γ(g.fiber (genericPoint S), ⊤)
  let t := S.fromSpecResidueField (genericPoint S)
  let : Algebra A B := g.appTop.hom.toAlgebra
  let : Algebra A C := t.appTop.hom.toAlgebra
  let : Algebra B D := (g.fiberι (genericPoint S)).appTop.hom.toAlgebra
  let : Algebra C D := (g.fiberToSpecResidueField (genericPoint S)).appTop.hom.toAlgebra
  let : Algebra A D := ((g.fiberι (genericPoint S)).appTop.hom.comp g.appTop.hom).toAlgebra
  have : IsScalarTower A B D := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower A C D := by
    apply IsScalarTower.of_algebraMap_eq'
    have he := congrArg Scheme.Hom.appTop (g.fiber_fac (genericPoint S))
    simp only [Scheme.Hom.comp_appTop] at he
    exact congrArg CommRingCat.Hom.hom he
  let e : C ≅ S.functionField :=
    Scheme.ΓSpecIso (S.residueField (genericPoint S)) ≪≫ (asIso (S.residue _)).symm
  let : Algebra A S.functionField := (S.germToFunctionField ⊤).hom.toAlgebra
  let eA : C ≃ₐ[A] S.functionField :=
    { e.commRingCatIsoToRingEquiv with
      commutes' := by
        intro x
        have he : t.appTop ≫ e.hom = S.germToFunctionField ⊤ := by
          change (Spec.map (S.residue _) ≫ S.fromSpecStalk _).appTop ≫
            ((Scheme.ΓSpecIso _).hom ≫ inv (S.residue _)) = _
          rw [Scheme.Hom.comp_appTop, Category.assoc,
            Scheme.ΓSpecIso_naturality_assoc, Scheme.fromSpecStalk_appTop]
          simp [Scheme.germToFunctionField, Category.assoc]
        exact congr($(he) x) }
  have : IsFractionRing A S.functionField :=
    functionField_isFractionRing_of_isAffineOpen S ⊤ (isAffineOpen_top S)
  have : IsFractionRing A C := IsFractionRing.of_algEquiv eA.symm
  have H := isPushout_appTop_of_isPullback (IsPullback.of_hasPullback g t)
  have : Algebra.IsPushout A C B D :=
    CommRingCat.isPushout_iff_isPushout.mp H.flip
  have : Algebra.IsPushout A B C D := Algebra.IsPushout.symm inferInstance
  have : IsLocalization (Algebra.algebraMapSubmonoid B (nonZeroDivisors A)) D :=
    (Algebra.isLocalization_iff_isPushout (nonZeroDivisors A) C).mpr inferInstance
  have : _root_.IsReduced D :=
    isReduced_localizationPreserves (Algebra.algebraMapSubmonoid B (nonZeroDivisors A))
      D inferInstance
  exact isReduced_of_isAffine_isReduced _

/-- A reduced affine family with geometrically irreducible generic fibre has a finitely
generated generic function field.
Source: Stacks Project, Tag 0559, second proof, the generic function field construction.
Proof: identify S and Z with Spec A and Spec B. At the generic point the base residue field
is Frac A, and the fibre ring is B localized at the nonzero elements of A. Localization
preserves reducedness. Geometric irreducibility implies irreducibility and nonemptiness,
so this reduced ring is a nonzero domain. Take its actual fraction field L. Finite
presentation gives a finite set of algebra generators of the fibre ring; they also generate
L as a field. The injection of the fibre ring into its fraction field gives a
scheme-theoretically dominant spectrum map j. Its composite to the base spectrum is the
spectrum of the induced field algebra map by contravariant functoriality.
The empty fibre is excluded by geometric irreducibility; a zero-dimensional fibre gives
its ordinary finite function field. No geometrically reduced hypothesis is used.
(blueprint: lem-sbc-generic-fibre-dominant-field) -/
theorem exists_generic_fibre_dominant_field
    {Z S : Scheme.{u}} [IsAffine Z] [IsReduced Z] [IsAffine S] [IsIntegral S]
    (g : Z ⟶ S) [Flat g] [LocallyOfFinitePresentation g]
    (η : S) (hη : IsGenericPoint η Set.univ)
    (hgeom : GeometricallyIrreducible (g.fiberToSpecResidueField η)) :
    ∃ (L : Type u) (hL : Field L) (aL : Algebra (S.residueField η) L),
      letI := hL
      letI := aL
      (⊤ : IntermediateField (S.residueField η) L).FG ∧
      ∃ j : Spec (.of L) ⟶ g.fiber η,
        IsSchemeTheoreticallyDominant j ∧
        j ≫ g.fiberToSpecResidueField η =
          Spec.map (CommRingCat.ofHom (algebraMap (S.residueField η) L)) := by
  classical
  let X := g.fiber η
  let p := g.fiberToSpecResidueField η
  have : GeometricallyIrreducible p := hgeom
  have : IrreducibleSpace X :=
    GeometricallyIrreducible.irreducibleSpace_of_subsingleton p
  have : IsReduced X := reduced_generic_fibre g η hη
  have : IsIntegral X := isIntegral_of_irreducibleSpace_of_isReduced X
  have : Nonempty (⊤ : X.Opens) := ⟨⟨genericPoint X, trivial⟩⟩
  let K := S.residueField η
  let a : K →+* Γ(X, ⊤) := ((Scheme.ΓSpecIso K).inv ≫ p.appTop).hom
  let : Algebra K Γ(X, ⊤) := a.toAlgebra
  let b : K →+* X.functionField := (X.germToFunctionField ⊤).hom.comp a
  let : Algebra K X.functionField := b.toAlgebra
  have : IsScalarTower K Γ(X, ⊤) X.functionField :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : LocallyOfFiniteType p := by
    dsimp [p, Scheme.Hom.fiberToSpecResidueField]
    infer_instance
  have : Algebra.FiniteType K Γ(X, ⊤) := by
    have hp := HasRingHomProperty.appTop (P := @LocallyOfFiniteType) p inferInstance
    exact RingHom.FiniteType.comp hp (RingHom.FiniteType.of_surjective (Scheme.ΓSpecIso K).inv.hom
      (Scheme.ΓSpecIso K).commRingCatIsoToRingEquiv.symm.surjective)
  have : IsFractionRing Γ(X, ⊤) X.functionField :=
    functionField_isFractionRing_of_isAffineOpen X ⊤ (isAffineOpen_top X)
  have : Algebra.EssFiniteType Γ(X, ⊤) X.functionField :=
    Algebra.EssFiniteType.of_isLocalization X.functionField (nonZeroDivisors Γ(X, ⊤))
  have : Algebra.EssFiniteType K X.functionField :=
    Algebra.EssFiniteType.comp K Γ(X, ⊤) X.functionField
  refine ⟨X.functionField, inferInstance, inferInstance, IntermediateField.fg_top _ _,
    X.fromSpecStalk (genericPoint X), ?_, ?_⟩
  · have : IsDominant (X.fromSpecStalk (genericPoint X)) := by
      rw [isDominant_iff, DenseRange]
      apply dense_iff_closure_eq.mpr
      apply Set.eq_univ_of_univ_subset
      rw [← genericPoint_spec X]
      exact closure_mono (Set.singleton_subset_iff.mpr ⟨_, X.fromSpecStalk_closedPoint⟩)
    exact IsSchemeTheoreticallyDominant.of_isDominant _
  · refine ext_of_isAffine ?_
    rw [← cancel_epi (Scheme.ΓSpecIso _).inv, ← Scheme.ΓSpecIso_inv_naturality]
    ext x
    simp only [Scheme.Hom.comp_appTop, Scheme.fromSpecStalk_appTop]
    rfl

end AlgebraicGeometry

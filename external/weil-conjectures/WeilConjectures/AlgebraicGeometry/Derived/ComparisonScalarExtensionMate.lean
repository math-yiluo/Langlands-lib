/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
public import WeilConjectures.AlgebraicGeometry.Derived.DerivedMorphismSheafComparison
import all WeilConjectures.AlgebraicGeometry.ProperBaseChange.WitnessCompatibility
import WeilConjectures.SixFunctors.ProEtale.Comparison.Flat

/-! # Derived scalar extension commutes with the etale/pro-etale comparison

Source: Stacks Tags 09B1, 0F63, 06YY and 07A4
(blueprint: def-sfb-finite-coefficient-system-evaluation).

For a ring map `φ : A →+* B`, the mate of the canonical square
`Scheme.comparisonRestrictScalarsIso` (derived restriction of scalars commutes with the
exact comparison pullback `ν^*`) with respect to the derived scalar-extension adjunctions
on the small etale and pro-etale sites is invertible. This is the pro-etale comparison
analogue of `AlgebraicGeometry.ProEtale.proEtaleScalarPullbackMate_isIso` and uses the
same flat-resolution machinery of `WitnessCompatibility`.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

attribute [local instance] pbcRestriction_isRightAdjoint

universe u

/-- The comparison pullback `ν^*` preserves flat sheaves of modules over an arbitrary ring:
the local relation criterion transports along the representably flat, cover-preserving
inclusion of the small etale site into the small pro-etale site. -/
private theorem comparisonUpperStar_preservesFlat (A : Type (u + 1)) [CommRing A]
    (X : Scheme.{u}) :
    (comparisonUpperStar (ModuleCat.{u + 1} A) X).PreservesFlat :=
  ⟨fun hF ↦ flat_pullback_of_local_relations (coverPreserving_toProEt X) hF⟩

/-- The ordinary (underived) scalar-extension mate of the square
`Scheme.comparisonRestrictScalarsSheafIso` is invertible: by iterated mates it suffices
that the conjugate square of right adjoints (`ν_*` and coextension of scalars) is
invertible, and that square is the identity. -/
private theorem comparison_ordinary_mate_isIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    IsIso (((mateEquiv (scalarAdjunction X.smallEtaleTopology φ)
      (scalarAdjunction (Scheme.ProEt.topology X) φ)).symm
      (TwoSquare.mk _ _ _ _ (Scheme.comparisonRestrictScalarsSheafIso X A φ).hom))) := by
  let adj₁ := (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).comp
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
  let adj₂ := (comparisonAdjunction (ModuleCat.{u + 1} B) X).comp
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
  have he (M : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B)) :
      (Adjunction.leftAdjointUniq adj₁ adj₂).hom.app M =
        Scheme.comparisonRestrictScalarsMap X A φ M := by
    apply (adj₁.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    change adj₂.unit.app M =
      (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).homEquiv _ _
        ((comparisonAdjunction (ModuleCat.{u + 1} A) X).homEquiv _ _
          (Scheme.comparisonRestrictScalarsMap X A φ M))
    rw [Scheme.comparisonRestrictScalarsMap, Equiv.apply_symm_apply,
      Adjunction.homEquiv_unit]
    dsimp only [adj₂]
    rw [Adjunction.comp_unit_app]
    exact (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ).unit.naturality
      ((comparisonAdjunction (ModuleCat.{u + 1} B) X).unit.app M)
  have hE : (Scheme.comparisonRestrictScalarsSheafIso X A φ).hom =
      ((conjugateIsoEquiv adj₂ adj₁).symm (Iso.refl _)).hom := by
    ext M : 2
    exact (he M).symm.trans (Adjunction.leftAdjointUniq_inv_app adj₂ adj₁ M).symm
  apply isIso_left_mate_of_iterated
    (scalarAdjunction X.smallEtaleTopology φ)
    (scalarAdjunction (Scheme.ProEt.topology X) φ)
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (comparisonAdjunction (ModuleCat.{u + 1} B) X)
  have h := mate_of_conjugate
    (comparisonAdjunction (ModuleCat.{u + 1} B) X)
    (comparisonAdjunction (ModuleCat.{u + 1} A) X)
    (Sheaf.restrictCoextendScalarsAdj (Scheme.ProEt.topology X) φ)
    (Sheaf.restrictCoextendScalarsAdj X.smallEtaleTopology φ)
    (Iso.refl _) (𝟙 _) (by
      ext F V x
      simp only [mateEquiv_apply, NatTrans.comp_app, Functor.comp_obj,
        Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
        Functor.associator_hom_app, Functor.associator_inv_app,
        Functor.whiskerLeft_app, Functor.whiskerRight_app, NatTrans.id_app,
        Category.id_comp]
      exact congrArg (fun k ↦ k.hom x)
        ((ModuleCat.restrictCoextendScalarsAdj.{u + 1, u + 1, u + 1} φ).right_triangle_components
          _))
  rw [hE, h]
  infer_instance

/-- The derived mate for the explicit (flat-resolution) derived scalar adjunctions is
invertible: `ν^*` preserves flatness, so flat K-flat resolutions compute both derived
scalar extensions, and on them the mate is the ordinary one. -/
private theorem comparison_computed_mate_isIso {A B : Type (u + 1)} [CommRing A] [CommRing B]
    (φ : A →+* B) (X : Scheme.{u}) :
    IsIso (((mateEquiv
      (scalarDerivedAdjunctionData X.smallEtaleTopology φ).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) φ).adjunction).symm
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso
          (Scheme.comparisonRestrictScalarsSheafIso X A φ)).hom))) := by
  have := comparisonUpperStar_preservesFlat A X
  have : IsIso (((mateEquiv (scalarAdjunction X.smallEtaleTopology φ)
      (scalarAdjunction (Scheme.ProEt.topology X) φ)).symm
      (TwoSquare.mk _ _ _ _
        (Scheme.comparisonRestrictScalarsSheafIso X A φ).symm.inv))) := by
    simpa only [Iso.symm_inv] using comparison_ordinary_mate_isIso φ X
  have h := derived_mate_isIso_of_flat
    (A := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A))
    (B := Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} B))
    (C := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} A))
    (D := Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} B))
    (scalarAdjunction X.smallEtaleTopology φ)
    (scalarAdjunction (Scheme.ProEt.topology X) φ)
    (scalarDerivedAdjunctionData X.smallEtaleTopology φ)
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) φ)
    (comparisonUpperStar (ModuleCat.{u + 1} A) X)
    (comparisonUpperStar (ModuleCat.{u + 1} B) X)
    (Scheme.comparisonRestrictScalarsSheafIso X A φ).symm
  have hs : (Functor.mapDerivedCategoryNatIso
      (Scheme.comparisonRestrictScalarsSheafIso X A φ).symm).inv =
      (Functor.mapDerivedCategoryNatIso (Scheme.comparisonRestrictScalarsSheafIso X A φ)).hom := by
    simpa only [Iso.symm_symm_eq] using
      (Functor.mapDerivedCategoryNatIso_symm
        (Scheme.comparisonRestrictScalarsSheafIso X A φ).symm).symm
  simpa only [Functor.mapDerivedCategorySquareIso,
    Functor.mapDerivedCategoryNatIso_symm, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, hs, Category.assoc] using h

/-- The derived scalar-extension mate of the etale/pro-etale comparison square
`Scheme.comparisonRestrictScalarsIso` is invertible: derived scalar extension commutes with
the exact comparison pullback `ν^*`, for an arbitrary ring map `φ`.
Source: Stacks 09B1, 0F63, 06YY and 07A4
(blueprint: def-sfb-finite-coefficient-system-evaluation).
Proof: `ν^*` preserves flat sheaves, so flat K-flat resolutions compute both derived scalar
extensions; there the mate is the ordinary one, which is invertible by iterated mates since
the conjugate square of right adjoints is the identity. Finally transport the result across
the uniqueness of the derived scalar left adjoints. -/
theorem isIso_mate_comparisonRestrictScalarsIso {A B : Type (u + 1)} [CommRing A]
    [CommRing B] (φ : A →+* B) (X : Scheme.{u}) :
    IsIso (((mateEquiv
      (G := (comparisonUpperStar (ModuleCat.{u + 1} A) X).mapDerivedCategory)
      (H := (comparisonUpperStar (ModuleCat.{u + 1} B) X).mapDerivedCategory)
      (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
      (Adjunction.ofIsRightAdjoint
        (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))).symm
      (TwoSquare.mk _ _ _ _ (Scheme.comparisonRestrictScalarsIso X A φ).hom))) := by
  have : IsIso (((mateEquiv
      (scalarDerivedAdjunctionData X.smallEtaleTopology φ).adjunction
      (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) φ).adjunction).symm
      (TwoSquare.mk _ _ _ _ (Scheme.comparisonRestrictScalarsIso X A φ).hom))) :=
    comparison_computed_mate_isIso φ X
  exact isIso_left_mate_change_adjunction
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars X.smallEtaleTopology φ))
    (Adjunction.ofIsRightAdjoint (Sheaf.derivedRestrictScalars (Scheme.ProEt.topology X) φ))
    (scalarDerivedAdjunctionData X.smallEtaleTopology φ).adjunction
    (scalarDerivedAdjunctionData (Scheme.ProEt.topology X) φ).adjunction
    (Scheme.comparisonRestrictScalarsIso X A φ).hom

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Topology.Category.Profinite.AsLimit
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.AlgebraicGeometry.ProEtalePointPullback
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.ContinuousMap
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import Mathlib.NumberTheory.Padics.RingHoms
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.FiniteSubextension
public import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.RingTheory.Ideal.Quotient.Operations

/-!
# Data for the completed coefficient comparison

The integral comparison is stated as a limit universal property, with its reductions
normalized on constant sections. Rationalization is stated as the sequential module
colimit together with the ring-localization universal property.

## Implementation details

These formulations specify the canonical comparisons without choosing new models for the
coefficients. The pullback equations in `SfbCompletedCoefficientComparison` use the bundled
ring comparison (identity followed by `condensedPullbackHom`), which avoids expensive instance
conversion.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor

namespace AlgebraicGeometry.ProEtale

/-- Constant rings, as ring objects in abelian sheaves, with the standard integer tensor. -/
noncomputable def sfbConstantRing (X : Scheme.{u}) :
    RingCat.{u + 1} ⥤ Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (Scheme.ProEt.topology X) Ab.{u + 1}).mapMon

/-- The same constant-ring construction on the pro-étale point. -/
noncomputable def sfbPointConstantRing :
    RingCat.{u + 1} ⥤ Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) :=
  RingCat.toMonAb ⋙ (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).mapMon

/-- The quotient tower, including the harmless terminal zero quotient at exponent zero.
Its maps are the quotient reductions, not arbitrary ring homomorphisms. -/
noncomputable def sfbCoefficientQuotientTower (R : Type) [CommRing R] (I : Ideal R) :
    ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (R ⧸ I ^ n)))
    (fun n : ℕ ↦ RingCat.ofHom
    (ULift.ringEquiv.symm.toRingHom.comp
      ((Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ n))).comp
        ULift.ringEquiv.toRingHom)))

/-- Constant sections of a topological ring, mapped into its condensed abelian sheaf.
This is the adjoint of the map sending a scalar to its constant continuous function. -/
noncomputable def sfbConstantToContinuous (R : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] :
    (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} R)) ⟶ Profinite.continuousMapRingObj R :=
  ((sheafificationAdjunction (coherentTopology Profinite.{u}) Ab.{u + 1}).homEquiv _ _).symm
    { app S := AddCommGrpCat.ofHom
        { toFun := fun x ↦ ULift.up (ContinuousMap.const S.unop x.down)
          map_zero' := rfl
          map_add' := fun _ _ ↦ rfl }
      naturality := fun _ _ _ ↦ rfl }

/-- The pulled-back inclusion of integers into their coefficient field. The underlying
map is precisely `p_X^*` applied to postcomposition with the given continuous inclusion. -/
noncomputable def sfbCoefficientInclusion (R K : Type) [CommRing R] [TopologicalSpace R]
    [IsTopologicalRing R] [CommRing K] [TopologicalSpace K] [IsTopologicalRing K]
    (φ : R →+* K) (hφ : Continuous φ) (X : Scheme.{u}) :
    coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) :=
  (upperStarFromPoint X).mapMon.map (Mon.ofHom
    ((sheafCompose (coherentTopology Profinite.{u})
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).map
        (Profinite.continuousMapRingSheafMap φ hφ)))

/-- The coefficient field as a module over the pulled-back integers, using their actual
inclusion. -/
noncomputable def sfbRationalCoefficientModule (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K]
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) (X : Scheme.{u}) :
    Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  (Mod.comap (i X).hom).obj
    (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj K) X))

/-- The sequential diagram of integer modules with transition multiplication by `ℓ`.
Multiplication by `ℓ` is used only as a module map. -/
noncomputable def sfbRationalizationSequence (ℓ : ℕ) (R : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] (X : Scheme.{u}) :
    ℕ ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.continuousMapRingObj R) X) :=
  Functor.ofSequence (fun _ : ℕ ↦ ℓ •
    𝟙 (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj R) X)))

/-- The completed coefficient comparisons: the integral coefficient ring is the limit of its
reductions modulo powers of `I` (normalized by the quotient maps on constants), the rational
coefficient ring is the sequential colimit of multiplication by `ℓ` and has the universal
property of the localization as rings, and these comparisons are compatible with pullback. -/
def SfbCompletedCoefficientComparison (ℓ : ℕ) (R K : Type) [CommRing R]
    [TopologicalSpace R] [IsTopologicalRing R] [CommRing K] [TopologicalSpace K]
    [IsTopologicalRing K] (I : Ideal R)
    (i : ∀ X : Scheme.{u}, coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶
      coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K))) : Prop :=
  ∃ ρ : (Functor.const ℕᵒᵖ).obj (Mon.mk (Profinite.continuousMapRingObj.{u} R)) ⟶
      sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing,
    (∀ n : ℕ, sfbConstantToContinuous R ≫ (ρ.app (op n)).hom =
      (constantSheaf (coherentTopology Profinite.{u}) Ab.{u + 1}).map
        (AddCommGrpCat.ofHom
          (ULift.ringEquiv.symm.toRingHom.comp
            ((Ideal.Quotient.mk (I ^ n)).comp ULift.ringEquiv.toRingHom)).toAddMonoidHom)) ∧
    (∀ X : Scheme.{u},
      Nonempty (IsLimit ((upperStarFromPoint X).mapMon.mapCone
        (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))) ∧
      Nonempty ((sfbCoefficientQuotientTower R I ⋙ sfbPointConstantRing ⋙
        (upperStarFromPoint X).mapMon) ≅
          (sfbCoefficientQuotientTower R I ⋙ sfbConstantRing X))) ∧
    (∀ (X Y : Scheme.{u}) (f : X ⟶ Y),
      Nonempty (IsLimit ((upperStar Ab.{u + 1} f).mapMon.mapCone
        ((upperStarFromPoint Y).mapMon.mapCone
          (Cone.mk (Mon.mk (Profinite.continuousMapRingObj R)) ρ))))) ∧
    ∃ ι : ∀ X : Scheme.{u}, sfbRationalizationSequence ℓ R X ⟶
        (Functor.const ℕ).obj (sfbRationalCoefficientModule R K i X),
      (∀ X : Scheme.{u},
        ((ι X).app 0).hom = (i X).hom ∧
        Nonempty (IsColimit (Cocone.mk (sfbRationalCoefficientModule R K i X) (ι X))) ∧
        IsIso (ℓ • 𝟙 (condensedRingObj (Profinite.continuousMapRingObj K) X))) ∧
      (∀ (X Y : Scheme.{u}) (f : X ⟶ Y) (m : ℕ),
        (upperStar Ab.{u + 1} f).map (((ι Y).app m).hom) ≫
            ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj K))).hom).hom =
          ((coefficientPullbackIso f
            (Mon.mk (Profinite.continuousMapRingObj R))).hom).hom ≫
            ((ι X).app m).hom) ∧
      (∀ (X : Scheme.{u}) (B : Mon (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})),
        IsIso (ℓ • 𝟙 B.X) →
        ∀ a : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj R)) ⟶ B,
          ∃! b : coefficientRing X (Mon.mk (Profinite.continuousMapRingObj K)) ⟶ B,
            i X ≫ b = a)

/-- The finite-subextension diagram, in ring objects rather than only abelian sheaves. -/
noncomputable def sfbFiniteSubfieldRingDiagram (ℓ : ℕ) [Fact ℓ.Prime] :
    PadicAlgCl.FiniteIntermediateField ℓ ⥤
      Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) where
  obj E := Mon.mk (Profinite.continuousMapRingObj E)
  map f := Mon.ofHom (Profinite.padicSubfieldRingObjMap ℓ (leOfHom f))
  map_id E := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_id ℓ E
  map_comp f g := by
    apply Mon.Hom.ext
    exact Profinite.padicSubfieldRingObjMap_comp ℓ (leOfHom f) (leOfHom g)

/-- The canonical finite-field cocone as a cocone of rings; its legs are the inclusions
into the finite-subextension-valued algebraic-closure coefficients. -/
noncomputable def sfbFiniteSubfieldRingCocone (ℓ : ℕ) [Fact ℓ.Prime] :
    Cocone (sfbFiniteSubfieldRingDiagram.{u} ℓ) where
  pt := Mon.mk (Profinite.padicAlgClRingObj ℓ)
  ι :=
    { app E := Mon.ofHom (Profinite.padicSubfieldRingObjToPadicAlgCl ℓ E)
      naturality := fun E F f ↦ by
        apply Mon.Hom.ext
        exact (Profinite.padicSubfieldRingObjMap_comp_toPadicAlgCl ℓ (leOfHom f)).trans
          (Category.comp_id _).symm }

/-- The standard finite constant coefficient rings `ZMod (ℓ^n)`, with reduction maps. -/
noncomputable def sfbZModCoefficientTower (ℓ : ℕ) : ℕᵒᵖ ⥤ RingCat.{u + 1} :=
  Functor.ofOpSequence (X := fun n : ℕ ↦ RingCat.of (ULift.{u + 1} (ZMod (ℓ ^ n))))
    (fun n : ℕ ↦ RingCat.ofHom (ULift.ringEquiv.symm.toRingHom.comp
      ((ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ n)) (ZMod (ℓ ^ n))).comp
        ULift.ringEquiv.toRingHom)))

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.DerivedExtendScalars

/-! # Restrictions and adjunctions of the finite coefficient derived extensions

For the derived extensions of scalars `derivedExtendScalarsSubfield` and
`derivedExtendScalarsToPadicAlgCl`, this file names the exact derived restrictions of
scalars, the derived extension/restriction adjunctions and their Hom equivalences.
These names cache the derived constructions, avoiding repeated elaboration of their
resolution and localization data.
-/

@[expose] public section
universe u
open CategoryTheory Limits
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale
open Scheme PadicAlgCl
variable (X : Scheme.{u}) (ℓ : ℕ) [Fact ℓ.Prime]

/-- The exact derived restriction between finite coefficient fields.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedRestriction {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
  (Mod.comap (padicSubfieldRingObjMap X ℓ h)).mapDerivedCategory

/-- The exact derived restriction from the condensed algebraic closure.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedFromAlgCl (E : FiniteIntermediateField ℓ) :
    DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ)) ⥤
      DerivedCategory (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)) :=
  (Mod.comap (padicSubfieldRingObjToPadicAlgCl X ℓ E)).mapDerivedCategory

/-- The canonical derived finite extension/restriction adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedAdjunction {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F) :
    derivedExtendScalarsSubfield X ℓ h ⊣ finiteCoefficientDerivedRestriction X ℓ h :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjMap X ℓ h)

/-- The canonical derived algebraic-closure extension/restriction adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedAlgClAdjunction (E : FiniteIntermediateField ℓ) :
    derivedExtendScalarsToPadicAlgCl X ℓ E ⊣ finiteCoefficientDerivedFromAlgCl X ℓ E :=
  Mod.derivedExtendMapDerivedCategoryAdjunction (padicSubfieldRingObjToPadicAlgCl X ℓ E)

/-- The Hom equivalence of the finite coefficient derived adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedHomEquiv {E F : FiniteIntermediateField ℓ}
    (h : E ≤ F)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ F))) :
    ((derivedExtendScalarsSubfield X ℓ h).obj K ⟶ L) ≃
      (K ⟶ (finiteCoefficientDerivedRestriction X ℓ h).obj L) :=
  (finiteCoefficientDerivedAdjunction X ℓ h).homEquiv K L

/-- The Hom equivalence of the algebraic-closure derived adjunction.
Source: `Mod.derivedExtendMapDerivedCategoryAdjunction` and exact scalar restriction.
(auxiliary; not a blueprint node) -/
noncomputable def finiteCoefficientDerivedAlgClHomEquiv (E : FiniteIntermediateField ℓ)
    (K : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicSubfieldRingObj X ℓ E)))
    (L : DerivedCategory
      (Mod (Sheaf (ProEt.topology X) Ab.{u + 1}) (padicAlgClRingObj X ℓ))) :
    ((derivedExtendScalarsToPadicAlgCl X ℓ E).obj K ⟶ L) ≃
      (K ⟶ (finiteCoefficientDerivedFromAlgCl X ℓ E).obj L) :=
  (finiteCoefficientDerivedAlgClAdjunction X ℓ E).homEquiv K L

end AlgebraicGeometry.ProEtale

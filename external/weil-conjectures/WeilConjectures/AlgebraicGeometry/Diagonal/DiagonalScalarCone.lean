/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.LinearScalarCone.LinearScalarCone

/-! # Scalar cones independent of quotient presentations

Source: Stacks 099M, the two-term free resolution of a principal quotient.
(blueprint: def-sfb-diagonal-scalar-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe a v w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.ProEtale

variable (A : Type a) [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The natural-scalar arrow, before taking its cone.
Source: Stacks 099M (blueprint: def-sfb-diagonal-scalar-cone). -/
abbrev diagonalScalarConeArrow (r : ℕ) :
    CochainComplex A ℤ ⥤ Arrow (CochainComplex A ℤ) where
  obj P := Arrow.mk (r • 𝟙 P)
  map {P Q} f := Arrow.homMk (f := Arrow.mk (r • 𝟙 P))
    (g := Arrow.mk (r • 𝟙 Q)) f f (by
      change f ≫ (r • 𝟙 Q) = (r • 𝟙 P) ≫ f
      simp only [Preadditive.nsmul_comp, Preadditive.comp_nsmul,
        Category.id_comp, Category.comp_id])

/-- The functorial two-term scalar cone, before localization.
Source: Stacks 099M (blueprint: def-sfb-diagonal-scalar-cone). -/
abbrev diagonalScalarConeComplex (r : ℕ) : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  diagonalScalarConeArrow A r ⋙ CochainComplex.ConeCoimage.cone

/-- The natural-power model is the existing integer-linear scalar cone.
Source: integer scalar action (blueprint: def-sfb-diagonal-scalar-cone). -/
def diagonalScalarConeComplexComparison (r : ℕ) :
    CochainComplex.LinearScalarCone.cochain (A := A) (r : ℤ) ≅
      diagonalScalarConeComplex A r :=
  Functor.isoWhiskerRight
    (NatIso.ofComponents (F := CochainComplex.smulArrow (𝒜 := A) (r : ℤ))
      (G := diagonalScalarConeArrow A r) (fun P ↦
      Arrow.isoMk (f := Arrow.mk ((r : ℤ) • 𝟙 P)) (g := Arrow.mk (r • 𝟙 P))
        (Iso.refl P) (Iso.refl P) (by simp)) (by
      intro P Q f
      ext <;> simp [diagonalScalarConeArrow])) CochainComplex.ConeCoimage.cone

/-- The inclusion in the degree-zero term of the two-term scalar resolution.
Source: Stacks 099M (blueprint: def-sfb-diagonal-scalar-cone). -/
def diagonalScalarConeComplexUnit (r : ℕ) :
    𝟭 (CochainComplex A ℤ) ⟶ diagonalScalarConeComplex A r where
  app P := CochainComplex.mappingCone.inr _
  naturality P Q f := by
    dsimp only [Functor.id_map, diagonalScalarConeComplex, diagonalScalarConeArrow]
    simp [CochainComplex.mappingCone.map]

/-- The derived scalar cone, obtained by localization of its explicit complex functor.
Source: Stacks 099M (blueprint: def-sfb-diagonal-scalar-cone). -/
abbrev diagonalScalarCone (r : ℕ) : DerivedCategory A ⥤ DerivedCategory A :=
  CochainComplex.LinearScalarCone.derived (A := A) (r : ℤ)

/-- The canonical comparison with the explicit complex cone.
Source: localization universal property (blueprint: def-sfb-diagonal-scalar-cone). -/
def diagonalScalarConeFactors (r : ℕ) :
    DerivedCategory.Q ⋙ diagonalScalarCone A r ≅
      diagonalScalarConeComplex A r ⋙ DerivedCategory.Q :=
  CochainComplex.LinearScalarCone.comparison (A := A) (r : ℤ) ≪≫
    Functor.isoWhiskerRight (diagonalScalarConeComplexComparison A r) DerivedCategory.Q

/-- The quotient unit in the localized two-term model.
Source: Stacks 099M (blueprint: def-sfb-diagonal-scalar-cone). -/
def diagonalScalarConeUnit (r : ℕ) : 𝟭 (DerivedCategory A) ⟶ diagonalScalarCone A r :=
  (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory A)).preimage
      ((Functor.rightUnitor DerivedCategory.Q).hom ≫
        Functor.whiskerRight (diagonalScalarConeComplexUnit A r) DerivedCategory.Q ≫
        (diagonalScalarConeFactors A r).inv)

/-- The derived unit is exactly the localization of the degree-zero inclusion.
Source: localization universal property (blueprint: def-sfb-diagonal-scalar-cone). -/
theorem diagonalScalarConeUnit_factors (r : ℕ) (P : CochainComplex A ℤ) :
    (diagonalScalarConeUnit A r).app (DerivedCategory.Q.obj P) ≫
      (diagonalScalarConeFactors A r).hom.app P =
        DerivedCategory.Q.map (CochainComplex.mappingCone.inr (r • 𝟙 P)) := by
  have h := congrArg (fun t ↦ t.app P)
    ((Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso A (.up ℤ)) (DerivedCategory A)).map_preimage
        ((Functor.rightUnitor DerivedCategory.Q).hom ≫
          Functor.whiskerRight (diagonalScalarConeComplexUnit A r) DerivedCategory.Q ≫
          (diagonalScalarConeFactors A r).inv))
  change (diagonalScalarConeUnit A r).app (DerivedCategory.Q.obj P) = _ at h
  rw [h]
  simp only [NatTrans.comp_app, Functor.rightUnitor_hom_app, Functor.whiskerRight_app,
    diagonalScalarConeComplexUnit, Category.assoc, Iso.inv_hom_id_app,
    Category.comp_id]
  exact Category.id_comp _

end AlgebraicGeometry.ProEtale

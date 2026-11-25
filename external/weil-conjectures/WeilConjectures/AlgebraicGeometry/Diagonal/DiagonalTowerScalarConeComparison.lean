/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalTowerLimitInterface
public import WeilConjectures.AlgebraicGeometry.Diagonal.DiagonalScalarCone

/-! # The explicit scalar-cone map from a strict quotient limit

Source: Stacks 099M and 0941; diagonal tower limit proof paragraph (3).
(blueprint: def-sfb-diagonal-tower-scalar-cone-comparison).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
universe a b va vb w
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.ProEtale

variable {A : Type a} [Category.{va} A] [Abelian A]
  {B : Type b} [Category.{vb} B] [Abelian B] [HasLimitsOfShape ℕᵒᵖ B]
  [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} (ℕᵒᵖ ⥤ B)]
  {ℓ : ℕ} {S : A ⥤ B} (O : DiagonalReductionPresentation ℓ S) (L : DiagonalRlim B)
  (n : ℕ)

omit [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] in
/-- Cokernel projections make the target strictly annihilated by the prime power.
Source: cokernel universal property (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
theorem diagonalQuotient_annihilated (M : A) :
    ℓ ^ (n + 1) • 𝟙 ((O.E.obj M).obj (op n)) = 0 := by
  have : Epi ((O.π n).app M) := Cofork.IsColimit.epi (O.quotient n M)
  change ℓ ^ (n + 1) • 𝟙 ((O.E ⋙ (evaluation ℕᵒᵖ B).obj (op n)).obj M) = 0
  apply (cancel_epi ((O.π n).app M)).1
  calc
    _ = ℓ ^ (n + 1) • (O.π n).app M := by
      simpa only [Category.comp_id] using
        (Preadditive.comp_nsmul ((O.π n).app M) (𝟙 _) (ℓ ^ (n + 1)))
    _ = 0 := by
      simpa only [Preadditive.nsmul_comp, Category.id_comp] using O.zero n M
    _ = _ := comp_zero.symm

/-- Exact evaluation of the ordinary quotient complex.
Source: Stacks 099M (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
abbrev diagonalQuotientLevelComplex : CochainComplex A ℤ ⥤ CochainComplex B ℤ :=
  O.E.mapHomologicalComplex (.up ℤ) ⋙
    ((evaluation ℕᵒᵖ B).obj (op n)).mapHomologicalComplex (.up ℤ)

omit [HasLimitsOfShape ℕᵒᵖ B] [HasDerivedCategory B]
  [HasDerivedCategory (ℕᵒᵖ ⥤ B)] in
/-- The strict quotient complex is annihilated degreewise.
Source: Stacks 099M (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
theorem diagonalQuotientLevel_annihilated (P : CochainComplex A ℤ) :
    ℓ ^ (n + 1) • 𝟙 ((diagonalQuotientLevelComplex O n).obj P) = 0 := by
  ext i
  exact diagonalQuotient_annihilated O n (P.X i)

/-- The identity as a map out of a strictly annihilated complex.
Source: Stacks 099M (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
def diagonalQuotientLevelSequence (P : CochainComplex A ℤ) : ShortComplex (CochainComplex B ℤ) :=
  ShortComplex.mk (ℓ ^ (n + 1) • 𝟙 ((diagonalQuotientLevelComplex O n).obj P)) (𝟙 _)
    (by rw [diagonalQuotientLevel_annihilated, zero_comp])

/-- Projection from the scalar cone of the strict finite quotient to that quotient.
Source: Stacks 099M (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
def diagonalQuotientLevelConeProjection :
    diagonalQuotientLevelComplex O n ⋙ diagonalScalarConeComplex B (ℓ ^ (n + 1)) ⟶
      diagonalQuotientLevelComplex O n where
  app P := CochainComplex.mappingCone.descShortComplex (diagonalQuotientLevelSequence O n P)
  naturality P Q f := by
    let g := (diagonalQuotientLevelComplex O n).map f
    let t : diagonalQuotientLevelSequence O n P ⟶ diagonalQuotientLevelSequence O n Q :=
      { τ₁ := g, τ₂ := g, τ₃ := g
        comm₁₂ := by
          simp only [diagonalQuotientLevelSequence, Preadditive.nsmul_comp, Preadditive.comp_nsmul,
            Category.id_comp, Category.comp_id]
        comm₂₃ := by simp only [diagonalQuotientLevelSequence, Category.id_comp, Category.comp_id] }
    exact CochainComplex.mappingCone.map_descShortComplex _ _ t

/-- Evaluation commutes with localization of the ordinary quotient complex.
Source: exact evaluation (blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
def diagonalQuotientLevelFactors :
    (O.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory ≅
      diagonalQuotientLevelComplex O n ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft (O.E.mapHomologicalComplex (.up ℤ))
    ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategoryFactors

/-- Apply the scalar cone to the actual limit projection, then project its finite
strictly annihilated target cone to its degree-zero summand. All data are explicit.
Source: Stacks 099M, the two-term scalar resolution, and 0941.
(blueprint: def-sfb-diagonal-tower-scalar-cone-comparison). -/
def diagonalTowerScalarConeComparison :
    (O.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        L.R ⋙ diagonalScalarCone B (ℓ ^ (n + 1)) ⟶
      (O.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
        ((evaluation ℕᵒᵖ B).obj (op n)).mapDerivedCategory :=
  Functor.whiskerRight
      (Functor.whiskerLeft (O.E.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
        (L.projection n)) (diagonalScalarCone B (ℓ ^ (n + 1))) ≫
    (Functor.isoWhiskerRight (diagonalQuotientLevelFactors O n)
      (diagonalScalarCone B (ℓ ^ (n + 1)))).hom ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft (diagonalQuotientLevelComplex O n)
      (diagonalScalarConeFactors B (ℓ ^ (n + 1))).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (diagonalQuotientLevelConeProjection O n) DerivedCategory.Q ≫
    (diagonalQuotientLevelFactors O n).inv

/-- The explicit comparison extends precisely the supplied derived-limit projection.
Source: Stacks 099M, adjunction unit formula.
(blueprint: def-sfb-diagonal-tower-scalar-cone-comparison).
Proof: naturality of the scalar-cone unit moves the limit projection and evaluation
comparison before the unit. On a strict complex the unit is the cone inclusion,
whose composite with the degree-zero cone projection is the identity. Cancel the
exact evaluation comparison. -/
theorem diagonalTowerScalarConeComparison_unit (P : CochainComplex A ℤ) :
    (diagonalScalarConeUnit B (ℓ ^ (n + 1))).app
        (L.R.obj (DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P))) ≫
      (diagonalTowerScalarConeComparison O L n).app P =
        (L.projection n).app
          (DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P)) := by
  let η := diagonalScalarConeUnit B (ℓ ^ (n + 1))
  let C := diagonalScalarCone B (ℓ ^ (n + 1))
  let X := DerivedCategory.Q.obj ((O.E.mapHomologicalComplex (.up ℤ)).obj P)
  let p := (L.projection n).app X
  let e := (diagonalQuotientLevelFactors O n).app P
  change η.app (L.R.obj X) ≫ _ = p
  dsimp only [diagonalTowerScalarConeComparison, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom,
    Functor.associator_hom_app, Functor.associator_inv_app]
  simp only [Category.id_comp]
  change η.app (L.R.obj X) ≫
    (C.map p ≫ C.map e.hom ≫ (diagonalScalarConeFactors B (ℓ ^ (n + 1))).hom.app
      ((diagonalQuotientLevelComplex O n).obj P) ≫
      DerivedCategory.Q.map ((diagonalQuotientLevelConeProjection O n).app P) ≫ e.inv) = p
  let Z := (diagonalQuotientLevelComplex O n).obj P
  let s := (diagonalScalarConeFactors B (ℓ ^ (n + 1))).hom.app Z
  let q := DerivedCategory.Q.map ((diagonalQuotientLevelConeProjection O n).app P)
  dsimp only [Functor.comp_obj] at e
  have ht := η.naturality (p ≫ e.hom)
  simp only [Functor.id_map] at ht
  have hc : CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 Z) ≫
      (diagonalQuotientLevelConeProjection O n).app P = 𝟙 Z :=
    CochainComplex.mappingCone.inr_descShortComplex (diagonalQuotientLevelSequence O n P)
  calc
    _ = (η.app (L.R.obj X) ≫ C.map (p ≫ e.hom)) ≫ s ≫ q ≫ e.inv := by
      rw [Functor.map_comp]
      simp only [s, q, Z, Category.assoc]
    _ = ((p ≫ e.hom) ≫ η.app (DerivedCategory.Q.obj Z)) ≫ s ≫ q ≫ e.inv := by
      simpa only [Functor.comp_obj, Z] using
        congrArg (fun f ↦ f ≫ s ≫ q ≫ e.inv) ht.symm
    _ = (p ≫ e.hom) ≫ DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 Z)) ≫ q ≫ e.inv := by
      dsimp only [s, Z]
      simp only [Category.assoc]
      rw [← Category.assoc (η.app _) _ _, diagonalScalarConeUnit_factors]
    _ = (p ≫ e.hom) ≫ (DerivedCategory.Q.map
        (CochainComplex.mappingCone.inr (ℓ ^ (n + 1) • 𝟙 Z)) ≫ q) ≫ e.inv := by
      simp only [Category.assoc]
    _ = (p ≫ e.hom) ≫ (𝟙 (DerivedCategory.Q.obj Z)) ≫ e.inv := by
      congr 2
      dsimp only [q]
      change DerivedCategory.Q.map _ ≫ DerivedCategory.Q.map _ = _
      rw [← DerivedCategory.Q.map_comp, hc]
      exact DerivedCategory.Q.map_id Z
    _ = p := by
      have hi : (𝟙 (DerivedCategory.Q.obj Z)) ≫ e.inv = e.inv :=
        Category.id_comp e.inv
      rw [hi]
      exact (Category.assoc p e.hom e.inv).trans
        ((congrArg (fun f ↦ p ≫ f) e.hom_inv_id).trans (Category.comp_id p))

end AlgebraicGeometry.ProEtale

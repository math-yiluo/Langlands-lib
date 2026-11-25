/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.Algebra.Homology.DerivedCategory.AdicTower

/-! # Localization of the explicit linear scalar cone

Source: Stacks, Tags 014A and 06YS, principal two-term complex.
(blueprint: def-coef-linear-scalar-cone).
-/

@[expose] public noncomputable section
set_option autoImplicit false
universe v u w r
open CategoryTheory CategoryTheory.Limits

namespace CochainComplex.LinearScalarCone

variable {R : Type r} [Ring R] {A : Type u} [Category.{v} A] [Abelian A] [Linear R A]
  [HasDerivedCategory.{w} A] (s : R)

/-- The actual diagonal cone functor, without any choice of resolutions.
Source: Stacks 014A (blueprint: def-coef-linear-scalar-cone). -/
abbrev cochain : CochainComplex A ℤ ⥤ CochainComplex A ℤ :=
  CochainComplex.smulArrow s ⋙ CochainComplex.ConeCoimage.cone

/-- Cone formation inverts quasi-isomorphisms. The two unchanged vertices of its
mapping-cone triangle give the assertion by the two-isomorphisms property.
Source: Stacks 014A (blueprint: def-coef-linear-scalar-cone). -/
theorem inverts : (HomologicalComplex.quasiIso A (.up ℤ)).IsInvertedBy
    (cochain (A := A) s ⋙ DerivedCategory.Q) := by
  intro P P' f hf
  have : QuasiIso f := hf
  let q := HomotopyCategory.quotient A (.up ℤ)
  let m := (DerivedCategory.Qh (C := A)).mapTriangle.map
    (q.mapTriangle.map (CochainComplex.mappingCone.triangleMap
      (s • 𝟙 P) (s • 𝟙 P') f f (by simp)))
  have hi : IsIso (DerivedCategory.Qh.map (q.map f)) :=
    Localization.inverts DerivedCategory.Qh _ _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff f).2 hf)
  have hm : IsIso m.hom₃ := CategoryTheory.Pretriangulated.isIso₃_of_isIso₁₂ m
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished (s • 𝟙 P)))
    (DerivedCategory.Qh.map_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished (s • 𝟙 P'))) hi hi
  exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso A) _).1 hm

/-- The explicit augmentation from a scalar cone in a normalized tower.
Source: Stacks 0941 (blueprint: def-coef-linear-scalar-cone). -/
def augmentation {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (hT : CochainComplex.IsNormalizedAdicTower ϖ T) (n : ℕ) (m : ℕᵒᵖ) :
    (cochain (ϖ ^ n)).obj (T.obj ((CategoryTheory.Pretriangulated.addOpFunctor n).obj m)) ⟶
      T.obj (Opposite.op n) :=
  CochainComplex.ConeCoimage.ρ.app
      ((CochainComplex.IsNormalizedAdicTower.arrowTower (ϖ := ϖ) (T := T) n).obj m) ≫
    CochainComplex.ConeCoimage.desc.app _ ≫ hT.cokerDesc n m

/-- The universal localization of the explicit cone, on every derived morphism.
Source: Stacks 05SU (blueprint: def-coef-linear-scalar-cone). -/
@[irreducible]
def derived : DerivedCategory A ⥤ DerivedCategory A :=
  Localization.lift (cochain (A := A) s ⋙ DerivedCategory.Q) (inverts s) DerivedCategory.Q

/-- Its canonical representative comparison, fixed by localization's universal property.
Source: Stacks 05SU (blueprint: def-coef-linear-scalar-cone). -/
def comparison : DerivedCategory.Q ⋙ derived (A := A) s ≅
    cochain s ⋙ DerivedCategory.Q := by
  unfold derived
  exact Localization.fac (cochain (A := A) s ⋙ DerivedCategory.Q) (inverts s) DerivedCategory.Q

/-- The localized augmented projection at one strict tower term.
Source: Stacks 0941 (blueprint: def-coef-linear-scalar-cone). -/
def derivedAugmentation {ϖ : R} {T : ℕᵒᵖ ⥤ CochainComplex A ℤ}
    (hT : CochainComplex.IsNormalizedAdicTower ϖ T) (n : ℕ) (m : ℕᵒᵖ) :
    (derived (ϖ ^ n)).obj
        (DerivedCategory.Q.obj
          (T.obj ((CategoryTheory.Pretriangulated.addOpFunctor n).obj m))) ⟶
      DerivedCategory.Q.obj (T.obj (Opposite.op n)) :=
  (comparison (ϖ ^ n)).hom.app _ ≫ DerivedCategory.Q.map (augmentation hT n m)

end CochainComplex.LinearScalarCone

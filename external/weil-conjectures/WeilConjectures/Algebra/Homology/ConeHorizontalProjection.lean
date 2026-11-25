/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.Algebra.Homology.TotalComplex
public import WeilConjectures.Mathlib.Algebra.Homology.ComplexShapeSigns
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone
public import Mathlib.Algebra.Homology.HomotopyCategory.Shift

/-! # Explicit projections onto a horizontal column

Source: Stacks Project, Homology, Tag 012X, the first filtration.
-/

@[expose] public section

universe v u
open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject
namespace HomologicalComplex₂
variable {C : Type u} [Category.{v} C] [Abelian C]
variable [∀ L : HomologicalComplex₂ C (ComplexShape.up ℕ)
  (ComplexShape.up ℕ), L.HasTotal (ComplexShape.up ℕ)]

/-- Projection from a total degree onto its column `p`, before extension by zero.
It selects that column in the coproduct and is zero on the other columns.
Source: Stacks Project, Tag 012X, first-filtration summands.
(blueprint: def-sp-cone-horizontal-projection) -/
noncomputable def horizontalTotalProjection
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p m : ℕ) : (K.total (ComplexShape.up ℕ)).X m ⟶ (K.X p).X (m - p) :=
  K.totalDesc (fun i j hij ↦ if hi : i = p then
    (K.XXIsoOfEq _ _ _ hi (by
      change i + j = m at hij
      omega)).hom else 0)

/-- Projection from the integer-extended total object onto an extended column.
When `m < p` the column object is zero and the projection is the zero map.
Source: Stacks Project, Tag 012X, first-filtration summands extended by zero.
(blueprint: def-sp-cone-horizontal-projection) -/
noncomputable def horizontalExtendedProjection
    (K : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ))
    (p : ℕ) (m : ℤ) :
    ((K.total (ComplexShape.up ℕ)).extend ComplexShape.embeddingUpNat).X m ⟶
      ((K.X p).extend ComplexShape.embeddingUpNat).X (m - (p : ℤ)) :=
  if hm : (p : ℤ) ≤ m then
    ((K.total (ComplexShape.up ℕ)).extendXIso ComplexShape.embeddingUpNat
      (Int.toNat_of_nonneg (by omega : 0 ≤ m))).hom ≫
    horizontalTotalProjection K p m.toNat ≫
    ((K.X p).extendXIso ComplexShape.embeddingUpNat
      (show ((m.toNat - p : ℕ) : ℤ) = m - (p : ℤ) by omega)).inv
  else 0

/-- The signed degreewise projection from the total-map cone to the shifted column cone.
This is a morphism of objects, not asserted to commute with the full cone differential:
the horizontal differential is killed only after restriction to the filtration tail.
The source projection is multiplied by `(-1)^p`; the target projection is unchanged.
Source: Stacks Project, Tag 012X, Lemma 12.25.1(1), and the parent node's
column-cone sign calculation.
(blueprint: def-sp-cone-horizontal-projection) -/
noncomputable def coneHorizontalProjection
    {A B : HomologicalComplex₂ C (ComplexShape.up ℕ) (ComplexShape.up ℕ)}
    (f : A ⟶ B) (p : ℕ) (n : ℤ) :
    (CochainComplex.mappingCone
      (HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
        ComplexShape.embeddingUpNat)).X n ⟶
      ((CochainComplex.mappingCone
        (HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat))⟦-(p : ℤ)⟧).X n :=
  let q := HomologicalComplex.extendMap (total.map f (ComplexShape.up ℕ))
    ComplexShape.embeddingUpNat
  let c := HomologicalComplex.extendMap (f.f p) ComplexShape.embeddingUpNat
  (HomologicalComplex.homotopyCofiber.XIsoBiprod q n (n + 1) rfl).hom ≫
    biprod.desc
      (((-1 : ℤ) ^ p) • (horizontalExtendedProjection A p (n + 1) ≫
        (((A.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
          (show n + 1 - (p : ℤ) = (n + -(p : ℤ)) + 1 by omega)).hom ≫
        HomologicalComplex.homotopyCofiber.inlX c
          ((n + -(p : ℤ)) + 1) (n + -(p : ℤ)) rfl))
      (horizontalExtendedProjection B p n ≫
        (((B.X p).extend ComplexShape.embeddingUpNat).XIsoOfEq
          (show n - (p : ℤ) = n + -(p : ℤ) by omega)).hom ≫
        (CochainComplex.mappingCone.inr c).f (n + -(p : ℤ)))

end HomologicalComplex₂

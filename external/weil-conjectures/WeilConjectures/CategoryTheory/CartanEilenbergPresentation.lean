/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.CartanEilenbergExists
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import WeilConjectures.CategoryTheory.DoubleComplexTotal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic

/-! # Presentations by injective and Cartan--Eilenberg resolutions

Source: Stacks Project, Derived Categories, Tags 015H and 015K
(blueprint: def-sp-cartan-eilenberg-presentation).
-/

@[expose] public section

universe uA vA uB vB uC vC

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory

variable {A : Type uA} [Category.{vA} A] [Abelian A]
variable {B : Type uB} [Category.{vB} B] [Abelian B]

/-- A presentation of an object by an injective resolution and a Cartan--Eilenberg
resolution of its image. The five properties are exactly the witnesses of
`exists_cartanEilenberg_resolution`, with their shared augmentation.
Source: Stacks, Tags 015H and 015K (blueprint: def-sp-cartan-eilenberg-presentation). -/
structure CartanEilenbergPresentation (F : A ⥤ B) [F.Additive] where
  X : A
  J : InjectiveResolution X
  I : HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ)
  e : ((CochainComplex.single₀ B).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      (J.cocomplex.extend ComplexShape.embeddingUpNat)) ⟶ I
  zero_neg : ∀ p : ℤ, p < 0 → IsZero (I.X p)
  column_quasiIso : ∀ p : ℤ, QuasiIso (e.f p)
  term_injective : ∀ (p : ℤ) (q : ℕ), Injective ((I.X p).X q)
  horizontal_injective : ∀ (p : ℤ) (q : ℕ),
    Injective ((I.cycles p).X q) ∧
    Injective ((image (I.d (p - 1) p)).X q) ∧ Injective ((I.homology p).X q)
  horizontal_quasiIso : ∀ p : ℤ,
    QuasiIso (HomologicalComplex.cyclesMap e p) ∧
    QuasiIso (image.map (Arrow.homMk' (e.f (p - 1)) (e.f p) (e.comm (p - 1) p))) ∧
    QuasiIso (HomologicalComplex.homologyMap e p)

namespace CartanEilenbergPresentation

variable {F : A ⥤ B} [F.Additive]

/-- A comparison consists of the original map, its injective-resolution lift and
its Cartan--Eilenberg lift, with both augmentation squares in resolution degree zero
(the form of `cartanEilenberg_doubleComplex_homotopy`).
Source: Stacks, Tag 015K (blueprint: def-sp-cartan-eilenberg-presentation). -/
structure Comparison (P Q : CartanEilenbergPresentation F) where
  f : P.X ⟶ Q.X
  β : P.J.cocomplex ⟶ Q.J.cocomplex
  comm_ι : P.J.ι.f 0 ≫ β.f 0 = f ≫ Q.J.ι.f 0
  α : P.I ⟶ Q.I
  comm_e : ∀ p : ℤ, (P.e.f p).f 0 ≫ (α.f p).f 0 =
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map
      (HomologicalComplex.extendMap β ComplexShape.embeddingUpNat)).f p ≫ (Q.e.f p).f 0

variable {C : Type uC} [Category.{vC} C] [Abelian C]

/-- Apply `G` vertically and extend the resolution degree by zero.
Source: Stacks, Tag 015K (blueprint: def-sp-cartan-eilenberg-presentation). -/
noncomputable def mappedFunctor (G : B ⥤ C) [G.Additive] :
    HomologicalComplex₂ B (ComplexShape.up ℤ) (ComplexShape.up ℕ) ⥤
      HomologicalComplex₂ C (ComplexShape.up ℤ) (ComplexShape.up ℤ) :=
  (G.mapHomologicalComplex (ComplexShape.up ℕ) ⋙
    ComplexShape.embeddingUpNat.extendFunctor C).mapHomologicalComplex (ComplexShape.up ℤ)

/-- The total complex after applying `G`, extended by zero in negative resolution degrees.
Source: Stacks, Tag 015K (blueprint: def-sp-cartan-eilenberg-presentation). -/
noncomputable def total (G : B ⥤ C) [G.Additive] [IsGrothendieckAbelian.{vC} C]
    (P : CartanEilenbergPresentation F) : CochainComplex C ℤ :=
  ((mappedFunctor G).obj P.I).total (ComplexShape.up ℤ)

end CartanEilenbergPresentation
end CategoryTheory

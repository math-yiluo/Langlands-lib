/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.HomotopyCategory.Adjunction
public import Mathlib.CategoryTheory.Adjunction.Mates
import WeilConjectures.CategoryTheory.Derived.DerivedMateUnitComparison
import WeilConjectures.CategoryTheory.InverseMateEquivalence

/-! # Cochain specialization of the normalized inverse-mate comparison

Source: Zheng Construction 4.1 and Lemma 5.16; Stacks 0FND and 09T5.
-/

@[expose] public noncomputable section
set_option autoImplicit false
open CategoryTheory CategoryTheory.Functor
namespace CategoryTheory

private theorem cochainMate_unit
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Preadditive A] [Preadditive B] [Preadditive C] [Preadditive D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (τ : R₁ ⋙ G ⟶ H ⋙ R₂)
    (P : CochainComplex A ℤ) :
    (a₂.mapHomologicalComplex (.up ℤ)).homEquiv
        ((G.mapHomologicalComplex (.up ℤ)).obj P)
        ((H.mapHomologicalComplex (.up ℤ)).obj ((L₁.mapHomologicalComplex (.up ℤ)).obj P))
        ((((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).mapHomologicalComplex
          (.up ℤ)).app P) =
      (G.mapHomologicalComplex (.up ℤ)).map ((a₁.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
        (τ.mapHomologicalComplex (.up ℤ)).app ((L₁.mapHomologicalComplex (.up ℤ)).obj P) := by
  apply HomologicalComplex.hom_ext
  intro i
  change a₂.homEquiv _ _
    (((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ)).app (P.X i)) = _
  exact (unit_mateEquiv_symm a₁ a₂ (TwoSquare.mk _ _ _ _ τ) (P.X i)).symm

/-- An ordinary right comparison between equivalences determines an inverse
comparison whose cochain localization is prescribed by the normalized derived mate.
Source: Zheng Construction 4.1 and Lemma 5.16; Stacks 0FND and 09T5.
Proof: the inverse mate of the ordinary right comparison is invertible because
both vertical functors are equivalences. Let e be its inverse. Prolong its unit
identity degreewise to cochain complexes. Apply the abstract invertible mate
comparison with the four localization functors, the supplied Hom normalizations,
the right-unit square, and the prescribed derived mate. The resulting inverse
comparison is the displayed equation for every complex. The calculation uses
no invertibility of the right-derived units and no boundedness condition.
(blueprint: lem-pur-cochain-inverse-mate-comparison). -/
theorem cochainInverseMate_comparison
    {A B C D : Type*} [Category A] [Category B] [Category C] [Category D]
    [Abelian A] [Abelian B] [Abelian C] [Abelian D]
    [HasDerivedCategory A] [HasDerivedCategory B]
    [HasDerivedCategory C] [HasDerivedCategory D]
    {L₁ : A ⥤ B} {R₁ : B ⥤ A} {L₂ : C ⥤ D} {R₂ : D ⥤ C}
    {G : A ⥤ C} {H : B ⥤ D}
    [L₁.Additive] [R₁.Additive] [L₂.Additive] [R₂.Additive] [G.Additive] [H.Additive]
    [G.IsEquivalence] [H.IsEquivalence]
    {LD₁ : DerivedCategory A ⥤ DerivedCategory B}
    {RD₁ : DerivedCategory B ⥤ DerivedCategory A}
    {LD₂ : DerivedCategory C ⥤ DerivedCategory D}
    {RD₂ : DerivedCategory D ⥤ DerivedCategory C}
    {GD : DerivedCategory A ⥤ DerivedCategory C}
    {HD : DerivedCategory B ⥤ DerivedCategory D}
    (a₁ : L₁ ⊣ R₁) (a₂ : L₂ ⊣ R₂) (ad₁ : LD₁ ⊣ RD₁) (ad₂ : LD₂ ⊣ RD₂)
    (ε₁ : DerivedCategory.Q ⋙ LD₁ ≅ L₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ε₂ : DerivedCategory.Q ⋙ LD₂ ≅ L₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ρ₁ : R₁.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RD₁)
    (ρ₂ : R₂.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q ⟶
      DerivedCategory.Q ⋙ RD₂)
    (γ : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (η : DerivedCategory.Q ⋙ HD ≅ H.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (h₁ : ∀ (P : CochainComplex A ℤ) (K : CochainComplex B ℤ)
      (f : (L₁.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad₁.homEquiv _ _ (ε₁.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₁.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          ρ₁.app K)
    (h₂ : ∀ (P : CochainComplex C ℤ) (K : CochainComplex D ℤ)
      (f : (L₂.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad₂.homEquiv _ _ (ε₂.hom.app P ≫ DerivedCategory.Q.map f) =
        DerivedCategory.Q.map ((a₂.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
          ρ₂.app K)
    (τ : R₁ ⋙ G ≅ H ⋙ R₂) (τD : RD₁ ⋙ GD ≅ HD ⋙ RD₂)
    (ιD : GD ⋙ LD₂ ≅ LD₁ ⋙ HD)
    (hτ : ∀ K : CochainComplex B ℤ,
      GD.map (ρ₁.app K) ≫ τD.hom.app (DerivedCategory.Q.obj K) ≫ RD₂.map (η.hom.app K) =
        γ.hom.app ((R₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((τ.hom.mapHomologicalComplex (.up ℤ)).app K) ≫
            ρ₂.app ((H.mapHomologicalComplex (.up ℤ)).obj K))
    (hιD : mateEquiv ad₁ ad₂ (TwoSquare.mk _ _ _ _ ιD.hom) =
      TwoSquare.mk _ _ _ _ τD.hom) :
    ∃ e : L₁ ⋙ H ≅ G ⋙ L₂, ∀ K : CochainComplex A ℤ,
      ιD.inv.app (DerivedCategory.Q.obj K) ≫ LD₂.map (γ.hom.app K) ≫
          ε₂.hom.app ((G.mapHomologicalComplex (.up ℤ)).obj K) =
        HD.map (ε₁.hom.app K) ≫ η.hom.app ((L₁.mapHomologicalComplex (.up ℤ)).obj K) ≫
          DerivedCategory.Q.map ((NatIso.mapHomologicalComplex e (.up ℤ)).hom.app K) := by
  classical
  let δ := ((mateEquiv a₁ a₂).symm (TwoSquare.mk _ _ _ _ τ.hom))
  have : IsIso δ := isIso_inverseMate_of_equivalences a₁ a₂ τ
  let e := (asIso δ).symm
  refine ⟨e, ?_⟩
  intro K
  exact derivedMate_unitComparison
    (QA := DerivedCategory.Q (C := A)) (QB := DerivedCategory.Q (C := B))
    (QC := DerivedCategory.Q (C := C)) (QD := DerivedCategory.Q (C := D))
    (G := G.mapHomologicalComplex (.up ℤ)) (H := H.mapHomologicalComplex (.up ℤ))
    (GD := GD) (HD := HD)
    (a₁.mapHomologicalComplex (.up ℤ)) (a₂.mapHomologicalComplex (.up ℤ))
    ad₁ ad₂ ε₁.hom ε₂.hom ρ₁ ρ₂ γ η h₁ h₂
    (TwoSquare.mk _ _ _ _ (τ.hom.mapHomologicalComplex (.up ℤ)))
    (TwoSquare.mk _ _ _ _ τD.hom) hτ
    (NatIso.mapHomologicalComplex e (.up ℤ))
    (fun P ↦ cochainMate_unit a₁ a₂ τ.hom P) ιD hιD K

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import Mathlib.CategoryTheory.Adjunction.Unique

/-! # Composition of normalized adjunction comparisons

Source: the mates correspondence and its horizontal composition law.
-/

@[expose] public section
set_option autoImplicit false
universe u₁ u₂ u₃ u₄ u₅ u₆ v₁ v₂ v₃ v₄ v₅ v₆
namespace CategoryTheory
open Category CategoryTheory.Functor
variable {A : Type u₁} {B : Type u₂} {C : Type u₃}
  {DA : Type u₄} {DB : Type u₅} {DC : Type u₆}
  [Category.{v₁} A] [Category.{v₂} B] [Category.{v₃} C]
  [Category.{v₄} DA] [Category.{v₅} DB] [Category.{v₆} DC]
  {F : A ⥤ B} {R : B ⥤ A} {G : B ⥤ C} {S : C ⥤ B}
  {FD : DA ⥤ DB} {RD : DB ⥤ DA} {GD : DB ⥤ DC} {SD : DC ⥤ DB}
  {QA : A ⥤ DA} {QB : B ⥤ DB} {QC : C ⥤ DC}

/-- Normalized transpose equations compose. Source: Mathlib's horizontal mates law
(blueprint: lem-pur-normalized-adjunction-composition).
Proof: transpose first through the second adjunction and then the first. Naturality
in the source moves the first comparison out of the second transpose. Naturality in
the target moves the second right comparison out of the first transpose. The two
normalization equations then give the displayed composite right comparison. -/
theorem normalizedAdjunction_composition
    (a : F ⊣ R) (b : G ⊣ S) (ad : FD ⊣ RD) (bd : GD ⊣ SD)
    (εF : QA ⋙ FD ⟶ F ⋙ QB) (εG : QB ⋙ GD ⟶ G ⋙ QC)
    (ρF : R ⋙ QA ⟶ QB ⋙ RD) (ρG : S ⋙ QB ⟶ QC ⋙ SD)
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF.app P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF.app K)
    (hG : ∀ P K (f : G.obj P ⟶ K),
      bd.homEquiv _ _ (εG.app P ≫ QC.map f) = QB.map (b.homEquiv _ _ f) ≫ ρG.app K)
    (P : A) (K : C) (f : G.obj (F.obj P) ⟶ K) :
    (ad.comp bd).homEquiv _ _
      (GD.map (εF.app P) ≫ εG.app (F.obj P) ≫ QC.map f) =
      QA.map ((a.comp b).homEquiv _ _ f) ≫
        ρF.app (S.obj K) ≫ RD.map (ρG.app K) := by
  rw [Adjunction.comp_homEquiv]
  change ad.homEquiv _ _ (bd.homEquiv _ _ _) = _
  rw [bd.homEquiv_naturality_left]
  dsimp only [comp_obj]
  rw [hG (F.obj P) K f]
  rw [← assoc, ad.homEquiv_naturality_right]
  rw [hF P (S.obj K) (b.homEquiv _ _ f), assoc, Adjunction.comp_homEquiv]
  rfl

/-- Adjoint uniqueness preserves every transpose, not just the unit.
Source: uniqueness of left adjoints (blueprint: lem-pur-normalized-adjunction-composition).
Proof: apply naturality in the target to the normalization of the uniqueness map;
the hom-equivalence unit formula identifies the result. -/
theorem leftAdjointUniq_homEquiv_comp {D : Type u₄} [Category.{v₄} D]
    {L L' : A ⥤ D} {U : D ⥤ A} (a : L ⊣ U) (b : L' ⊣ U)
    (P : A) (K : D) (f : L'.obj P ⟶ K) :
    a.homEquiv P K ((a.leftAdjointUniq b).hom.app P ≫ f) = b.homEquiv P K f := by
  rw [a.homEquiv_naturality_right, Adjunction.homEquiv_leftAdjointUniq_hom_app]
  rw [Adjunction.homEquiv_unit]

/-- Compatible right comparisons determine compatibility of the left uniqueness map.
Source: uniqueness of adjoints and the mates correspondence
(blueprint: lem-pur-normalized-adjunction-composition).
Proof: apply the transferred derived Hom bijection to both sides. Adjoint uniqueness
and the second normalization identify the first transpose. The first normalization,
the right comparison square, and the ordinary uniqueness equation identify the second.
-/
theorem normalizedAdjunction_uniqueness
    {H : A ⥤ B} {U : B ⥤ A} {HD : DA ⥤ DB} {UD : DB ⥤ DA}
    (a : F ⊣ R) (c : H ⊣ U) (ad : FD ⊣ RD) (cd : HD ⊣ UD)
    (εF : ∀ P, FD.obj (QA.obj P) ⟶ QB.obj (F.obj P))
    (εH : ∀ P, HD.obj (QA.obj P) ⟶ QB.obj (H.obj P))
    (ρF : ∀ K, QA.obj (R.obj K) ⟶ RD.obj (QB.obj K))
    (ρH : ∀ K, QA.obj (U.obj K) ⟶ UD.obj (QB.obj K))
    (hF : ∀ P K (f : F.obj P ⟶ K),
      ad.homEquiv _ _ (εF P ≫ QB.map f) = QA.map (a.homEquiv _ _ f) ≫ ρF K)
    (hH : ∀ P K (f : H.obj P ⟶ K),
      cd.homEquiv _ _ (εH P ≫ QB.map f) = QA.map (c.homEquiv _ _ f) ≫ ρH K)
    (η : R ≅ U) (δ : RD ≅ UD) (ν : ∀ P, F.obj P ⟶ H.obj P)
    (hν : ∀ P, a.homEquiv _ _ (ν P) ≫ η.hom.app (H.obj P) = c.unit.app P)
    (hρ : ∀ K, ρF K ≫ δ.hom.app (QB.obj K) = QA.map (η.hom.app K) ≫ ρH K)
    (P : A) :
    ((ad.ofNatIsoRight δ).leftAdjointUniq cd).hom.app (QA.obj P) ≫ εH P =
      εF P ≫ QB.map (ν P) := by
  apply ((ad.ofNatIsoRight δ).homEquiv _ _).injective
  rw [leftAdjointUniq_homEquiv_comp]
  rw [Adjunction.homEquiv_ofNatIsoRight_apply]
  rw [hF]
  rw [assoc, hρ, ← assoc, ← QA.map_comp, hν]
  have hh := hH P (H.obj P) (𝟙 _)
  simpa only [map_id, comp_obj, comp_id, Adjunction.homEquiv_id] using hh

/-- Transposing a composite of two adjunct maps inserts the restriction compositor.
Source: uniqueness of left adjoints
(blueprint: lem-pur-normalized-adjunction-composition).
Proof: the inverse uniqueness map transfers transposition to the composite adjunction.
Its two Hom bijections cancel the two specified adjuncts, and naturality moves the
second given arrow outside the first transpose. -/
theorem adjunctionComposition_transpose
    {L : A ⥤ C} {U : C ⥤ A} (a : F ⊣ R) (b : G ⊣ S) (c : L ⊣ U)
    (δ : S ⋙ R ≅ U) (X : A) (Y : B) (Z : C)
    (f : X ⟶ R.obj Y) (g : Y ⟶ S.obj Z) :
    c.homEquiv X Z
      ((((a.comp b).ofNatIsoRight δ).leftAdjointUniq c).inv.app X ≫
        G.map ((a.homEquiv X Y).symm f) ≫ (b.homEquiv Y Z).symm g) =
      f ≫ R.map g ≫ δ.hom.app Z := by
  rw [Adjunction.leftAdjointUniq_inv_app, leftAdjointUniq_homEquiv_comp,
    Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
  change a.homEquiv X _ (b.homEquiv _ Z _) ≫ δ.hom.app Z = _
  rw [b.homEquiv_naturality_left, Equiv.apply_symm_apply,
    a.homEquiv_naturality_right, Equiv.apply_symm_apply, Category.assoc]

end CategoryTheory

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.MapDerivedCategory
public import Mathlib.CategoryTheory.Adjunction.Mates

/-! # Pasted-unit normalization for derived mates

The normalization is separate from right-derived extensionality and the particular
composition comparison. Source: Mathlib's derived adjunction factorization equations.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe v u₁ u₂ u₃ u₄ w
open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace CategoryTheory.Functor
variable {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
  [Category.{v} C] [Category.{v} D] [Category.{v} C'] [Category.{v} D']
  [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w} D]
  [HasDerivedCategory.{w} C'] [HasDerivedCategory.{w} D']
  [HasKInjectiveResolutions C] [HasKInjectiveResolutions D]
  [HasKInjectiveResolutions C'] [HasKInjectiveResolutions D']
  (F : C ⥤ D) (K : C' ⥤ D') (G : D ⥤ D') (H : C ⥤ C')
  (P : C' ⥤ C) (Q : D' ⥤ D)
  [F.Additive] [K.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (ah : H ⊣ P) (ag : G ⊣ Q)
  (m : F ⋙ G ⟶ H ⋙ K)
  (β : F.rightDerivedFunctor ⋙ G.mapDerivedCategory ⟶
    H.mapDerivedCategory ⋙ K.rightDerivedFunctor)
  (hβ : rightDerivedFunctorCompUnit F G ≫
      whiskerLeft DerivedCategory.Qh
        (isoWhiskerLeft F.rightDerivedFunctor
          G.rightDerivedFunctorIsoMapDerivedCategory).hom ≫
      whiskerLeft DerivedCategory.Qh β =
    whiskerRight (NatTrans.mapHomotopyCategory m (.up ℤ)) DerivedCategory.Qh ≫
      rightDerivedFunctorCompUnit H K ≫
      whiskerLeft DerivedCategory.Qh
        (isoWhiskerRight H.rightDerivedFunctorIsoMapDerivedCategory
          K.rightDerivedFunctor).hom)

private lemma compUnit_app
    {A : Type u₁} {B : Type u₂} {E : Type u₃}
    [Category.{v} A] [Category.{v} B] [Category.{v} E]
    [Abelian A] [Abelian B] [Abelian E]
    [HasDerivedCategory.{w} A] [HasDerivedCategory.{w} B] [HasDerivedCategory.{w} E]
    [HasKInjectiveResolutions A] [HasKInjectiveResolutions B]
    (T : A ⥤ B) (U : B ⥤ E) [T.Additive] [U.Additive]
    (X : HomotopyCategory A (.up ℤ)) :
    (rightDerivedFunctorCompUnit T U).app X =
      U.rightDerivedFunctorUnit.app ((T.mapHomotopyCategory (.up ℤ)).obj X) ≫
        U.rightDerivedFunctor.map (T.rightDerivedFunctorUnit.app X) := by
  have hi := (mapHomotopyCategoryCompIso (Iso.refl (T ⋙ U)) (.up ℤ)).inv_hom_id_app X
  rw [mapHomotopyCategoryCompIso_refl_hom_app, Category.comp_id] at hi
  simp [rightDerivedFunctorCompUnit, hi]

private lemma homotopy_mate_app
    {C : Type u₁} {D : Type u₂} {C' : Type u₃} {D' : Type u₄}
    [Category.{v} C] [Category.{v} D] [Category.{v} C'] [Category.{v} D']
    [Abelian C] [Abelian D] [Abelian C'] [Abelian D']
    (F : C ⥤ D) (K : C' ⥤ D') (G : D ⥤ D') (H : C ⥤ C')
    (P : C' ⥤ C) (Q : D' ⥤ D)
    [F.Additive] [K.Additive] [G.Additive] [H.Additive] [P.Additive] [Q.Additive]
    (ah : H ⊣ P) (ag : G ⊣ Q) (m : F ⋙ G ⟶ H ⋙ K)
    (X : HomotopyCategory C' (.up ℤ)) :
    (NatTrans.mapHomotopyCategory
      (mateEquiv ah ag (TwoSquare.mk _ _ _ _ m)) (.up ℤ)).app X =
    (ag.mapHomotopyCategory (.up ℤ)).unit.app
        ((F.mapHomotopyCategory (.up ℤ)).obj ((P.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      (Q.mapHomotopyCategory (.up ℤ)).map
        ((NatTrans.mapHomotopyCategory m (.up ℤ)).app
          ((P.mapHomotopyCategory (.up ℤ)).obj X)) ≫
      (Q.mapHomotopyCategory (.up ℤ)).map
        ((K.mapHomotopyCategory (.up ℤ)).map
          ((ah.mapHomotopyCategory (.up ℤ)).counit.app X)) := by
  obtain ⟨M, rfl⟩ := HomotopyCategory.quotient_obj_surjective X
  erw [Adjunction.mapHomotopyCategory_unit_app_quotient,
    Adjunction.mapHomotopyCategory_counit_app_quotient]
  change (HomotopyCategory.quotient D (.up ℤ)).map _ =
    (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
      (HomotopyCategory.quotient D (.up ℤ)).map _ ≫
        (HomotopyCategory.quotient D (.up ℤ)).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  ext n
  simp only [mateEquiv_apply, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
    NatTrans.mapHomologicalComplex_app_f, Adjunction.mapHomologicalComplex_unit_app_f,
    Adjunction.mapHomologicalComplex_counit_app_f, NatTrans.comp_app, Functor.comp_obj,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.associator_inv_app, Functor.rightUnitor_inv_app, Functor.leftUnitor_hom_app,
    Category.id_comp, Functor.comp_map]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)

include hβ in
/-- An arbitrary normalized derived square has a mate whose pasted unit is the
localized ordinary mate. This calculation does not identify that mate with a specified
right-adjoint comparison; right-derived extensionality is a separate step.

Source: Mathlib/CategoryTheory/Functor/Derived/Adjunction.lean,
`derivedη_fac_app` and `derivedε_fac_app`; Stacks Project, Tag 079W.
(blueprint: lem-pc-derived-mate-pasted-unit).

Proof: Evaluate at an object X of the homotopy category of C'. Expand the pasted
P,F unit and the forward mate into the G-unit, Q-image of β at RP(X), and H-counit.
Use naturality of the derived G-unit to move the F-unit across it, then
naturality of β to move the right-derived P-unit across it. Apply hβ at the image of X under
P on the homotopy category. The exact identifications RG ≅ D(G) and RH ≅ D(H)
replace their units by the inverses of the localization factor isomorphisms.
Use derivedη_fac_app for G and derivedε_fac_app for H to replace the derived
unit and counit. Naturality of the localization factor isomorphisms and the
P,F,K,Q units gives the composite localized G-unit, Q-image of m at P(X), and H-counit,
followed by the pasted K,Q unit. This is precisely the ordinary forward mate
by the defining formula of mateEquiv. Associators and unitors cancel componentwise.
More explicitly, write p,f,k,q for the four right-derived units, and γH,γG
for the inverses of the exact localization factor isomorphisms. Put N = P(X)
in the homotopy category, transporting composite functors by their canonical
composition isomorphisms. Naturality of the derived G-unit at RF(p_X),
naturality of β at p_X, and naturality of that unit at f_N rewrite the left side
as ηG at Qh(F(N)), followed by RQ of D(G)(f_N), β at Qh(N),
RK(D(H)(p_X)), and RK of the derived H-counit at Qh(X).
The G-unit factorization rewrites this ηG as the localized ordinary G-unit,
then q at G(F(N)), then RQ(γG at F(N)). The hypothesis hβ replaces
γG;D(G)(f_N);β by the localized ordinary square followed by k at H(N)
and RK(γH at N). The H-counit factorization gives
D(H)(p_X);εH = γH inverse at N followed by the localized ordinary H-counit.
Thus γH cancels with its inverse. Finally naturality of k at the ordinary
H-counit and of q at the ordinary square and its K-image of that counit
puts q and RQ(k) last. What precedes them is the localized ordinary
G-unit, Q-image of m at P(X), and Q-image of K applied to the H-counit,
which is the ordinary forward mate. Restoring the composite-functor
isomorphisms gives precisely the right side.
The argument only uses naturality and the factorization equations; it works for
zero categories, zero squares, and identity adjunctions without cancellation of
noninvertible derived units. -/
theorem derivedMate_pastedUnit :
    rightDerivedFunctorCompUnit P F ≫ whiskerLeft DerivedCategory.Qh
      (mateEquiv ah.mapDerivedCategoryRightDerivedAdjunction
        ag.mapDerivedCategoryRightDerivedAdjunction
          (TwoSquare.mk _ _ _ _ β)) =
    whiskerRight (NatTrans.mapHomotopyCategory
      (mateEquiv ah ag (TwoSquare.mk _ _ _ _ m)) (.up ℤ))
        DerivedCategory.Qh ≫ rightDerivedFunctorCompUnit K Q := by
  -- The unit and counit equations of the exact-left-adjoint derived adjunctions.
  have hη (Y : HomotopyCategory D (.up ℤ)) :
      ag.mapDerivedCategoryRightDerivedAdjunction.unit.app (DerivedCategory.Qh.obj Y) ≫
        Q.rightDerivedFunctor.map (G.mapDerivedCategoryFactorsh.hom.app Y) =
      DerivedCategory.Qh.map ((ag.mapHomotopyCategory (.up ℤ)).unit.app Y) ≫
        Q.rightDerivedFunctorUnit.app ((G.mapHomotopyCategory (.up ℤ)).obj Y) := by
    exact (ag.mapHomotopyCategory (.up ℤ)).derivedη_fac_app
      (HomotopyCategory.quasiIso D (.up ℤ))
      G.mapDerivedCategoryFactorsh.hom Q.rightDerivedFunctorUnit Y
  have hε (Y : HomotopyCategory C' (.up ℤ)) :
      H.mapDerivedCategory.map (P.rightDerivedFunctorUnit.app Y) ≫
        ah.mapDerivedCategoryRightDerivedAdjunction.counit.app (DerivedCategory.Qh.obj Y) =
      H.mapDerivedCategoryFactorsh.hom.app ((P.mapHomotopyCategory (.up ℤ)).obj Y) ≫
        DerivedCategory.Qh.map ((ah.mapHomotopyCategory (.up ℤ)).counit.app Y) := by
    exact (ah.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
      (HomotopyCategory.quasiIso C' (.up ℤ))
      H.mapDerivedCategoryFactorsh.hom P.rightDerivedFunctorUnit Y
  -- Normalize hβ by the exact comparisons and their factorization equations.
  have hn (Y : HomotopyCategory C (.up ℤ)) :
      G.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj Y) ≫
        G.mapDerivedCategory.map (F.rightDerivedFunctorUnit.app Y) ≫
        β.app (DerivedCategory.Qh.obj Y) =
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory m (.up ℤ)).app Y) ≫
        K.rightDerivedFunctorUnit.app ((H.mapHomotopyCategory (.up ℤ)).obj Y) ≫
        K.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.inv.app Y) := by
    have hb := congr_app hβ Y
    simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app, compUnit_app,
      isoWhiskerLeft_hom, isoWhiskerRight_hom] at hb
    have gf := congr_app G.rightDerivedFunctorIsoMapDerivedCategory_hom_fac
      ((F.mapHomotopyCategory (.up ℤ)).obj Y)
    have hf := congr_app H.rightDerivedFunctorIsoMapDerivedCategory_hom_fac Y
    dsimp only [NatTrans.comp_app, whiskerLeft_app] at gf hf
    simp only [Category.assoc] at hb
    erw [G.rightDerivedFunctorIsoMapDerivedCategory.hom.naturality_assoc,
      reassoc_of% gf, ← K.rightDerivedFunctor.map_comp, hf] at hb
    exact hb
  -- Expand the two mates, then move the derived units through by naturality.
  ext X
  simp only [NatTrans.comp_app, whiskerLeft_app, whiskerRight_app]
  erw [homotopy_mate_app F K G H P Q ah ag m X]
  simp only [compUnit_app, mateEquiv_apply, NatTrans.comp_app,
    whiskerLeft_app, whiskerRight_app, associator_hom_app, associator_inv_app,
    leftUnitor_hom_app, rightUnitor_inv_app, Functor.comp_map,
    Category.id_comp, Category.assoc]
  dsimp only [TwoSquare.mk, Functor.comp_obj]
  erw [Category.comp_id]
  erw [Category.id_comp, Category.id_comp]
  erw [ag.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  dsimp only [Functor.comp_map]
  erw [← Q.rightDerivedFunctor.map_comp_assoc, β.naturality,
    Q.rightDerivedFunctor.map_comp]
  erw [ag.mapDerivedCategoryRightDerivedAdjunction.unit.naturality_assoc]
  dsimp only [Functor.comp_map]
  simp only [Category.assoc]
  erw [← Q.rightDerivedFunctor.map_comp,
    ← K.rightDerivedFunctor.map_comp, hε X, K.rightDerivedFunctor.map_comp,
    Q.rightDerivedFunctor.map_comp]
  -- The exact factor is invertible; the derived units themselves need not be.
  have hη' := congrArg (fun t => t ≫
    Q.rightDerivedFunctor.map (G.mapDerivedCategoryFactorsh.inv.app
      ((F.mapHomotopyCategory (.up ℤ)).obj ((P.mapHomotopyCategory (.up ℤ)).obj X))))
    (hη ((F.mapHomotopyCategory (.up ℤ)).obj ((P.mapHomotopyCategory (.up ℤ)).obj X)))
  simp only [Category.assoc, ← Functor.map_comp, Iso.hom_inv_id_app] at hη'
  erw [Functor.map_id, Category.comp_id] at hη'
  erw [hη']
  simp only [Category.assoc]
  erw [← Q.rightDerivedFunctor.map_comp_assoc,
    ← Q.rightDerivedFunctor.map_comp_assoc,
    Category.assoc, hn ((P.mapHomotopyCategory (.up ℤ)).obj X)]
  simp only [Functor.map_comp, Category.assoc]
  erw [← Q.rightDerivedFunctor.map_comp_assoc
    (K.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.inv.app
      ((P.mapHomotopyCategory (.up ℤ)).obj X)))
    (K.rightDerivedFunctor.map (H.mapDerivedCategoryFactorsh.hom.app
      ((P.mapHomotopyCategory (.up ℤ)).obj X))),
    ← K.rightDerivedFunctor.map_comp, Iso.inv_hom_id_app,
    K.rightDerivedFunctor.map_id, Q.rightDerivedFunctor.map_id, Category.id_comp]
  erw [← Q.rightDerivedFunctor.map_comp,
    ← K.rightDerivedFunctorUnit.naturality,
    Q.rightDerivedFunctor.map_comp]
  dsimp only [Functor.comp_map]
  erw [← Q.rightDerivedFunctorUnit.naturality_assoc,
    ← Q.rightDerivedFunctorUnit.naturality_assoc]
  rfl

end CategoryTheory.Functor

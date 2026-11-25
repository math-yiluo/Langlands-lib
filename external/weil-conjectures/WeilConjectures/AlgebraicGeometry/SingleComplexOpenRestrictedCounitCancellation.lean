/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedComposition
public import WeilConjectures.AlgebraicGeometry.SingleComplexOpenPinnedAdjunction
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounitIso
import WeilConjectures.AlgebraicGeometry.OpenPinnedCounitHomotopyRestriction

/-! # Cancelling the restricted homotopy counit comparisons

Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry

-- Keep constructed functors abstract; expose only category aliases to implicit unification.
attribute [local irreducible] singleComplexOpenPullbackIso Functor.mapHomotopyCategory
  Functor.mapDerivedCategory openPinnedHomotopyTensorRestrictionIso
attribute [local implicit_reducible] Scheme.Modules Scheme.Modules.Hom TopCat.Sheaf
  DerivedCategory HomotopyCategory

private theorem remove_mapped_identity
    {C D : Type*} [Category C] [Category D] (F : D ⥤ C) (M : D)
    {A B E H : C} (s₁ : A ⟶ B) (s₂ : B ⟶ E) (s₃ : E ⟶ H)
    {J : C} (s₄ : H ⟶ J) (s₅ : J ⟶ F.obj M) :
    s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ ≫ F.map (𝟙 M) = s₁ ≫ s₂ ≫ s₃ ≫ s₄ ≫ s₅ := by
  rw [F.map_id, Category.comp_id]

private theorem cancel_restriction_counit
    {C : Type*} [Category C] {A B D E H J K N : C}
    (k : A ≅ B) (s : A ⟶ D) (e : D ⟶ E) (b : E ⟶ H)
    (t : H ≅ J) (d : B ⟶ J) (v : E ⟶ K) (z : K ⟶ N)
    (q : H ⟶ N)
    (hc : s ≫ e ≫ b ≫ t.hom = k.hom ≫ d)
    (hn : v ≫ z = b ≫ q) :
    k.inv ≫ s ≫ e ≫ v ≫ z = d ≫ t.inv ≫ q := by
  have h := congrArg (fun a ↦ k.inv ≫ a ≫ t.inv) hc
  simp only [Category.assoc, Iso.hom_inv_id, Category.comp_id,
    Iso.inv_hom_id_assoc] at h
  simp only [hn]
  rw [reassoc_of% h]

set_option linter.unusedVariables false in
-- Preserve the existing unused F₀ and a bindings in the public statement.
/-- A separate step of the open counit factorization.
Source: Stacks Project, Tags 08FE, 08HY and 0D5S.
(blueprint: lem-pc-k3-open-restricted-counit-cancellation).

Proof: Put P = F_h(I), let v be the homotopy tensor adjunction counit at I,
 and write t for the homotopy tensor restriction isomorphism. Apply
 open_pinned_counit_homotopy_restriction to P and the restricted square. Its identity
 input contributes only an identity map, so its left side is S(Qh(P)) followed by
 rX(epsilon_f(P)), the target restriction factorization at the homotopy pullback of
 P, and Qh(t.hom(P)). Its right side is Lf0 of the source restriction factorization
 followed by epsilon_f0(rY_h(P)). Precompose both sides with Lf0 of the inverse
 source restriction factorization, and postcompose both sides with Qh(t.inv(P)).
 Functoriality and the inverse identities cancel the source factorization and the
 pair t.hom, t.inv. Next postcompose with Qh(rX_h(v)). Naturality of the target
 restriction factorization at v identifies its composite with this arrow with
 rX(Qh(v)) followed by the restriction factorization at I. Finally combine the two
 Qh images on the right by functoriality. This gives precisely the asserted
 equality. No derived unit or derived-adjunction counit occurs. All cancellations
 are of isomorphisms, so empty opens and zero complexes require no exceptions. -/
theorem singleComplexOpen_restricted_counit_cancellation
    [∀ Y : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    {X Y : Scheme.{u}} (f : X ⟶ Y) (V : Y.Opens)
    (I : HomotopyCategory (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ)) :
    let _ : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
      @Classical.choose _ _ exists_derivedPullbackComposition
    let F := RingedSpace.moduleDirectImage f.toLRSHom.toShHom
    let F₀ := RingedSpace.moduleDirectImage (f ∣_ V).toLRSHom.toShHom
    let rY := schemeOpenRestriction Y V
    let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
    let a := @singleComplexOpenPinnedAdjunction.{u, w} _
    let c := @singleComplexOpenPinnedComposition.{u, w} _
    let ε := @Classical.choose _ _
      (Classical.choose_spec exists_derivedPullbackComposition)
    (derivedPullback (f ∣_ V)).map
      (rY.mapDerivedCategoryFactorsh.inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      ((derivedPullback (f ∣_ V)).mapIso
          ((singleComplexOpenPullbackIso Y V).symm.app
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I))) ≪≫
        (c (f ∣_ V) V.ι).app (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        eqToIso (congrArg
          (fun k ↦ (derivedPullback k).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))
          (morphismRestrict_ι f V)) ≪≫
        (c (f ⁻¹ᵁ V).ι f).symm.app
          (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≪≫
        (singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).app
          ((derivedPullback f).obj
            (DerivedCategory.Qh.obj ((F.mapHomotopyCategory (.up ℤ)).obj I)))).hom ≫
      rX.mapDerivedCategory.map ((ε f).app ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map
        (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
          |>.mapHomotopyCategory (.up ℤ)).counit.app I)) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I =
    (ε (f ∣_ V)).app ((rY.mapHomotopyCategory (.up ℤ)).obj
      ((F.mapHomotopyCategory (.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map
        ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
            (morphismRestrict_ι f V)).inv.app ((F.mapHomotopyCategory (.up ℤ)).obj I) ≫
          (rX.mapHomotopyCategory (.up ℤ)).map
            (((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
              |>.mapHomotopyCategory (.up ℤ)).counit.app I)) := by
  classical
  let : ∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  have h := open_pinned_counit_homotopy_restriction.{u, w} f V (f ⁻¹ᵁ V)
    (f ∣_ V) (morphismRestrict_ι f V)
    ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory (.up ℤ) |>.obj I)
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at h
  let rX := schemeOpenRestriction X (f ⁻¹ᵁ V)
  let rY := schemeOpenRestriction Y V
  let P := ((RingedSpace.moduleDirectImage f.toLRSHom.toShHom).mapHomotopyCategory
    (.up ℤ)).obj I
  let v := ((Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction f))
    |>.mapHomotopyCategory (.up ℤ)).counit.app I
  have hn := rX.mapDerivedCategoryFactorsh.hom.naturality v
  dsimp only [Functor.comp_map] at hn
  have h' := cancel_restriction_counit
    ((derivedPullback (f ∣_ V)).mapIso (rY.mapDerivedCategoryFactorsh.app P))
    (singleComplexRestrictedCoefficient f (DerivedCategory.Qh.obj P)
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P)) (𝟙 _) V (f ⁻¹ᵁ V)
      (f ∣_ V) (morphismRestrict_ι f V))
    _ _ (DerivedCategory.Qh.mapIso
      ((openPinnedHomotopyTensorRestrictionIso f V (f ⁻¹ᵁ V) (f ∣_ V)
        (morphismRestrict_ι f V)).app P)) _ _ _ _ h hn
  clear h hn
  have hs := remove_mapped_identity rX.mapDerivedCategory
    ((derivedPullback f).obj (DerivedCategory.Qh.obj P))
    ((derivedPullback (f ∣_ V)).map
      ((singleComplexOpenPullbackIso Y V).inv.app (DerivedCategory.Qh.obj P)))
    ((singleComplexOpenPinnedComposition (f ∣_ V) V.ι).hom.app (DerivedCategory.Qh.obj P))
    (eqToHom (congrArg
      (fun k ↦ (derivedPullback k).obj (DerivedCategory.Qh.obj P)) (morphismRestrict_ι f V)))
    ((singleComplexOpenPinnedComposition (f ⁻¹ᵁ V).ι f).inv.app (DerivedCategory.Qh.obj P))
    ((singleComplexOpenPullbackIso X (f ⁻¹ᵁ V)).hom.app
      ((derivedPullback f).obj (DerivedCategory.Qh.obj P)))
  have he := congrArg (fun s ↦
    ((derivedPullback (f ∣_ V)).mapIso (rY.mapDerivedCategoryFactorsh.app P)).inv ≫ s ≫
      rX.mapDerivedCategory.map ((pinnedPullbackCounit f).app P) ≫
      rX.mapDerivedCategory.map (DerivedCategory.Qh.map v) ≫
      rX.mapDerivedCategoryFactorsh.hom.app I) hs
  have hmain := he.symm.trans h'
  simpa only [Functor.id_obj, singleComplexOpenPinnedComposition,
    pinnedPullbackCounit, Functor.mapIso_hom, Functor.mapIso_inv, Iso.trans_hom,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, eqToIso.hom,
    Category.assoc, Functor.map_comp] using hmain

end AlgebraicGeometry

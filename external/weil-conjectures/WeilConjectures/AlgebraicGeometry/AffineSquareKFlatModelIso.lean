/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectHomTransport


public import WeilConjectures.AlgebraicGeometry.DerivedPullback
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Symmetric
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import Mathlib.Algebra.Homology.Monoidal
import WeilConjectures.AlgebraicGeometry.PerfectHomTransportExtension
import WeilConjectures.AlgebraicGeometry.AffineDerivedPullbackTensorTilde
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
import Mathlib.CategoryTheory.Localization.Equivalence
import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived

/-! # Object comparison in one affine square
Source: Stacks Project, Tags 08DW and 0D5S.
(blueprint: lem-pc-affine-square-kflat-model-iso). -/

@[expose] public section
universe u w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

set_option backward.isDefEq.respectTransparency false in
private noncomputable def moduleIsoEquivalence {X Y : Scheme.{u}} (s : X ≅ Y) :
    SheafOfModules.{u} (moduleRings X.toRingedSpace) ≌
      SheafOfModules.{u} (moduleRings Y.toRingedSpace) :=
  CategoryTheory.Equivalence.mk (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
    (SheafOfModules.pushforward s.inv.toRingCatSheafHom)
    ((Scheme.Modules.pushforwardComp s.hom s.inv ≪≫
      Scheme.Modules.pushforwardCongr s.hom_inv_id ≪≫ Scheme.Modules.pushforwardId X).symm)
    (Scheme.Modules.pushforwardComp s.inv s.hom ≪≫
      Scheme.Modules.pushforwardCongr s.inv_hom_id ≪≫ Scheme.Modules.pushforwardId Y)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem inverse_iso_pullback {X Y : Scheme.{u}} (s : X ≅ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    (e : schemeDerivedCategory X ≌ schemeDerivedCategory Y)
    (he : DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings X.toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward s.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (.up ℤ)) ⋙ DerivedCategory.Q) :
    Nonempty (e.inverse ≅ derivedPullback s.hom) := by
  let e₀ := moduleIsoEquivalence s
  let F := e₀.functor
  let G := e₀.inverse
  have : F.IsEquivalence := e₀.isEquivalence_functor
  have : G.IsEquivalence := e₀.isEquivalence_inverse
  have : F.Additive := Functor.additive_of_preserves_binary_products F
  have : G.Additive := Functor.additive_of_preserves_binary_products G
  let eC := e₀.mapHomologicalComplex (.up ℤ)
  let α : (F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
      G.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eC.unitIso.symm _ ≪≫ Functor.leftUnitor _
  let β : (G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) ⋙
      F.mapDerivedCategory ≅ DerivedCategory.Q :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ F.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight eC.counitIso _ ≪≫ Functor.leftUnitor _
  let ec := Localization.equivalence DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso _ (.up ℤ))
    (F.mapHomologicalComplex _ ⋙ DerivedCategory.Q) F.mapDerivedCategory
    (G.mapHomologicalComplex _ ⋙ DerivedCategory.Q) G.mapDerivedCategory α β
  let δ : e.functor ≅ ec.functor :=
    (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
      (HomologicalComplex.quasiIso _ (.up ℤ)) (schemeDerivedCategory Y)).preimageIso
      (he ≪≫ F.mapDerivedCategoryFactors.symm)
  let δinv : e.inverse ≅ G.mapDerivedCategory := δ.isoInverseOfIsoFunctor
  obtain ⟨adj⟩ := Scheme.Modules.nonempty_tensorPullbackAdjunction s.hom
  let θ : Scheme.Modules.tensorPullback s.hom ≅ G :=
    adj.leftAdjointUniq e₀.symm.toAdjunction
  have aE : (Scheme.Modules.tensorPullback s.hom).Additive :=
    Functor.additive_of_iso θ.symm
  let θh : (Scheme.Modules.tensorPullback s.hom).mapHomotopyCategory (.up ℤ) ≅
      G.mapHomotopyCategory (.up ℤ) :=
    { hom := θ.hom.mapHomotopyCategory (.up ℤ)
      inv := θ.inv.mapHomotopyCategory (.up ℤ)
      hom_inv_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.hom_inv_id]; rfl
      inv_hom_id := by rw [← NatTrans.mapHomotopyCategory_comp, θ.inv_hom_id]; rfl }
  let γ := G.mapDerivedCategoryFactorsh ≪≫
    Functor.isoWhiskerRight θh.symm DerivedCategory.Qh
  have := Functor.isLeftDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso _ (.up ℤ)) G.mapDerivedCategory γ
  obtain ⟨I, hI, hImap, hIadd, hIlim, hIcolim, hIres,
    E, hE, hEmap, hEadd, ε, hL, htri, hK⟩ :=
      derivedPullback_spec s.hom
  have h : E = Scheme.Modules.tensorPullback s.hom :=
    CategoryTheory.Functor.ext hE (fun M N a ↦ hEmap a)
  subst E
  have : (derivedPullback s.hom).IsLeftDerivedFunctor ε
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (.up ℤ)) := hL
  exact ⟨δinv ≪≫ Functor.leftDerivedUnique (derivedPullback s.hom)
    G.mapDerivedCategory γ.hom ε (HomotopyCategory.quasiIso _ (.up ℤ))⟩

/-- A single K-flat model comparison across a commuting square of affine coordinates.
Source: Stacks Project, Tag 08DW(2), and Tag 0D5S.
(blueprint: lem-pc-affine-square-kflat-model-iso).

Proof: the affine K-flat comparison identifies pullback of Q(tilde M) along
Spec φ with Q(tilde (φ* M)). Pushforward along a scheme isomorphism is an
exact equivalence whose inverse is its pullback. Localize this assertion and
use he and hd to identify the specified derived equivalences with these
pushforwards. Apply the composition comparison to the square equation,
cancel pullback and pushforward along t and σ, and evaluate at Q(tilde M).
Compose Lt*(P) ≅ e.inverse(P) with hP and pull the result back along Spec φ.
The resulting isomorphism d.inverse(Lp*(P)) ≅ Q(tilde(φ* M)) is inverted,
then mapped by d.functor and followed by the counit of d.
This is an object comparison only: it asserts no compatibility between choices
for different ring maps. There is no flatness assumption on φ; M is K-flat.
The argument also applies to zero rings, zero complexes and identity squares. -/
theorem nonempty_affineSquareKFlatModelIso
    (A B : CommRingCat.{u}) (Y Z : Scheme.{u})
    [∀ X : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    (t : Spec A ≅ Y) (σ : Spec B ≅ Z) (φ : A →+* B) (p : Z ⟶ Y)
    (hsquare : σ.hom ≫ p = Spec.map (CommRingCat.ofHom φ) ≫ t.hom)
    (e : schemeDerivedCategory (Spec A) ≌ schemeDerivedCategory Y)
    (d : schemeDerivedCategory (Spec B) ≌ schemeDerivedCategory Z)
    (he : (DerivedCategory.Q ⋙ e.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward t.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q))
    (hd : (DerivedCategory.Q ⋙ d.functor ≅
      (@Functor.mapHomologicalComplex ℤ
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        (SheafOfModules.{u} (moduleRings Z.toRingedSpace)) _ _ _ _
        (SheafOfModules.pushforward σ.hom.toRingCatSheafHom)
        ⟨fun _ _ ↦ rfl⟩ (ComplexShape.up ℤ)) ⋙ DerivedCategory.Q))
    (M : CochainComplex (ModuleCat.{u} A) ℤ)
    (hM : (HomologicalComplex.quasiIso (ModuleCat.{u} A) (.up ℤ)).kFlat M)
    (P : schemeDerivedCategory Y)
    (hP : e.inverse.obj P ≅ DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} A)
        (SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} A ⥤
          SheafOfModules.{u} (moduleRings (Spec A).toRingedSpace)) (tilde.functor A))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj M)) :
    Nonempty (d.functor.obj (DerivedCategory.Q.obj
      ((@Functor.mapHomologicalComplex ℤ (ModuleCat.{u} B)
        (SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace))
        _ _ _ _ (@id (ModuleCat.{u} B ⥤
          SheafOfModules.{u} (moduleRings (Spec B).toRingedSpace)) (tilde.functor B))
        ⟨fun _ _ ↦ tilde.map_zero⟩ (.up ℤ)).obj
        (((ModuleCat.extendScalars φ).mapHomologicalComplex (.up ℤ)).obj M))) ≅
      (derivedPullback p).obj P) := by
  obtain ⟨ht⟩ := inverse_iso_pullback t e he
  obtain ⟨hσ⟩ := inverse_iso_pullback σ d hd
  obtain ⟨a⟩ := derivedPullback_tilde_kFlat_natIso A B φ
  let b := (perfectHomComposition σ.hom p).app P ≪≫
    (eqToIso (congrArg (fun f ↦ derivedPullback f) hsquare)).app P ≪≫
    (perfectHomComposition (Spec.map (CommRingCat.ofHom φ)) t.hom).symm.app P
  let c := hσ.app ((derivedPullback p).obj P) ≪≫ b ≪≫
    (derivedPullback (Spec.map (CommRingCat.ofHom φ))).mapIso
      (ht.symm.app P ≪≫ hP) ≪≫ a.app ⟨M, hM⟩
  exact ⟨d.functor.mapIso c.symm ≪≫ d.counitIso.app ((derivedPullback p).obj P)⟩

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
public import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroSource
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroCounit
import WeilConjectures.AlgebraicGeometry.OpenPinnedSingleDegreeZeroApex
import WeilConjectures.AlgebraicGeometry.SingleComplexOpenBaseChangeCalculation
/-! # Constructed target comparison for the degree-zero open square
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-zero-target). -/
@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory Limits
noncomputable section
namespace AlgebraicGeometry
/-- Naturality of the canonical mate in its derived input, from the naturality
of the pullback composition comparisons and the adjunction Hom equivalence.
Source: Stacks Project, Tag 08HY, the canonical derived base-change construction. -/
private theorem baseChange_naturality
    [∀ Z : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (f' : X' ⟶ S')
    (g : S' ⟶ S) (g' : X' ⟶ X) (h : g' ≫ f = f' ≫ g)
    {E F : schemeDerivedCategory X} (s : E ⟶ F) :
    (derivedPullback g).map ((schemeDerivedDirectImage f).map s) ≫
        schemeDerivedBaseChangeMap f f' g g' h F =
      schemeDerivedBaseChangeMap f f' g g' h E ≫
        (schemeDerivedDirectImage f').map ((derivedPullback g').map s) :=
    set_option backward.isDefEq.respectTransparency false in
    set_option backward.isDefEq.respectTransparency.types false in
    set_option synthInstance.maxSize 2048 in
    open MonoidalCategory in by
  classical
  have : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (Scheme.Modules.tensorPullback k).Additive :=
    @Classical.choose _ _ exists_derivedPullbackComposition.{u, w}
  let ε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings B.toRingedSpace)) ⋙
        derivedPullback k ⟶
        (Scheme.Modules.tensorPullback k).mapHomotopyCategory (.up ℤ) ⋙
          DerivedCategory.Qh (C := SheafOfModules.{u} (moduleRings A.toRingedSpace)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec exists_derivedPullbackComposition)) k
  have hε : ∀ {A B : Scheme.{u}} (k : A ⟶ B),
      (derivedPullback k).IsLeftDerivedFunctor (ε k)
        (HomotopyCategory.quasiIso
          (SheafOfModules.{u} (moduleRings B.toRingedSpace)) (.up ℤ)) :=
    fun k ↦ (Classical.choose (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition))) k
  let c : ∀ {A B D : Scheme.{u}} (k : A ⟶ B) (l : B ⟶ D),
      derivedPullback l ⋙ derivedPullback k ≅ derivedPullback (k ≫ l) :=
    fun k l ↦ (Classical.choose (Classical.choose_spec (Classical.choose_spec
      (Classical.choose_spec exists_derivedPullbackComposition)))) k l
  let adj := Classical.choose (exists_schemeDerivedAdjunction f
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f) (ε f) (hε f))
  let adj' := Classical.choose (exists_schemeDerivedAdjunction f'
    (hAdd := (Classical.choose exists_derivedPullbackComposition) f') (ε f') (hε f'))
  let γ : (schemeDerivedDirectImage f ⋙ derivedPullback g) ⋙ derivedPullback f' ⟶
      derivedPullback g' :=
    (Functor.associator _ _ _).hom ≫
      Functor.whiskerLeft _ (c f' g).hom ≫
      Functor.whiskerLeft _ (eqToHom (congrArg (fun k ↦ derivedPullback k) h.symm)) ≫
      Functor.whiskerLeft _ (c g' f).inv ≫
      (Functor.associator _ _ _).inv ≫
      Functor.whiskerRight adj.counit (derivedPullback g') ≫
      (Functor.leftUnitor _).hom
  have hγ (K : schemeDerivedCategory X) :
      γ.app K = (c f' g).hom.app ((schemeDerivedDirectImage f).obj K) ≫
        eqToHom (congrArg (fun k ↦
          (derivedPullback k).obj ((schemeDerivedDirectImage f).obj K)) h.symm) ≫
        (c g' f).inv.app ((schemeDerivedDirectImage f).obj K) ≫
        (derivedPullback g').map (adj.counit.app K) := by
    simp only [γ, NatTrans.comp_app, Functor.associator_hom_app,
      Functor.associator_inv_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
      Functor.leftUnitor_hom_app, eqToHom_app, Category.id_comp]
    change _ ≫ _ ≫ _ ≫ _ ≫ 𝟙 _ = _
    simp only [Category.comp_id]
  have hbc (K : schemeDerivedCategory X) :
      schemeDerivedBaseChangeMap f f' g g' h K = adj'.homEquiv _ _ (γ.app K) := by
    rw [hγ]
    rfl
  rw [hbc E, hbc F]
  exact adj'.homEquiv_naturality_left_square
    ((schemeDerivedDirectImage f ⋙ derivedPullback g).map s)
    (γ.app F) (γ.app E) ((derivedPullback g').map s) (γ.naturality s)


private theorem combine_restriction_square
    {C : Type*} [Category C] {A B B₀ C₁ C₀ C₂ A₀ D₀ A₁ D₁ : C}
    (x : A ⟶ B) (r : B ⟶ C₁) (d₁ : B ⟶ B₀) (d₂ : C₁ ⟶ C₀)
    (a : A ⟶ A₀) (y : A₀ ⟶ D₀) (δ : D₀ ⟶ B₀) (c : B₀ ⟶ C₀)
    (t : C₀ ⟶ C₂) (z : D₀ ⟶ D₁) (c₀ : D₁ ⟶ C₂)
    (s : A₀ ⟶ A₁) (y₁ : A₁ ⟶ D₁)
    (hx : x ≫ d₁ = a ≫ y ≫ δ) (hr : r ≫ d₂ = d₁ ≫ c)
    (hc : δ ≫ c ≫ t = z ≫ c₀) (hy : y ≫ z = s ≫ y₁) :
    x ≫ r ≫ (d₂ ≫ t) = (a ≫ s) ≫ (y₁ ≫ c₀) := by
  calc
    _ = (x ≫ d₁) ≫ c ≫ t := by rw [← Category.assoc r d₂, hr]; simp [Category.assoc]
    _ = a ≫ y ≫ (δ ≫ c ≫ t) := by rw [hx]; simp [Category.assoc]
    _ = a ≫ (y ≫ z) ≫ c₀ := by rw [hc]; simp [Category.assoc]
    _ = _ := by rw [hy]; simp [Category.assoc]

set_option backward.isDefEq.respectTransparency.types false in
/-- Construct the target comparison and prove mate compatibility from two
independent ingredients: restriction of the pinned tensor counit and invariance
under an isomorphic apex.
Source: Stacks Project, Tags 08FE, 08HY, 08IB and 0D5U.
(blueprint: lem-pc-open-pinned-single-degree-zero-target).
Proof: restrict the cartesian square using isPullback_resLE and identify its apex
with the chosen pullback. Whisker the explicit direct-image restriction comparison
with the single tensor source, then apply the counit restriction isomorphism to
construct b₀. Use the bare base-change calculation on G[0]. Naturality of the
direct-image comparison moves the tensor counit through that comparison. The
counit restriction square identifies the restricted coefficient/counit composite. Naturality of
the local base-change mate moves the exact single restriction identification to
the source. Finally whisker the apex transport isomorphism and compose it with b₀.
The apex transport identity finishes the equation. -/
theorem open_pinned_single_degree_zero_target
    [∀ Y : Scheme.{u}, HasDerivedCategory.{w}
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [∀ {Y Z : Scheme.{u}} (k : Y ⟶ Z), (Scheme.Modules.tensorPullback k).Additive]
    {X S X' S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S)
    (g' : X' ⟶ X) (f' : X' ⟶ S') (sq : IsPullback g' f' f g)
    (V : S.Opens) (W : S'.Opens) (hWV : W ≤ g ⁻¹ᵁ V) :
    ∃ b : singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙
        (schemeOpenRestriction S' W).mapDerivedCategory ≅
      schemeOpenRestriction X (f ⁻¹ᵁ V) ⋙
        singleDegreeBaseChangeTarget.{u, w} (pullback.fst (f ∣_ V) (g.resLE V W hWV))
          (pullback.snd (f ∣_ V) (g.resLE V W hWV)) 0,
    ∀ G : X.Modules,
      (schemeOpenRestriction S' W).mapDerivedCategory.map
          (singleDegreeBaseChangeComposite f g g' f' sq.w 0 G) ≫ b.hom.app G =
        (openPinnedSingleDegreeZeroSourceIso f g V W hWV).hom.app G ≫
          singleDegreeBaseChangeComposite (f ∣_ V) (g.resLE V W hWV)
            (pullback.fst (f ∣_ V) (g.resLE V W hWV))
            (pullback.snd (f ∣_ V) (g.resLE V W hWV)) pullback.condition 0
            ((schemeOpenRestriction X (f ⁻¹ᵁ V)).obj G) := by
  classical
  dsimp only [Scheme.Modules, Scheme.ringCatSheaf] at *
  let U := f ⁻¹ᵁ V
  let Z := f' ⁻¹ᵁ W
  have hZ : Z ≤ g' ⁻¹ᵁ U := by
    calc
      Z ≤ f' ⁻¹ᵁ (g ⁻¹ᵁ V) := f'.preimage_mono hWV
      _ = g' ⁻¹ᵁ U := by
        dsimp [U]
        rw [← Scheme.Hom.comp_preimage, ← Scheme.Hom.comp_preimage, sq.w]
  let j := g'.resLE U Z hZ
  have hj : j ≫ U.ι = Z.ι ≫ g' := Scheme.Hom.resLE_comp_ι g' hZ
  have hsq : IsPullback j (f' ∣_ W) (f ∣_ V) (g.resLE V W hWV) := by
    have hz : Z = g' ⁻¹ᵁ U ⊓ f' ⁻¹ᵁ W := (inf_eq_right.mpr hZ).symm
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict, U, Z, j] using
      Scheme.Hom.isPullback_resLE sq hWV le_rfl hz
  obtain ⟨t, ht⟩ := open_pinned_single_degree_zero_counit_square g' U Z j hj
  let d := singleComplexOpenDirectImageIso f' W
  let b₀ : singleDegreeBaseChangeTarget.{u, w} g' f' 0 ⋙
      (schemeOpenRestriction S' W).mapDerivedCategory ≅
      schemeOpenRestriction X U ⋙ singleDegreeBaseChangeTarget.{u, w} j (f' ∣_ W) 0 :=
    Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft
        (Scheme.Modules.tensorPullback g' ⋙ DerivedCategory.singleFunctor
          (SheafOfModules.{u} (moduleRings X'.toRingedSpace)) 0) d ≪≫
      (Functor.associator _ _ _).symm ≪≫ Functor.isoWhiskerRight t _ ≪≫
      Functor.associator _ _ _
  obtain ⟨v, hv⟩ := open_pinned_single_degree_zero_apex (f ∣_ V) (g.resLE V W hWV)
    j (f' ∣_ W) (pullback.fst _ _) (pullback.snd _ _) hsq.w pullback.condition
    hsq.isoPullback hsq.isoPullback_hom_fst hsq.isoPullback_hom_snd
  refine ⟨b₀ ≪≫ Functor.isoWhiskerLeft (schemeOpenRestriction X U) v, ?_⟩
  intro G
  have hc := ht G
  have hb := singleComplexOpen_baseChange_calculation f f' g g' sq
    ((DerivedCategory.singleFunctor _ 0).obj G) V W hWV j hj hsq
  have hn := d.hom.naturality (openPinnedSingleDegreeZeroCounit g' G)
  dsimp only [Functor.comp_map] at hn
  let K := (DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) 0).obj G
  let H := (schemeOpenRestriction X U).obj G
  let K₀ := (schemeOpenRestriction X U).mapDerivedCategory.obj K
  let s := ((schemeOpenRestriction X U).mapDerivedCategorySingleFunctor 0).hom.app G
  let R := (schemeOpenRestriction S' W).mapDerivedCategory
  let RZ := (schemeOpenRestriction X' Z).mapDerivedCategory
  let L := derivedPullback j
  let Q := schemeDerivedDirectImage (f' ∣_ W)
  let δ := singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K)
    (𝟙 _) U Z j hj
  have hb' : R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) ≫
      d.hom.app ((derivedPullback g').obj K) =
        (singleComplexOpenBaseChangeSourceIso f g K V W hWV).hom ≫
          schemeDerivedBaseChangeMap (f ∣_ V) (f' ∣_ W) (g.resLE V W hWV) j hsq.w K₀ ≫
            Q.map δ := by
    dsimp only at hb
    change R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K) =
      (singleComplexOpenBaseChangeSourceIso f g K V W hWV).hom ≫
        schemeDerivedBaseChangeMap (f ∣_ V) (f' ∣_ W) (g.resLE V W hWV) j hsq.w K₀ ≫
          Q.map (singleComplexRestrictedCoefficient g' K ((derivedPullback g').obj K)
            (𝟙 _) U Z j hj) ≫ d.inv.app _ at hb
    apply (Iso.eq_comp_inv (d.app _)).mp
    with_unfolding_all
      simpa only [Category.assoc, δ, R, Q, Functor.comp_obj, Iso.app_inv] using hb
  have hc' : δ ≫ RZ.map (openPinnedSingleDegreeZeroCounit g' G) ≫ t.hom.app G =
      L.map s ≫ openPinnedSingleDegreeZeroCounit j H := hc
  have hb₀ : b₀.hom.app G = d.hom.app _ ≫ Q.map (t.hom.app G) := by
    simp only [b₀, Iso.trans_hom, Functor.isoWhiskerLeft_hom,
      Functor.isoWhiskerRight_hom, NatTrans.comp_app, Functor.whiskerLeft_app,
      Functor.whiskerRight_app, Functor.associator_hom_app, Iso.symm_hom,
      Functor.associator_inv_app, Category.id_comp, Category.comp_id]
    exact Category.id_comp _
  have hfull : R.map (singleDegreeBaseChangeComposite f g g' f' sq.w 0 G) ≫
      b₀.hom.app G =
        (openPinnedSingleDegreeZeroSourceIso f g V W hWV).hom.app G ≫
          singleDegreeBaseChangeComposite (f ∣_ V) (g.resLE V W hWV)
            j (f' ∣_ W) hsq.w 0 H := by
    have hQc : Q.map δ ≫ Q.map (RZ.map (openPinnedSingleDegreeZeroCounit g' G)) ≫
        Q.map (t.hom.app G) =
        Q.map (L.map s) ≫ Q.map (openPinnedSingleDegreeZeroCounit j H) := by
      simpa only [Functor.map_comp] using congrArg Q.map hc'
    have hy := (baseChange_naturality (f ∣_ V) (f' ∣_ W)
      (g.resLE V W hWV) j hsq.w s).symm
    have h := combine_restriction_square
      (R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K))
      (R.map ((schemeDerivedDirectImage f').map (openPinnedSingleDegreeZeroCounit g' G)))
      (d.hom.app ((derivedPullback g').obj K)) (d.hom.app _)
      (singleComplexOpenBaseChangeSourceIso f g K V W hWV).hom
      (schemeDerivedBaseChangeMap (f ∣_ V) (f' ∣_ W) (g.resLE V W hWV) j hsq.w K₀)
      (Q.map δ) (Q.map (RZ.map (openPinnedSingleDegreeZeroCounit g' G)))
      (Q.map (t.hom.app G)) (Q.map (L.map s))
      (Q.map (openPinnedSingleDegreeZeroCounit j H))
      ((derivedPullback (g.resLE V W hWV)).map
        ((schemeDerivedDirectImage (f ∣_ V)).map s))
      (schemeDerivedBaseChangeMap (f ∣_ V) (f' ∣_ W) (g.resLE V W hWV) j hsq.w
        ((DerivedCategory.singleFunctor _ 0).obj H)) hb' hn hQc hy
    conv at h =>
      rhs
      lhs
      rw [← openPinnedSingleDegreeZeroSourceIso_app f g V W hWV G]
    change R.map (schemeDerivedBaseChangeMap f f' g g' sq.w K ≫
      (schemeDerivedDirectImage f').map (openPinnedSingleDegreeZeroCounit g' G)) ≫
        b₀.hom.app G =
      (openPinnedSingleDegreeZeroSourceIso f g V W hWV).hom.app G ≫
        (schemeDerivedBaseChangeMap (f ∣_ V) (f' ∣_ W) (g.resLE V W hWV) j hsq.w
          ((DerivedCategory.singleFunctor _ 0).obj H) ≫
            Q.map (openPinnedSingleDegreeZeroCounit j H))
    rw [Functor.map_comp, hb₀]
    with_unfolding_all
      simpa only [Category.assoc, R, Q, K, U, H, singleDegreeBaseChangeSource,
        singleDegreeBaseChangeTarget, Functor.comp_obj] using h
  simpa only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app,
    Category.assoc, U, H] using
      (congrArg (fun z ↦ z ≫ v.hom.app H) hfull).trans
        (by rw [Category.assoc, hv H])
end AlgebraicGeometry

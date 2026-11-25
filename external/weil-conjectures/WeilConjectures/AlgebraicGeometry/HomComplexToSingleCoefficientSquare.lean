/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SignedSheafDualCoefficientMap

/-! # Naturality of the Hom-to-single comparison

Source: Stacks Project, Tag 0A8X, product Hom differential. -/

@[expose] public section

set_option autoImplicit false

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

private lemma homObjMap_zero_target {M N N' : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} (f : M ⟶ M) :
    SheafOfModules.homObjMap (R := R) f (0 : N ⟶ N') = 0 := by
  apply SheafOfModules.hom_ext
  ext X φ : 3
  change (PresheafOfModules.restrictOver R.obj X.unop).map f.val ≫ φ ≫
    (PresheafOfModules.restrictOver R.obj X.unop).map 0 = 0
  ext W x
  rfl

private lemma isIso_dependent {D : Type*} [Category D] {A : D} {B : ℤ → D}
    {k : ℤ} (π : ∀ q, k = q → (A ⟶ B q)) {q : ℤ} (hq : k = q)
    (hi : IsIso (π k rfl)) : IsIso (π q hq) := by
  subst q
  exact hi

set_option backward.isDefEq.respectTransparency true in
/-- Hom into a single sheaf is its signed internal dual complex.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product Hom differential.
The component formula is retained for the coefficient naturality proof.

Proof: project the degree n product to its factor p=-n. All other factors have
zero target and are zero objects. The inverse is the product lift with identity
at p=-n and zero elsewhere. The product universal property proves both inverse
identities. Transport the surviving target term along the canonical degree-zero
isomorphism of the single complex. The target differential is zero; the Hom
projection formula leaves -(-1)^n times precomposition by L.d(-(n+1),-n).
Thus the degreewise isomorphisms commute with differentials. This works for any
integer-indexed complex and any sheaf N, including zero sheaves and empty sites. -/
private theorem homComplex_to_single_components
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    let π := Classical.choose
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
    ∃ a : homComplex (R := R) L
        ((CochainComplex.singleFunctor _ 0).obj N) ≅ signedSheafDualComplex L N,
      ∀ k : ℤ, a.hom.f k =
        π L ((CochainComplex.singleFunctor _ 0).obj N) k (-k) 0 (by omega) ≫
          SheafOfModules.homObjMap (𝟙 (L.X (-k)))
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N).hom := by
  classical
  let M := (CochainComplex.singleFunctor _ 0).obj N
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  let H := ((homComplexFunctor (R := R)).obj (op L)).obj M
  let Q := fun n p : ℤ ↦ SheafOfModules.homObj (R := R) (L.X p) (M.X (p + n))
  have hc (n : ℤ) : IsLimit (Fan.mk (H.X n) (fun p : ℤ ↦ π L M n p (p + n) rfl)) :=
    Classical.choice ((Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).1 L M n)
  have hz (n p : ℤ) (h : p ≠ -n) : IsZero (Q n p) := by
    have ht : IsZero (M.X (p + n)) :=
      HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 N (p + n) (by omega)
    apply (IsZero.iff_id_eq_zero _).mpr
    change 𝟙 (SheafOfModules.homObj (L.X p) (M.X (p + n))) = 0
    rw [← SheafOfModules.homObjMap_id, ht.eq_of_tgt (𝟙 _) 0]
    exact homObjMap_zero_target _
  let v (n : ℤ) : Q n (-n) ⟶ H.X n := Fan.IsLimit.lift (hc n)
    (fun p ↦ if h : p = -n then eqToHom (congrArg (Q n) h.symm) else 0)
  have hv (n : ℤ) : v n ≫ π L M n (-n) (-n + n) rfl = 𝟙 (Q n (-n)) := by
    change Fan.IsLimit.lift (hc n) _ ≫
      (Fan.mk (H.X n) (fun p : ℤ ↦ π L M n p (p + n) rfl)).proj (-n) = _
    rw [Fan.IsLimit.fac]
    simp
  have hπ (n : ℤ) : π L M n (-n) (-n + n) rfl ≫ v n = 𝟙 (H.X n) := by
    apply Fan.IsLimit.hom_ext (hc n)
    intro p
    change (π L M n (-n) (-n + n) rfl ≫ v n) ≫ π L M n p (p + n) rfl =
      𝟙 (H.X n) ≫ π L M n p (p + n) rfl
    by_cases h : p = -n
    · subst p
      rw [Category.assoc, hv, Category.comp_id, Category.id_comp]
    · exact (hz n p h).eq_of_tgt _ _
  have hi (n : ℤ) : IsIso (π L M n (-n) 0 (by omega)) := by
    have h := (Iso.mk (π L M n (-n) (-n + n) rfl) (v n) (hπ n) (hv n)).isIso_hom
    exact isIso_dependent (fun q hq ↦ π L M n (-n) q hq) (by omega) h
  let s : M.X 0 ≅ N := HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 N
  let e (n : ℤ) : H.X n ≅ (signedSheafDualComplex L N).X n :=
    @asIso _ _ _ _ (π L M n (-n) 0 (by omega)) (hi n) ≪≫
      ((SheafOfModules.homFunctor R).obj (op (L.X (-n)))).mapIso s
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_, ?_⟩
  · intro n m hnm
    have hm : m = n + 1 := by exact hnm.symm
    subst m
    have hd := (Classical.choose_spec
      (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).2.1
        L M n (n + 1) (-(n + 1)) 0 (-1) (-n) rfl (by omega) (by omega) (by omega)
    change (π L M n (-n) 0 (by omega) ≫ SheafOfModules.homObjMap (𝟙 _) s.hom) ≫
        (signedSheafDualComplex L N).d n (n + 1) =
      H.d n (n + 1) ≫
        (π L M (n + 1) (-(n + 1)) 0 (by omega) ≫
          SheafOfModules.homObjMap (𝟙 _) s.hom)
    simp only [signedSheafDualComplex, CochainComplex.of_d]
    rw [Category.assoc, ← Category.assoc (H.d _ _) _ _, hd]
    have hzero : SheafOfModules.homObjMap (𝟙 (L.X (-(n + 1)))) (M.d (-1) 0) = 0 := by
      change SheafOfModules.homObjMap (𝟙 _) (0 : M.X (-1) ⟶ M.X 0) = 0
      exact homObjMap_zero_target _
    rw [hzero, comp_zero, zero_sub]
    simp only [Units.neg_smul, Preadditive.neg_comp, Preadditive.comp_neg,
      Linear.comp_units_smul, Linear.units_smul_comp, Category.assoc,
      SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp, Category.comp_id]
    rfl
  · intro k
    rfl


/-- Hom-to-single comparison is compatible with a coefficient morphism.
Source: Stacks Project, Tag 0A8X, product Hom construction.
(blueprint: new-g3-hom-to-single-coefficient-square).

Proof: Choose the same product projections of the Hom bifunctor for both
coefficient sheaves. In degree k the projection with source degree -k is an
isomorphism, because every other factor has zero target. Compose it with
internal Hom applied to the degree-zero single-object isomorphism. The
projection differential formula makes these components chain isomorphisms:
the target differential is zero and the source contribution is -(-1)^k
precomposition. The projection formula for a map in the second variable
says that postcomposition by the single-complex map becomes postcomposition
by g after the degree-zero identification. Hence these two chain
isomorphisms intertwine the maps in the displayed square. No freeness or
boundedness is needed, including for zero coefficient sheaves. -/
theorem homComplex_to_single_coefficient_square
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N N' : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (g : N ⟶ N') :
    let H := (homComplexFunctor (R := R)).obj (op L)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) 0
    ∃ (a : H.obj (S.obj N) ≅ signedSheafDualComplex (R := R) L N)
      (b : H.obj (S.obj N') ≅ signedSheafDualComplex (R := R) L N'),
      H.map (S.map g) ≫ b.hom = a.hom ≫ signedSheafDualCoefficientMap L g := by
  classical
  obtain ⟨a, ha⟩ := homComplex_to_single_components (R := R) L N
  obtain ⟨b, hb⟩ := homComplex_to_single_components (R := R) L N'
  refine ⟨a, b, ?_⟩
  apply HomologicalComplex.Hom.ext
  funext k
  simp only [HomologicalComplex.comp_f, ha, hb]
  let π := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))
  let S := CochainComplex.singleFunctor
    (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) 0
  have hn := (Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (C := C) (J := J) (R := R))).2.2
      L L (S.obj N) (S.obj N') (𝟙 L) (S.map g) k (-k) 0 (by omega)
  simp only [op_id, Functor.map_id, NatTrans.id_app, Category.id_comp,
    HomologicalComplex.id_f] at hn
  change _ ≫ (π L (S.obj N') k (-k) 0 (by omega) ≫ _) = _
  rw [← Category.assoc, hn, Category.assoc]
  change _ ≫ (SheafOfModules.homObjMap (𝟙 (L.X (-k))) ((S.map g).f 0) ≫
    SheafOfModules.homObjMap (𝟙 _) _) =
    (_ ≫ SheafOfModules.homObjMap (𝟙 _) _) ≫
      SheafOfModules.homObjMap (𝟙 _) g
  rw [Category.assoc, SheafOfModules.homObjMap_comp_homObjMap,
    SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp]
  congr 2

end CategoryTheory

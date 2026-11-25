/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplexProjections
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Signed dual and Hom into a single sheaf

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: lem-sc-hom-complex-to-single).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  {R : Sheaf J CommRingCat.{u}}

private lemma homObjMap_zero_source {M M' N : SheafOfModules.{u}
    ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)} :
    SheafOfModules.homObjMap (R := R) (0 : M' ⟶ M) (𝟙 N) = 0 := by
  exact (((SheafOfModules.homFunctor R).flip.obj N).map_zero (op M) (op M'))

/-- The signed dual differential squares to zero.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-signed-sheaf-dual-complex).
Proof: the two signs factor out, and precomposition reverses composition.
The remaining composite is precomposition by two successive differentials of L,
which is zero by the complex identity. -/
theorem signedSheafDual_d_comp_d
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R))
    (n : ℤ) :
    (-(n.negOnePow) • SheafOfModules.homObjMap (L.d (-(n + 1)) (-n)) (𝟙 N)) ≫
      (-((n + 1).negOnePow) •
        SheafOfModules.homObjMap (L.d (-((n + 1) + 1)) (-(n + 1))) (𝟙 N)) = 0 := by
  rw [Linear.units_smul_comp, Linear.comp_units_smul]
  simp only [SheafOfModules.homObjMap_comp_homObjMap, Category.id_comp,
    HomologicalComplex.d_comp_d, homObjMap_zero_source, smul_zero]

/-- The signed internal sheaf dual of an integer cochain complex.
It has terms Hom(L^(-n), N) and differential -(-1)^n times precomposition.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(blueprint: def-sc-signed-sheaf-dual-complex). -/
noncomputable def signedSheafDualComplex
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ :=
  CochainComplex.of (fun n ↦ SheafOfModules.homObj (L.X (-n)) N)
    (fun n ↦ -(n.negOnePow) • SheafOfModules.homObjMap (L.d (-(n + 1)) (-n)) (𝟙 N))
    (signedSheafDual_d_comp_d L N)

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
(blueprint: lem-sc-hom-complex-to-single).

Proof: project the degree n product to its factor p=-n. All other factors have
zero target and are zero objects. The inverse is the product lift with identity
at p=-n and zero elsewhere. The product universal property proves both inverse
identities. Transport the surviving target term along the canonical degree-zero
isomorphism of the single complex. The target differential is zero; the Hom
projection formula leaves -(-1)^n times precomposition by L.d(-(n+1),-n).
Thus the degreewise isomorphisms commute with differentials. This works for any
integer-indexed complex and any sheaf N, including zero sheaves and empty sites. -/
theorem homComplex_to_single_iso
    (L : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (N : SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    Nonempty (homComplex (R := R) L
      ((CochainComplex.singleFunctor _ 0).obj N) ≅ signedSheafDualComplex L N) := by
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
  refine ⟨HomologicalComplex.Hom.isoOfComponents e ?_⟩
  intro n m hnm
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

end CategoryTheory

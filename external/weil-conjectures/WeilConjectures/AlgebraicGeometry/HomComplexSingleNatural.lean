/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.HomComplexSingle
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Naturality of the single-source internal Hom comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
namespace AlgebraicGeometry

private noncomputable def soleFactorIso {B : Type u} [Category B] [HasZeroMorphisms B]
    {f : ℤ → B} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : c.pt ≅ f i where
  hom := c.proj i
  inv := hc.lift (Fan.mk (f i) (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
  hom_inv_id := by
    apply hc.hom_ext
    rintro ⟨j⟩
    rw [Category.assoc, hc.fac]
    by_cases h : j = i
    · subst j
      simp
      rfl
    · exact (hz j h).eq_of_tgt _ _
  inv_hom_id := by
    change hc.lift (Fan.mk (f i)
      (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0)) ≫
      c.π.app (Discrete.mk i) = 𝟙 (f i)
    rw [hc.fac]
    simp

private lemma soleFactorIsIso {B : Type u} [Category B] [HasZeroMorphisms B]
    {f : ℤ → B} (c : Fan f) (hc : IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → IsZero (f j)) : IsIso (c.proj i) :=
  (soleFactorIso c hc i hz).isIso_hom

private lemma natIsoOfDegreewise {C D : Type*} [Category C] [Category D]
    [HasZeroMorphisms D] (F G : C ⥤ CochainComplex D ℤ)
    (π : ∀ K n, (F.obj K).X n ⟶ (G.obj K).X n)
    (hπ : ∀ K n, IsIso (π K n))
    (hd : ∀ K n m, n + 1 = m →
      π K n ≫ (G.obj K).d n m = (F.obj K).d n m ≫ π K m)
    (hf : ∀ {K K'} (f : K ⟶ K') n,
      (F.map f).f n ≫ π K' n = π K n ≫ (G.map f).f n) : Nonempty (F ≅ G) := by
  have (K : C) (n : ℤ) : IsIso (π K n) := hπ K n
  refine ⟨NatIso.ofComponents (fun K ↦
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ asIso (π K n)) (hd K)) ?_⟩
  intro K K' f
  apply HomologicalComplex.hom_ext
  exact hf f

private lemma removeIdentityMap {C D E : Type*}
    [Category C] [Category D] [Category E] (F : Cᵒᵖ ⥤ D ⥤ E)
    (L : C) {K K' : D} (f : K ⟶ K')
    (Q : (((F.obj (op L)).obj K) ⟶ ((F.obj (op L)).obj K')) → Prop)
    (h : Q ((F.map (𝟙 L).op).app K ≫ (F.obj (op L)).map f)) :
    Q ((F.obj (op L)).map f) := by
  rw [op_id, F.map_id (op L)] at h
  simpa only [NatTrans.id_app, Category.id_comp] using h

private lemma homObj_isZero_left
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    (M N : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) (h : IsZero M) :
    IsZero (SheafOfModules.homObj M N) := by
  exact ((SheafOfModules.homFunctor R).flip.obj N).map_isZero h.op

private lemma homObjMap_zero_left
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}}
    {M M' : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)}
    (N : SheafOfModules.{u} ((sheafCompose J
      (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) :
    SheafOfModules.homObjMap (0 : M' ⟶ M) (𝟙 N) = 0 := by
  change ((SheafOfModules.homFunctor R).flip.obj N).map (0 : M' ⟶ M).op = 0
  rw [op_zero]
  exact Functor.map_zero _ _ _

-- Keep the chosen bifunctor behind its definition when elaborating projection formulas.
private lemma homComplex_spec
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
    {R : Sheaf J CommRingCat.{u}} :
    ∃ π : ∀ (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n p q : ℤ), p + n = q →
        ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n ⟶
          SheafOfModules.homObj (L.X p) (M.X q)),
        (∀ (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          (((homComplexFunctor (R := R)).obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ SheafOfModules.homObjMap (𝟙 (L.X p)) (M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫
                SheafOfModules.homObjMap (L.d p p') (𝟙 (M.X q)))) ∧
        (∀ (L L' M M' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)) ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          ((((homComplexFunctor (R := R)).map f.op).app M) ≫
            ((homComplexFunctor (R := R)).obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ SheafOfModules.homObjMap (f.f p) (g.f q)) := by
  exact (homComplex_exists.{u, u, u, u} (R := R)).choose_spec

set_option backward.isDefEq.respectTransparency true in
/-- The single-source Hom-complex projection is a natural chain isomorphism.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X, product and map formulas.
(blueprint: lem-sc-hom-complex-single-natural).

Proof: Project in degree n onto the factor with source degree zero. All other
factors are zero, so the product universal property gives an inverse. The
single complex has zero differential, so the differential formula identifies
the projection with postcomposition by the target differential. The map formula
for the Hom complex identifies the projection of each mapped chain morphism
with postcomposition by that morphism, proving naturality in every degree. -/
theorem homComplex_single_natural_iso
    (Y : Scheme.{u})
    (P : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) :
    Nonempty ((homComplexFunctor (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor Y.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ)) := by
  classical
  obtain ⟨π, hh⟩ := homComplex_spec (R := Y.sheaf)
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let Pc := (CochainComplex.singleFunctor A 0).obj P
  let T := (SheafOfModules.homFunctor.{u, u, u, u} Y.toRingedSpace.sheaf).obj (op P)
  let proj (K : CochainComplex A ℤ) (n : ℤ) := π Pc K n 0 n (zero_add n)
  have hz (K : CochainComplex A ℤ) (n p : ℤ) (hp : p ≠ 0) :
      IsZero (SheafOfModules.homObj (R := Y.sheaf) (Pc.X p) (K.X (p+n))) := by
    exact homObj_isZero_left (R := Y.sheaf) _ _
      (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P p hp)
  have hpi (K : CochainComplex A ℤ) (n q : ℤ) (hq : 0+n=q) :
      IsIso (π Pc K n 0 q hq) := by
    subst q
    have he := soleFactorIsIso _ (hh.1 Pc K n).some 0 (hz K n)
    change IsIso (π Pc K n 0 (0+n) rfl) at he
    exact he
  have hp (K : CochainComplex A ℤ) (n : ℤ) : IsIso (proj K n) :=
    hpi K n n (zero_add n)
  apply natIsoOfDegreewise _ _ proj hp
  · intro K n m hnm
    symm
    change (homComplex.{u, u, u, u} (R := Y.sheaf) Pc K).d n m ≫ proj K m =
      proj K n ≫ T.map (K.d n m)
    have hd := hh.2.1 Pc K n m 0 m n 1 hnm (zero_add m) (zero_add n)
      ((add_comm 1 n).trans hnm)
    have hzero : SheafOfModules.homObjMap (R := Y.sheaf)
        (Pc.d 0 1) (𝟙 (K.X m)) = 0 := by
      rw [show Pc.d 0 1 = 0 from rfl]
      exact homObjMap_zero_left (R := Y.sheaf) _
    with_reducible simp only [hzero, comp_zero, smul_zero, sub_zero] at hd
    exact hd
  · intro K K' f n
    change (((homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).obj (op Pc)).map f).f n ≫
      proj K' n = proj K n ≫ T.map (f.f n)
    have hn := hh.2.2 Pc Pc K K' (𝟙 Pc) f n 0 n (zero_add n)
    set_option backward.isDefEq.respectTransparency true in
      exact removeIdentityMap (C := CochainComplex A ℤ)
        (D := CochainComplex A ℤ) (E := CochainComplex A ℤ)
        (homComplexFunctor.{u, u, u, u} (R := Y.sheaf)) Pc f
        (fun k ↦ k.f n ≫ proj K' n = proj K n ≫ T.map (f.f n)) hn

end AlgebraicGeometry

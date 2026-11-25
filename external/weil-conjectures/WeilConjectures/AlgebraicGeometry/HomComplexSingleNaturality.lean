/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.AlgebraicGeometry.DerivedCategory
import WeilConjectures.Algebra.Homology.HomComplexProjections
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHomFree

/-! # Naturality of the single-source internal Hom comparison

Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
-/

@[expose] public section

universe u
open CategoryTheory Opposite
namespace AlgebraicGeometry

private noncomputable def soleFactorIso {B : Type u} [Category B]
    [CategoryTheory.Limits.HasZeroMorphisms B]
    {f : ℤ → B} (c : CategoryTheory.Limits.Fan f) (hc : CategoryTheory.Limits.IsLimit c) (i : ℤ)
    (hz : ∀ j, j ≠ i → CategoryTheory.Limits.IsZero (f j)) : c.pt ≅ f i where
  hom := c.proj i
  inv := hc.lift (CategoryTheory.Limits.Fan.mk (f i)
    (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0))
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
    change hc.lift (CategoryTheory.Limits.Fan.mk (f i)
      (fun j ↦ if h : j = i then eqToHom (congrArg f h.symm) else 0)) ≫
      c.π.app (Discrete.mk i) = 𝟙 (f i)
    rw [hc.fac]
    simp

private theorem single_hom_functor_iso (Y : Scheme.{u})
    (F : (CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ ⥤
      CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (π : ∀ (L M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (n p q : ℤ), p + n = q →
        (((F.obj (op L)).obj M).X n ⟶ SheafOfModules.homObj (R := Y.sheaf) (L.X p) (M.X q)))
    (hlim : ∀ (L M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (n : ℤ), Nonempty (CategoryTheory.Limits.IsLimit
        (CategoryTheory.Limits.Fan.mk (((F.obj (op L)).obj M).X n)
          (fun p : ℤ ↦ π L M n p (p + n) rfl))))
    (hdiff : ∀ (L M : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (n m p q q' p' : ℤ) (_hnm : n + 1 = m) (hpq : p + m = q)
      (hq' : p + n = q') (hp' : p' + n = q),
      ((F.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
        π L M n p q' hq' ≫ SheafOfModules.homObjMap (R := Y.sheaf) (𝟙 (L.X p)) (M.d q' q) -
          n.negOnePow • (π L M n p' q hp' ≫
            SheafOfModules.homObjMap (R := Y.sheaf) (L.d p p') (𝟙 (M.X q))))
    (hnat : ∀ (L L' M M' :
      CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
      (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (hpq : p + n = q),
      (((F.map f.op).app M) ≫ (F.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
        π L M n p q hpq ≫ SheafOfModules.homObjMap (R := Y.sheaf) (f.f p) (g.f q))
    (P Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (k : Q ⟶ P)
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).Additive]
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).Additive] :
    ∃ bP : F.obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ),
    ∃ bQ : F.obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj Q)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).mapHomologicalComplex (.up ℤ),
      ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      (F.map
          ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op).app I ≫ bQ.hom.app I =
        bP.hom.app I ≫
          (NatTrans.mapHomologicalComplex
            ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).map k.op) (.up ℤ)).app I := by
  classical
  let A := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let S := CochainComplex.singleFunctor A 0
  let T (P : A) := (SheafOfModules.homFunctor Y.sheaf).obj (op P)
  let proj (P : A) (K : CochainComplex A ℤ) (n : ℤ) :=
    π (S.obj P) K n 0 n (zero_add n)
  have hp (P : A) (K : CochainComplex A ℤ) (n : ℤ) : IsIso (proj P K n) := by
    have hz (p : ℤ) (hp : p ≠ 0) :
        CategoryTheory.Limits.IsZero (SheafOfModules.homObj (R := Y.sheaf)
          ((S.obj P).X p) (K.X (p + n))) := by
      exact ((SheafOfModules.homFunctor Y.sheaf).flip.obj (K.X (p + n))).map_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 P p hp).op
    have hpi (q : ℤ) (hq : 0 + n = q) : IsIso (π (S.obj P) K n 0 q hq) := by
      subst q
      let c := CategoryTheory.Limits.Fan.mk (((F.obj (op (S.obj P))).obj K).X n)
        (fun p : ℤ ↦ π (S.obj P) K n p (p + n) rfl)
      have hc : CategoryTheory.Limits.IsLimit c := (hlim (S.obj P) K n).some
      exact (soleFactorIso c hc 0 hz).isIso_hom
    exact hpi n (zero_add n)
  have hd (P : A) [(T P).Additive] (K : CochainComplex A ℤ)
      (n m : ℤ) (hnm : n + 1 = m) :
      proj P K n ≫ (T P).map (K.d n m) =
        ((F.obj (op (S.obj P))).obj K).d n m ≫
          proj P K m := by
    have h := hdiff (S.obj P) K n m 0 m n 1 hnm (zero_add m) (zero_add n)
      ((add_comm 1 n).trans hnm)
    have hz : SheafOfModules.homObjMap (R := Y.sheaf)
        ((S.obj P).d 0 1) (𝟙 (K.X m)) = 0 := by
      change ((SheafOfModules.homFunctor Y.sheaf).flip.obj (K.X m)).map
        ((S.obj P).d 0 1).op = 0
      rw [show (S.obj P).d 0 1 = 0 from rfl, CategoryTheory.Limits.op_zero]
      exact Functor.map_zero _ _ _
    simp only [hz, CategoryTheory.Limits.comp_zero, smul_zero, sub_zero] at h
    exact h.symm
  let ec (P : A) [(T P).Additive] (K : CochainComplex A ℤ) :
      (F.obj (op (S.obj P))).obj K ≅
        ((T P).mapHomologicalComplex (.up ℤ)).obj K :=
    HomologicalComplex.Hom.isoOfComponents (fun n ↦ asIso (proj P K n)) (hd P K)
  have hn (P : A) [(T P).Additive] {K L : CochainComplex A ℤ} (f : K ⟶ L) :
      (F.obj (op (S.obj P))).map f ≫ (ec P L).hom =
        (ec P K).hom ≫ ((T P).mapHomologicalComplex (.up ℤ)).map f := by
    apply HomologicalComplex.hom_ext
    intro n
    have h := hnat (S.obj P) (S.obj P) K L (𝟙 _) f n 0 n (zero_add n)
    change ((F.map (𝟙 (op (S.obj P)))).app K ≫
      (F.obj (op (S.obj P))).map f).f n ≫ proj P L n =
        proj P K n ≫ (T P).map (f.f n) at h
    rw [F.map_id] at h
    simp only [NatTrans.id_app, Category.id_comp] at h
    exact h
  let b (P : A) [(T P).Additive] := NatIso.ofComponents (ec P) (fun f ↦ hn P f)
  refine ⟨b P, b Q, ?_⟩
  intro I
  apply HomologicalComplex.hom_ext
  intro n
  have h := hnat (S.obj P) (S.obj Q) I I (S.map k) (𝟙 I) n 0 n (zero_add n)
  change ((F.map (S.map k).op).app I ≫ (F.obj (op (S.obj Q))).map (𝟙 I)).f n ≫
    proj Q I n = proj P I n ≫ SheafOfModules.homObjMap (R := Y.sheaf)
      ((S.map k).f 0) (𝟙 (I.X n)) at h
  rw [(F.obj (op (S.obj Q))).map_id] at h
  simp only [Category.comp_id] at h
  exact h

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types true in
/-- The single-source Hom comparison is natural in both the sheaf and the complex.

Source: Stacks Project, sites-cohomology.tex, Section 0A8X, Hom-complex product
and functoriality formulas. (blueprint: lem-sc-hom-complex-single-naturality)

Proof: For each sheaf P and complex I, project the product defining Hom(P[0],I)
to its degree-zero source factor. All other factors are zero, because P[0]^p
is zero for p different from zero. The inverse is the product lift with this
component and zero elsewhere. The product universal property gives both inverse
identities. The differential formula reduces to postcomposition by d_I, as the
source differential vanishes. Naturality in I follows from the postcomposition
formula for the product projections. For k:Q → P, the precomposition formula for
those same projections identifies Hom(k[0],I) with degreewise internal Hom(k,I).
These arguments apply to unbounded I, zero P or Q, and the empty scheme. -/
theorem homComplex_single_precomposition_iso (Y : Scheme.{u})
    (P Q : SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (k : Q ⟶ P)
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).Additive]
    [((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).Additive] :
    ∃ bP : (homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj P)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op P)).mapHomologicalComplex (.up ℤ),
    ∃ bQ : (homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).obj
        (op ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj Q)) ≅
      ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).obj (op Q)).mapHomologicalComplex (.up ℤ),
      ∀ I : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ,
      ((homComplexFunctor.{u, u, u, u} (R := Y.sheaf)).map
          ((CochainComplex.singleFunctor
          (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).map k).op).app I ≫ bQ.hom.app I =
        bP.hom.app I ≫
          (NatTrans.mapHomologicalComplex
            ((SheafOfModules.homFunctor.{u, u, u, u} Y.sheaf).map k.op) (.up ℤ)).app I := by
  obtain ⟨π, hlim, hdiff, hnat⟩ :=
    homComplex_projections_exists.{u, u, u, u} (R := Y.sheaf)
  exact single_hom_functor_iso Y (homComplexFunctor (R := Y.sheaf)) π hlim hdiff hnat P Q k

end AlgebraicGeometry

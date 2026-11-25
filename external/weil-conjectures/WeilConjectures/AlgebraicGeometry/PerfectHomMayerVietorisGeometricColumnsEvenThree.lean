/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.Algebra.Category.Grp.Colimits
public import WeilConjectures.AlgebraicGeometry.PerfectHomPushPullCocone
public import WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisDiagram
public import WeilConjectures.AlgebraicGeometry.PerfectHomLocalComparison
public import WeilConjectures.AlgebraicGeometry.PerfectHomTriangleRow
import Mathlib.Algebra.Category.Grp.FilteredColimits
import Mathlib.CategoryTheory.Limits.Types.Filtered
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenColimitLocalComparison

/-! # Local comparisons for the outer columns of geometric triangle diagrams

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry


set_option backward.isDefEq.respectTransparency false in
private theorem product_colimit_presentation
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (K L M : J ⥤ Type w) (dK : Cocone K) (dL : Cocone L) (dM : Cocone M)
    (hK : IsColimit dK) (hL : IsColimit dL) (hM : IsColimit dM)
    (e : ∀ j, K.obj j ≃ L.obj j × M.obj j)
    (he : ∀ (j k : J) (f : j ⟶ k) (x : K.obj j),
      e k (K.map f x) = (L.map f (e j x).1, M.map f (e j x).2)) :
    ∃ a : dK.pt ≃ dL.pt × dM.pt, ∀ j x,
      a (dK.ι.app j x) = (dL.ι.app j (e j x).1, dM.ι.app j (e j x).2) := by
  have : IsFiltered J := inferInstance
  let D : Cocone K :=
    { pt := dL.pt × dM.pt
      ι :=
        { app j := TypeCat.ofHom fun x ↦ (dL.ι.app j (e j x).1, dM.ι.app j (e j x).2)
          naturality := by
            intro j k f
            ext x
            change (dL.ι.app k (e k (K.map f x)).1,
              dM.ι.app k (e k (K.map f x)).2) = _
            rw [he]
            exact Prod.ext (ConcreteCategory.congr_hom (dL.w f) _)
              (ConcreteCategory.congr_hom (dM.w f) _) } }
  have hD : IsColimit D := Types.FilteredColimit.isColimitOf K D (by
    rintro ⟨x, y⟩
    obtain ⟨j, xj, hx⟩ := Types.jointly_surjective_of_isColimit hL x
    obtain ⟨k, yk, hy⟩ := Types.jointly_surjective_of_isColimit hM y
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    refine ⟨l, (e l).symm (L.map (homOfLE hjl) xj, M.map (homOfLE hkl) yk), ?_⟩
    change (x, y) = (dL.ι.app l (e l ((e l).symm _)).1,
      dM.ι.app l (e l ((e l).symm _)).2)
    rw [Equiv.apply_symm_apply]
    exact Prod.ext (hx.symm.trans (ConcreteCategory.congr_hom (dL.w (homOfLE hjl)) _).symm)
      (hy.symm.trans (ConcreteCategory.congr_hom (dM.w (homOfLE hkl)) _).symm)) (by
    intro j k x y hxy
    obtain ⟨l, fj, fk, hl⟩ := (Types.FilteredColimit.isColimit_eq_iff L hL).mp
      (congrArg Prod.fst hxy)
    obtain ⟨m, gj, gk, hm⟩ := (Types.FilteredColimit.isColimit_eq_iff M hM).mp
      (congrArg Prod.snd hxy)
    obtain ⟨n, hln, hmn⟩ := exists_ge_ge l m
    let a : j ⟶ n := fj ≫ homOfLE hln
    let b : k ⟶ n := fk ≫ homOfLE hln
    refine ⟨n, a, b, (e n).injective ?_⟩
    rw [he, he]
    apply Prod.ext
    · change L.map (fj ≫ homOfLE hln) (e j x).1 =
        L.map (fk ≫ homOfLE hln) (e k y).1
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        congrArg (L.map (homOfLE hln)) hl
    · have ha : a = gj ≫ homOfLE hmn := Subsingleton.elim _ _
      have hb : b = gk ≫ homOfLE hmn := Subsingleton.elim _ _
      rw [ha, hb]
      simpa only [Functor.map_comp, ConcreteCategory.comp_apply] using
        congrArg (M.map (homOfLE hmn)) hm)
  refine ⟨(hK.coconePointUniqueUpToIso hD).toEquiv, ?_⟩
  intro j x
  exact ConcreteCategory.congr_hom (hK.comp_coconePointUniqueUpToIso_hom hD j) x

set_option backward.isDefEq.respectTransparency false in
private noncomputable def shifted_biprod_hom_equiv
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    (S : C ⥤ C) [S.Additive] (P B D : C) :
    (P ⟶ S.obj (B ⊞ D)) ≃ (P ⟶ S.obj B) × (P ⟶ S.obj D) where
  toFun f := (f ≫ S.map biprod.fst, f ≫ S.map biprod.snd)
  invFun f := f.1 ≫ S.map biprod.inl + f.2 ≫ S.map biprod.inr
  left_inv f := by
    dsimp
    rw [Category.assoc, Category.assoc, ← S.map_comp, ← S.map_comp,
      ← Preadditive.comp_add, ← S.map_add, biprod.total, S.map_id, Category.comp_id]
  right_inv f := by
    apply Prod.ext <;>
      simp only [Preadditive.add_comp, Category.assoc, ← S.map_comp, biprod.inl_fst,
        biprod.inr_fst, biprod.inl_snd, biprod.inr_snd, S.map_id, S.map_zero,
        Category.comp_id, comp_zero, add_zero, zero_add]


set_option backward.isDefEq.respectTransparency false in
private theorem localMap_of_split_colimit
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens)
    (K L M : Set.Ici i ⥤ AddCommGrpCat.{max u w})
    (dK : Cocone K) (dL : Cocone L) (dM : Cocone M)
    (e : ∀ j, K.obj j ≃ L.obj j × M.obj j) (b : dK.pt ≃ dL.pt × dM.pt)
    (he : ∀ (j k : Set.Ici i) (f : j ⟶ k) (x : K.obj j),
      e k (K.map f x) = (L.map f (e j x).1, M.map f (e j x).2))
    (hb : ∀ j x, b (dK.ι.app j x) =
      (dL.ι.app j (e j x).1, dM.ι.app j (e j x).2))
    (hL : PerfectHomLocalMap R c i X s₀ U V (colimit.desc L dL))
    (hM : PerfectHomLocalMap R c i X s₀ U V (colimit.desc M dM)) :
    PerfectHomLocalMap R c i X s₀ U V (colimit.desc K dK) := by
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  have : IsFiltered (Set.Ici i) := inferInstance
  let G := forget AddCommGrpCat.{max u w}
  have : PreservesFilteredColimitsOfSize.{max u w, max u w} G := inferInstance
  have : PreservesFilteredColimitsOfSize.{u, u} G :=
    preservesFilteredColimitsOfSize_shrink G
  obtain ⟨a, ha⟩ : ∃ a : ↥(colimit K) ≃ ↥(colimit L) × ↥(colimit M),
      ∀ (j : Set.Ici i) (x : K.obj j), a ((colimit.ι K j) x) =
        ((colimit.ι L j) (e j x).1, (colimit.ι M j) (e j x).2) := by
    obtain ⟨a, ha⟩ := product_colimit_presentation (K ⋙ G) (L ⋙ G) (M ⋙ G)
      (G.mapCocone (colimit.cocone K)) (G.mapCocone (colimit.cocone L))
      (G.mapCocone (colimit.cocone M))
      (isColimitOfPreserves G (colimit.isColimit K))
      (isColimitOfPreserves G (colimit.isColimit L))
      (isColimitOfPreserves G (colimit.isColimit M)) e he
    refine ⟨a, ?_⟩
    intro j x
    exact ha j x
  have hm := PerfectHomLocalMap.equiv (PerfectHomLocalMap.prod hL hM) a b.symm
  have eqm : (fun x ↦ b.symm
      ((colimit.desc L dL) (a x).1, (colimit.desc M dM) (a x).2)) =
      (fun x : ↥(colimit K) ↦ (colimit.desc K dK) x) := by
    funext x
    obtain ⟨j, y, rfl⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves G (colimit.isColimit K)) x
    apply b.injective
    rw [Equiv.apply_symm_apply]
    change ((colimit.desc L dL) (a ((colimit.ι K j) y)).1,
      (colimit.desc M dM) (a ((colimit.ι K j) y)).2) = _
    rw [ha]
    change ((colimit.desc L dL) ((colimit.ι L j) (e j y).1),
      (colimit.desc M dM) ((colimit.ι M j) (e j y).2)) =
      b ((colimit.desc K dK) ((colimit.ι K j) y))
    simp only [← ConcreteCategory.comp_apply, colimit.ι_desc]
    exact (hb j y).symm
  convert hm using 1
  exact eqm.symm

set_option backward.isDefEq.respectTransparency false in
/-- Fixed outer-column comparison at index 3.
Source: Stacks Project, perfect.tex Tag 09RE.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-three).
-/
theorem perfect_hom_mayerVietoris_geometric_columns_even_three
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R)
    (i : I) (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [LocallyOfFinitePresentation s₀] [QuasiCompact s₀] [QuasiSeparated s₀]
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens) (hU : IsCompact (U : Set X)) (hV : IsAffineOpen V)
    (Y : Scheme.{u}) (t : Y ⟶ X) [IsOpenImmersion t]
    (ht : t.opensRange = U ⊔ V)
    (s : Y ⟶ Spec (R.obj i)) (hs : s = t ≫ s₀)
    [LocallyOfFinitePresentation s] [QuasiCompact s] [QuasiSeparated s]
    [∀ W : Y.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings Y.toRingedSpace).over W))]
    (P Q : schemeDerivedCategory Y) (hP : Y.IsPerfect P) (hQ : Y.IsPerfect Q)
    (F : Set.Ici i ⥤ schemeDerivedCategory Y) (d : Cocone F)
    (h : PerfectHomPushPullData R c s Q F d)
    (A : PerfectHomMVFamily Y (t ⁻¹ᵁ U) (t ⁻¹ᵁ V)) :
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj (3 : Fin 5))
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj (3 : Fin 5),
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app (3 : Fin 5)⟩) := by
  let HU := schemeMVDerivedRestriction Y (t ⁻¹ᵁ U) ⋙
    schemeDerivedDirectImage (t ⁻¹ᵁ U).ι
  let HV := schemeMVDerivedRestriction Y (t ⁻¹ᵁ V) ⋙
    schemeDerivedDirectImage (t ⁻¹ᵁ V).ι
  let T := (preadditiveCoyoneda.obj (Opposite.op P)).shift (0 : ℤ) ⋙
    AddCommGrpCat.uliftFunctor.{u}
  let L := F ⋙ HU ⋙ T
  let M := F ⋙ HV ⋙ T
  let dL := (HU ⋙ T).mapCocone d
  let dM := (HV ⋙ T).mapCocone d
  let K := (A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj (3 : Fin 5)
  let dK : Cocone K :=
    ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj 3,
      (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
        (A.cocone F d h.stageQCoh h.limitQCoh)).app 3⟩
  let split (E : schemeDerivedCategory Y) :
      ULift.{u} (P ⟶ ((HU.obj E) ⊞ (HV.obj E))⟦(0 : ℤ)⟧) ≃
        ULift.{u} (P ⟶ (HU.obj E)⟦(0 : ℤ)⟧) ×
          ULift.{u} (P ⟶ (HV.obj E)⟦(0 : ℤ)⟧) :=
    Equiv.ulift.trans
      ((shifted_biprod_hom_equiv (shiftFunctor _ (0 : ℤ)) P (HU.obj E) (HV.obj E)).trans
        (Equiv.prodCongr Equiv.ulift.symm Equiv.ulift.symm))
  apply localMap_of_split_colimit R c i X s₀ U V K L M dK dL dM
    (fun j ↦ split (F.obj j)) (split d.pt)
  · intro j k f x
    change split (F.obj k) (ULift.up
      (x.down ≫ (A.map (h.stageQCoh j) (h.stageQCoh k) (F.map f)).hom₂⟦(0 : ℤ)⟧')) = _
    rw [A.map_hom₂]
    apply Prod.ext <;> apply ULift.ext
    · change (x.down ≫ (biprod.map (HU.map (F.map f))
        (HV.map (F.map f)))⟦(0 : ℤ)⟧') ≫ (biprod.fst)⟦(0 : ℤ)⟧' =
        (x.down ≫ (biprod.fst)⟦(0 : ℤ)⟧') ≫ (HU.map (F.map f))⟦(0 : ℤ)⟧'
      simp only [Category.assoc, ← Functor.map_comp, biprod.map_fst]
    · change (x.down ≫ (biprod.map (HU.map (F.map f))
        (HV.map (F.map f)))⟦(0 : ℤ)⟧') ≫ (biprod.snd)⟦(0 : ℤ)⟧' =
        (x.down ≫ (biprod.snd)⟦(0 : ℤ)⟧') ≫ (HV.map (F.map f))⟦(0 : ℤ)⟧'
      simp only [Category.assoc, ← Functor.map_comp, biprod.map_snd]
  · intro j x
    change split d.pt (ULift.up
      (x.down ≫ (A.map (h.stageQCoh j) h.limitQCoh (d.ι.app j)).hom₂⟦(0 : ℤ)⟧')) = _
    rw [A.map_hom₂]
    apply Prod.ext <;> apply ULift.ext
    · change (x.down ≫ (biprod.map (HU.map (d.ι.app j))
        (HV.map (d.ι.app j)))⟦(0 : ℤ)⟧') ≫ (biprod.fst)⟦(0 : ℤ)⟧' =
        (x.down ≫ (biprod.fst)⟦(0 : ℤ)⟧') ≫ (HU.map (d.ι.app j))⟦(0 : ℤ)⟧'
      simp only [Category.assoc, ← Functor.map_comp, biprod.map_fst]
    · change (x.down ≫ (biprod.map (HU.map (d.ι.app j))
        (HV.map (d.ι.app j)))⟦(0 : ℤ)⟧') ≫ (biprod.snd)⟦(0 : ℤ)⟧' =
        (x.down ≫ (biprod.snd)⟦(0 : ℤ)⟧') ≫ (HV.map (d.ι.app j))⟦(0 : ℤ)⟧'
      simp only [Category.assoc, ← Functor.map_comp, biprod.map_snd]
  · apply PerfectHomLocalMap.basic U (Or.inl rfl)
    exact perfect_hom_open_colimit_local_comparison R c i X s₀ U hU
      Y t (by rw [ht]; exact le_sup_left) s hs P Q hP hQ F d h
  · apply PerfectHomLocalMap.basic V (Or.inr (Or.inl rfl))
    exact perfect_hom_open_colimit_local_comparison R c i X s₀ V hV.isCompact
      Y t (by rw [ht]; exact le_sup_right) s hs P Q hP hQ F d h

end AlgebraicGeometry

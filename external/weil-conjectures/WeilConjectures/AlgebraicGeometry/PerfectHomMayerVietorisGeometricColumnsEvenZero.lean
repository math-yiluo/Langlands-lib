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
import WeilConjectures.AlgebraicGeometry.PerfectHomOpenStagePresentation
import all WeilConjectures.AlgebraicGeometry.PerfectHomMayerVietorisGeometricColumnsOdd

/-! # Local comparisons for the outer columns of geometric triangle diagrams

Source: Stacks Project, Tags 09RE and 08BW.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even).
-/

@[expose] public section

universe u w
open CategoryTheory CategoryTheory.Limits Pretriangulated TopologicalSpace
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
private theorem product_colimit_bijective
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (K K₁ K₂ : J ⥤ AddCommGrpCat.{max u w})
    (p : K ⟶ K₁) (q : K ⟶ K₂)
    (hpq : ∀ j, Function.Bijective (fun x : K.obj j ↦ (p.app j x, q.app j x))) :
    Function.Bijective (fun x : ↑(colimit K) ↦
      ((colim.map p) x, (colim.map q) x)) := by
  have : CategoryTheory.IsFiltered J := inferInstance
  let G := forget AddCommGrpCat.{max u w}
  have : PreservesFilteredColimitsOfSize.{max u w, max u w} G := inferInstance
  have : PreservesFilteredColimitsOfSize.{u, u} G :=
    preservesFilteredColimitsOfSize_shrink G
  have hd := isColimitOfPreserves G (colimit.isColimit K)
  have hd₁ := isColimitOfPreserves G (colimit.isColimit K₁)
  have hd₂ := isColimitOfPreserves G (colimit.isColimit K₂)
  have hp (j : J) (x : K.obj j) :
      (colim.map p) ((colimit.ι K j) x) = (colimit.ι K₁ j) (p.app j x) :=
    ConcreteCategory.congr_hom (colimit.ι_map p j) x
  have hq (j : J) (x : K.obj j) :
      (colim.map q) ((colimit.ι K j) x) = (colimit.ι K₂ j) (q.app j x) :=
    ConcreteCategory.congr_hom (colimit.ι_map q j) x
  constructor
  · intro x y hxy
    obtain ⟨j, f, g, hf, hg⟩ := Types.FilteredColimit.jointly_surjective_of_isColimit₂ hd x y
    change (colimit.ι K j) f = x at hf
    change (colimit.ι K j) g = y at hg
    rw [← hf, ← hg] at hxy ⊢
    have h₁ := congrArg Prod.fst hxy
    have h₂ := congrArg Prod.snd hxy
    dsimp only at h₁ h₂
    rw [hp, hp] at h₁
    rw [hq, hq] at h₂
    obtain ⟨l, a, ha⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hd₁ (p.app j f) (p.app j g)).mp h₁
    obtain ⟨m, b, hb⟩ :=
      (Types.FilteredColimit.isColimit_eq_iff' hd₂ (q.app j f) (q.app j g)).mp h₂
    change K₁.map a (p.app j f) = K₁.map a (p.app j g) at ha
    change K₂.map b (q.app j f) = K₂.map b (q.app j g) at hb
    obtain ⟨n, hln, hmn⟩ := exists_ge_ge l m
    let z : j ⟶ n := a ≫ homOfLE hln
    have hz : z = b ≫ homOfLE hmn := Subsingleton.elim _ _
    have he : K.map z f = K.map z g := by
      apply (hpq n).injective
      apply Prod.ext
      · dsimp only
        have hn (v : K.obj j) : p.app n (K.map z v) = K₁.map z (p.app j v) :=
          by simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom (p.naturality z) v
        rw [hn, hn]
        dsimp [z]
        rw [K₁.map_comp]
        change K₁.map (homOfLE hln) (K₁.map a (p.app j f)) =
          K₁.map (homOfLE hln) (K₁.map a (p.app j g))
        rw [ha]
      · dsimp only
        have hn (v : K.obj j) : q.app n (K.map z v) = K₂.map z (q.app j v) :=
          by simpa only [ConcreteCategory.comp_apply] using
            ConcreteCategory.congr_hom (q.naturality z) v
        rw [hn, hn, hz, K₂.map_comp]
        change K₂.map (homOfLE hmn) (K₂.map b (q.app j f)) =
          K₂.map (homOfLE hmn) (K₂.map b (q.app j g))
        rw [hb]
    exact (ConcreteCategory.congr_hom ((colimit.cocone K).w z) f).symm.trans
      ((congrArg (colimit.ι K n) he).trans
        (ConcreteCategory.congr_hom ((colimit.cocone K).w z) g))
  · intro x
    obtain ⟨j, f, hf⟩ := Types.jointly_surjective_of_isColimit hd₁ x.1
    obtain ⟨k, g, hg⟩ := Types.jointly_surjective_of_isColimit hd₂ x.2
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
    obtain ⟨v, hv⟩ := (hpq l).surjective
      (K₁.map (homOfLE hjl) f, K₂.map (homOfLE hkl) g)
    refine ⟨(colimit.ι K l) v, ?_⟩
    apply Prod.ext
    · dsimp only
      rw [hp, show p.app l v = K₁.map (homOfLE hjl) f from congrArg Prod.fst hv]
      exact (ConcreteCategory.congr_hom ((colimit.cocone K₁).w (homOfLE hjl)) f).trans hf
    · dsimp only
      rw [hq, show q.app l v = K₂.map (homOfLE hkl) g from congrArg Prod.snd hv]
      exact (ConcreteCategory.congr_hom ((colimit.cocone K₂).w (homOfLE hkl)) g).trans hg

set_option backward.isDefEq.respectTransparency false in
private theorem localMap_of_binary_presentation
    {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (R : I ⥤ CommRingCat.{u}) (c : Cocone R) (i : I)
    (X : Scheme.{u}) (s₀ : X ⟶ Spec (R.obj i))
    [∀ Z : Scheme.{u},
      HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Z.toRingedSpace))]
    (U V : X.Opens)
    (K K₁ K₂ : Set.Ici i ⥤ AddCommGrpCat.{max u w})
    (dK : Cocone K) (d₁ : Cocone K₁) (d₂ : Cocone K₂)
    (p : K ⟶ K₁) (q : K ⟶ K₂)
    (hpq : ∀ j, Function.Bijective (fun x : K.obj j ↦ (p.app j x, q.app j x)))
    (b : dK.pt ≃ d₁.pt × d₂.pt)
    (hb : ∀ j (x : K.obj j),
      b (dK.ι.app j x) = (d₁.ι.app j (p.app j x), d₂.ι.app j (q.app j x)))
    (h₁ : PerfectHomLocalMap R c i X s₀ U V (colimit.desc K₁ d₁))
    (h₂ : PerfectHomLocalMap R c i X s₀ U V (colimit.desc K₂ d₂)) :
    PerfectHomLocalMap R c i X s₀ U V (colimit.desc K dK) := by
  classical
  have : IsDirected (Set.Ici i) (· ≤ ·) := ⟨fun j k ↦ by
    obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j.val k.val
    exact ⟨⟨l, j.property.trans hjl⟩, hjl, hkl⟩⟩
  have : Nonempty (Set.Ici i) := ⟨⟨i, le_rfl⟩⟩
  let a : ↑(colimit K) ≃ ↑(colimit K₁) × ↑(colimit K₂) :=
    Equiv.ofBijective _ (product_colimit_bijective K K₁ K₂ p q hpq)
  have he : (colimit.desc K dK : ↑(colimit K) → ↑dK.pt) =
      (fun x ↦ b.symm ((colimit.desc K₁ d₁) (a x).1,
        (colimit.desc K₂ d₂) (a x).2)) := by
    funext x
    have : CategoryTheory.IsFiltered (Set.Ici i) := inferInstance
    let G := forget AddCommGrpCat.{max u w}
    have : PreservesFilteredColimitsOfSize.{max u w, max u w} G := inferInstance
    have : PreservesFilteredColimitsOfSize.{u, u} G :=
      preservesFilteredColimitsOfSize_shrink G
    obtain ⟨j, f, hf⟩ := Types.jointly_surjective_of_isColimit
      (isColimitOfPreserves G (colimit.isColimit K)) x
    change (colimit.ι K j) f = x at hf
    rw [← hf]
    apply b.injective
    rw [Equiv.apply_symm_apply]
    change b ((colimit.desc K dK) ((colimit.ι K j) f)) =
      ((colimit.desc K₁ d₁) ((colim.map p) ((colimit.ι K j) f)),
       (colimit.desc K₂ d₂) ((colim.map q) ((colimit.ι K j) f)))
    rw [← ConcreteCategory.comp_apply, colimit.ι_desc]
    change b (dK.ι.app j f) = _
    rw [hb j f]
    apply Prod.ext
    · dsimp only
      have hp := ConcreteCategory.congr_hom (colimit.ι_map p j) f
      simp only [ConcreteCategory.comp_apply] at hp
      exact ((congrArg (fun y ↦ (colimit.desc K₁ d₁) y) hp).trans
        (ConcreteCategory.congr_hom (colimit.ι_desc d₁ j) (p.app j f))).symm
    · dsimp only
      have hq := ConcreteCategory.congr_hom (colimit.ι_map q j) f
      simp only [ConcreteCategory.comp_apply] at hq
      exact ((congrArg (fun y ↦ (colimit.desc K₂ d₂) y) hq).trans
        (ConcreteCategory.congr_hom (colimit.ι_desc d₂ j) (q.app j f))).symm
  rw [he]
  exact PerfectHomLocalMap.equiv (PerfectHomLocalMap.prod h₁ h₂) a b.symm

private noncomputable def shiftedBinaryHomEquiv
    {C : Type*} [Category C] [Preadditive C] [HasBinaryBiproducts C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive]
    (M B D : C) (n : ℤ) :
    ULift.{u} (M ⟶ (B ⊞ D)⟦n⟧) ≃
      ULift.{u} (M ⟶ B⟦n⟧) × ULift.{u} (M ⟶ D⟦n⟧) where
  toFun f := (⟨f.down ≫ (biprod.fst : B ⊞ D ⟶ B)⟦n⟧'⟩,
    ⟨f.down ≫ (biprod.snd : B ⊞ D ⟶ D)⟦n⟧'⟩)
  invFun f := ⟨f.1.down ≫ (biprod.inl : B ⟶ B ⊞ D)⟦n⟧' +
    f.2.down ≫ (biprod.inr : D ⟶ B ⊞ D)⟦n⟧'⟩
  left_inv f := by
    apply ULift.ext
    dsimp
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      ← Preadditive.comp_add, ← Functor.map_add, biprod.total, CategoryTheory.Functor.map_id,
      Category.comp_id]
  right_inv f := by
    apply Prod.ext <;> apply ULift.ext
    · simp [Preadditive.add_comp, Category.assoc, ← Functor.map_comp]
    · simp [Preadditive.add_comp, Category.assoc, ← Functor.map_comp]

set_option backward.isDefEq.respectTransparency false in
/-- Fixed outer-column comparison at index 0.
Source: Stacks Project, perfect.tex Tag 09RE.
(blueprint: lem-pc-perfect-hom-mayer-vietoris-geometric-columns-even-zero).

Proof: Apply the single-open stage presentation with shift -1 on U and on V.
Their mapped cocones are recognized as local comparisons by the set-colimit
preservation of the abelian-group forgetful functor and the inclusion/desc law.
The row's second triangle object is the two-open biproduct. Its shifted projections
split each stage and the apex; shifted injections give the inverse splitting.
The prescribed second component of the geometric triangle maps identifies both
projections with the transitions and cocone legs of the single-open diagrams.
The induced map from the column colimit to the product of the single-open colimits
is bijective: stage representatives give surjectivity after moving to a common
stage, and eventual equality in each factor gives injectivity after moving both
equalities to a common later stage. Transport the product of the two basic local
comparisons through this source equivalence and the inverse apex splitting.
The transported map equals the original colimit.desc on every stage representative.
The proof also covers empty opens, coincident opens and zero perfect objects.
-/
theorem perfect_hom_mayerVietoris_geometric_columns_even_zero
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
          ((A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj (0 : Fin 5))
          ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj (0 : Fin 5),
            (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
              (A.cocone F d h.stageQCoh h.limitQCoh)).app (0 : Fin 5)⟩) := by
  classical
  let H (W : X.Opens) := schemeMVDerivedRestriction Y (t ⁻¹ᵁ W) ⋙
    schemeDerivedDirectImage (t ⁻¹ᵁ W).ι
  let S := (preadditiveCoyoneda.obj (Opposite.op P)).shift (-1 : ℤ)
  let L := AddCommGrpCat.uliftFunctor.{u}
  let K := (A.diagram F h.stageQCoh ⋙ perfectHomTriangleRowFunctor Y P).flip.obj (0 : Fin 5)
  let dK : Cocone K :=
    ⟨(perfectHomTriangleRow Y P (A.cocone F d h.stageQCoh h.limitQCoh).pt).obj (0 : Fin 5),
      (perfectHomTriangleRowCoconeMap Y P (A.diagram F h.stageQCoh)
        (A.cocone F d h.stageQCoh h.limitQCoh)).app (0 : Fin 5)⟩
  have hlocal (W : X.Opens) (hW : IsCompact (W : Set X))
      (hWt : W ≤ t.opensRange) (hWUV : W = U ∨ W = V ∨ W = U ⊓ V) :
      PerfectHomLocalMap R c i X s₀ U V
        (colimit.desc (F ⋙ H W ⋙ S ⋙ L) ((H W ⋙ S ⋙ L).mapCocone d)) := by
    obtain ⟨Z, k, hkI, hk, s', hs', hsL, hsC, hsQ, hD, P', Q', hP', hQ',
      e, b, he, hb⟩ := perfect_hom_open_stage_presentation R c i X s₀ W hW
        Y t hWt s hs P Q hP hQ F d h (-1 : ℤ)
    apply PerfectHomLocalMap.basic W hWUV
    apply localComparison_of_stage_presentation R c i X s₀ W
      Z k hk s' hs' P' Q' hP' hQ'
      (F ⋙ H W ⋙ S ⋙ L) ((H W ⋙ S ⋙ L).mapCocone d)
      (fun j ↦ Equiv.ulift.trans (e j)) (Equiv.ulift.trans b)
    · intro j l hjl f
      exact he j l hjl f.down
    · intro j f
      exact hb j f.down
  let p : K ⟶ F ⋙ H U ⋙ S ⋙ L :=
    { app j := L.map (S.map biprod.fst)
      naturality := by
        intro j k f
        change L.map (S.map (A.map (h.stageQCoh j) (h.stageQCoh k) (F.map f)).hom₂) ≫
          L.map (S.map biprod.fst) =
          L.map (S.map biprod.fst) ≫ L.map (S.map ((H U).map (F.map f)))
        rw [← L.map_comp, ← L.map_comp, ← S.map_comp, ← S.map_comp, A.map_hom₂]
        exact congrArg (fun f ↦ L.map (S.map f)) (biprod.map_fst _ _) }
  let q : K ⟶ F ⋙ H V ⋙ S ⋙ L :=
    { app j := L.map (S.map biprod.snd)
      naturality := by
        intro j k f
        change L.map (S.map (A.map (h.stageQCoh j) (h.stageQCoh k) (F.map f)).hom₂) ≫
          L.map (S.map biprod.snd) =
          L.map (S.map biprod.snd) ≫ L.map (S.map ((H V).map (F.map f)))
        rw [← L.map_comp, ← L.map_comp, ← S.map_comp, ← S.map_comp, A.map_hom₂]
        exact congrArg (fun f ↦ L.map (S.map f)) (biprod.map_snd _ _) }
  refine localMap_of_binary_presentation R c i X s₀ U V K
    (F ⋙ H U ⋙ S ⋙ L) (F ⋙ H V ⋙ S ⋙ L) dK
    ((H U ⋙ S ⋙ L).mapCocone d) ((H V ⋙ S ⋙ L).mapCocone d) p q
    ?_ (shiftedBinaryHomEquiv P ((H U).obj d.pt) ((H V).obj d.pt) (-1)) ?_ ?_ ?_
  · intro j
    exact (shiftedBinaryHomEquiv P
      ((H U).obj (F.obj j)) ((H V).obj (F.obj j)) (-1)).bijective
  · intro j f
    change ULift.{u} (P ⟶
      (((H U).obj (F.obj j)) ⊞ ((H V).obj (F.obj j)))⟦(-1 : ℤ)⟧) at f
    apply Prod.ext <;> apply ULift.ext
    · change (f.down ≫ (A.map (h.stageQCoh j) h.limitQCoh
        (d.ι.app j)).hom₂⟦(-1 : ℤ)⟧') ≫ biprod.fst⟦(-1 : ℤ)⟧' =
          (f.down ≫ biprod.fst⟦(-1 : ℤ)⟧') ≫ ((H U).map (d.ι.app j))⟦(-1 : ℤ)⟧'
      have hp : (A.map (h.stageQCoh j) h.limitQCoh (d.ι.app j)).hom₂ ≫
          (biprod.fst : _ ⟶ (H U).obj d.pt) =
          (biprod.fst : _ ⟶ (H U).obj (F.obj j)) ≫ (H U).map (d.ι.app j) := by
        rw [A.map_hom₂]
        exact biprod.map_fst _ _
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun g ↦ f.down ≫ (shiftFunctor (schemeDerivedCategory Y) (-1)).map g) hp
    · change (f.down ≫ (A.map (h.stageQCoh j) h.limitQCoh
        (d.ι.app j)).hom₂⟦(-1 : ℤ)⟧') ≫ biprod.snd⟦(-1 : ℤ)⟧' =
          (f.down ≫ biprod.snd⟦(-1 : ℤ)⟧') ≫ ((H V).map (d.ι.app j))⟦(-1 : ℤ)⟧'
      have hq : (A.map (h.stageQCoh j) h.limitQCoh (d.ι.app j)).hom₂ ≫
          (biprod.snd : _ ⟶ (H V).obj d.pt) =
          (biprod.snd : _ ⟶ (H V).obj (F.obj j)) ≫ (H V).map (d.ι.app j) := by
        rw [A.map_hom₂]
        exact biprod.map_snd _ _
      simp only [Category.assoc, ← CategoryTheory.Functor.map_comp]
      exact congrArg (fun g ↦ f.down ≫ (shiftFunctor (schemeDerivedCategory Y) (-1)).map g) hq
  · apply hlocal U hU
    · rw [ht]; exact le_sup_left
    · exact Or.inl rfl
  · apply hlocal V hV.isCompact
    · rw [ht]; exact le_sup_right
    · exact Or.inr (Or.inl rfl)

end AlgebraicGeometry

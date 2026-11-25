/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationData
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor

/-! # Hom complex comparison with specified product projections

Source: Stacks Project, Tags 0A8X and 08DL, Hom complexes and their differential.
(blueprint: lem-pc-hom-complex-over-equiv-projections). -/

@[expose] public section

set_option autoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

private def projection_spec
    {C : Type u} [Category C] [Preadditive C]
    (obj : C → C → C)
    (map : ∀ {A A' B B'}, (A' ⟶ A) → (B ⟶ B') → (obj A B ⟶ obj A' B'))
    (G : (CochainComplex C ℤ)ᵒᵖ ⥤ CochainComplex C ℤ ⥤ CochainComplex C ℤ)
    (π : ∀ (L M : CochainComplex C ℤ) (n p q : ℤ), p + n = q →
        (((G.obj (op L)).obj M).X n ⟶ obj (L.X p) (M.X q))) : Prop :=
        (∀ (L M : CochainComplex C ℤ) (n : ℤ),
          Nonempty (IsLimit (Fan.mk (((G.obj (op L)).obj M).X n)
            (fun p : ℤ ↦ π L M n p (p + n) rfl)))) ∧
        (∀ (L M : CochainComplex C ℤ) (n m p q q' p' : ℤ)
          (_hnm : n + 1 = m) (hpq : p + m = q)
          (hq' : p + n = q') (hp' : p' + n = q),
          ((G.obj (op L)).obj M).d n m ≫ π L M m p q hpq =
            π L M n p q' hq' ≫ map (𝟙 (L.X p)) (M.d q' q) -
              n.negOnePow • (π L M n p' q hp' ≫ map (L.d p p') (𝟙 (M.X q)))) ∧
        (∀ (L L' M M' : CochainComplex C ℤ) (f : L' ⟶ L) (g : M ⟶ M')
          (n p q : ℤ) (hpq : p + n = q),
          (((G.map f.op).app M) ≫ (G.obj (op L')).map g).f n ≫ π L' M' n p q hpq =
            π L M n p q hpq ≫ map (f.f p) (g.f q))

private theorem factor_differential
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (F : C ⥤ D) [F.Additive]
    {Hn Hm A B E : C} {Kn Km A' B' E' : D}
    (dH : Hn ⟶ Hm) (dK : Kn ⟶ Km)
    (a : Hn ⟶ A) (b : Hn ⟶ B) (c : Hm ⟶ E)
    (α : A ⟶ E) (β : B ⟶ E)
    (a' : Kn ⟶ A') (b' : Kn ⟶ B') (c' : Km ⟶ E')
    (α' : A' ⟶ E') (β' : B' ⟶ E')
    (en : F.obj Hn ⟶ Kn) (em : F.obj Hm ⟶ Km)
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤˣ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Linear.comp_units_smul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, CategoryTheory.Functor.map_units_smul, Functor.map_comp,
    Preadditive.sub_comp, Linear.units_smul_comp, Category.assoc, hα, hβ]


private theorem id_first
    {C D E : Type*} [Category C] [Category D] [Category E]
    (G : Cᵒᵖ ⥤ D ⥤ E) (L : C) {M N : D} (f : M ⟶ N) :
    (G.map (𝟙 L).op).app M ≫ (G.obj (op L)).map f = (G.obj (op L)).map f := by
  rw [op_id, CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]

private theorem factor_naturality
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {HM HN A B : C} {KM KN A' B' : D}
    (h : HM ⟶ HN) (k : KM ⟶ KN)
    (πM : HM ⟶ A) (πN : HN ⟶ B) (τM : KM ⟶ A') (τN : KN ⟶ B')
    (φ : A ⟶ B) (ψ : A' ⟶ B')
    (eM : F.obj HM ⟶ KM) (eN : F.obj HN ⟶ KN)
    (sM : F.obj A ⟶ A') (sN : F.obj B ⟶ B')
    (heM : eM ≫ τM = F.map πM ≫ sM) (heN : eN ≫ τN = F.map πN ≫ sN)
    (hh : h ≫ πN = πM ≫ φ) (hk : k ≫ τN = τM ≫ ψ)
    (hs : F.map φ ≫ sN = sM ≫ ψ) :
    (F.map h ≫ eN) ≫ τN = (eM ≫ k) ≫ τN := by
  calc
    _ = F.map h ≫ (F.map πN ≫ sN) := by rw [Category.assoc, heN]
    _ = F.map (h ≫ πN) ≫ sN := by rw [Functor.map_comp, Category.assoc]
    _ = F.map πM ≫ (F.map φ ≫ sN) := by rw [hh, Functor.map_comp, Category.assoc]
    _ = (F.map πM ≫ sM) ≫ ψ := by rw [hs, Category.assoc]
    _ = eM ≫ (τM ≫ ψ) := by rw [← heM, Category.assoc]
    _ = _ := by rw [← hk, Category.assoc]

-- The generic product and signed differential calculation needs extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
private theorem compare_hom_complex
      (C D : Type (u + 1)) [Category.{u} C] [Category.{u} D]
      [Preadditive C] [Preadditive D]
      (objY : C → C → C)
      (mapY : ∀ {A A' B B'}, (A' ⟶ A) → (B ⟶ B') → (objY A B ⟶ objY A' B'))
      (objZ : D → D → D)
      (mapZ : ∀ {A A' B B'}, (A' ⟶ A) → (B ⟶ B') → (objZ A B ⟶ objZ A' B'))
      (F : C ⥤ D)
      [F.Additive] [PreservesLimitsOfShape (Discrete ℤ) F]
      (HY : (CochainComplex (C) ℤ)ᵒᵖ ⥤
        CochainComplex (C) ℤ ⥤
        CochainComplex (C) ℤ)
      (HZ : (CochainComplex (D) ℤ)ᵒᵖ ⥤
        CochainComplex (D) ℤ ⥤
        CochainComplex (D) ℤ)
      (π : ∀ (L M : CochainComplex C ℤ) (n p q : ℤ), p + n = q →
        (((HY.obj (op L)).obj M).X n ⟶ objY (L.X p) (M.X q)))
      (τ : ∀ (L M : CochainComplex D ℤ) (n p q : ℤ), p + n = q →
        (((HZ.obj (op L)).obj M).X n ⟶ objZ (L.X p) (M.X q)))
      (hπ : projection_spec objY mapY HY π)
      (hτ : projection_spec objZ mapZ HZ τ)
      (s : ∀ A B : C,
        F.obj (objY A B) ≅
          objZ (F.obj A) (F.obj B))
      (hs : ∀ {A A' B B'} (f : A' ⟶ A) (g : B ⟶ B'),
        F.map (mapY f g) ≫ (s A' B').hom =
          (s A B).hom ≫ mapZ (F.map f) (F.map g))
      (L : CochainComplex (C) ℤ) :
      let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
      let H := HY.obj (op L)
      let K := HZ.obj (op (FC.obj L))
      ∃ E : ∀ M : CochainComplex (C) ℤ,
        FC.obj (H.obj M) ≅ K.obj (FC.obj M),
        (∀ {M N : CochainComplex (C) ℤ} (f : M ⟶ N),
          FC.map (H.map f) ≫ (E N).hom = (E M).hom ≫ K.map (FC.map f)) ∧
        (∀ (M : CochainComplex C ℤ) (n p q : ℤ) (hpq : p + n = q),
          (E M).hom.f n ≫ τ (FC.obj L) (FC.obj M) n p q hpq =
            F.map (π L M n p q hpq) ≫ (s (L.X p) (M.X q)).hom) := by
  classical
  let FC := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let LF := FC.obj L
  let H := HY.obj (op L)
  let K := HZ.obj (op LF)
  have hp (M : CochainComplex (C) ℤ) (n : ℤ) :
      IsLimit (Fan.mk (F.obj ((H.obj M).X n))
        (fun p : ℤ ↦ F.map (π L M n p (p + n) rfl))) :=
    isLimitFanMkObjOfIsLimit F _ _ (Classical.choice (hπ.1 L M n))
  have ht (M : CochainComplex (C) ℤ) (n : ℤ) :
      IsLimit (Fan.mk ((K.obj (FC.obj M)).X n)
        (fun p : ℤ ↦ τ LF (FC.obj M) n p (p + n) rfl)) :=
    Classical.choice (hτ.1 LF (FC.obj M) n)
  have hi (M : CochainComplex (C) ℤ) (n : ℤ) :
      ∃ a : F.obj ((H.obj M).X n) ≅ (K.obj (FC.obj M)).X n,
        ∀ p : ℤ, a.hom ≫ τ LF (FC.obj M) n p (p + n) rfl =
          F.map (π L M n p (p + n) rfl) ≫
            (s (L.X p) (M.X (p + n))).hom := by
    let a := Fan.IsLimit.lift (ht M n)
      (fun p ↦ F.map (π L M n p (p + n) rfl) ≫
        (s (L.X p) (M.X (p + n))).hom)
    let b := Fan.IsLimit.lift (hp M n)
      (fun p ↦ τ LF (FC.obj M) n p (p + n) rfl ≫
        (s (L.X p) (M.X (p + n))).inv)
    have ha (p : ℤ) :
        a ≫ τ LF (FC.obj M) n p (p + n) rfl =
          F.map (π L M n p (p + n) rfl) ≫
            (s (L.X p) (M.X (p + n))).hom :=
      Fan.IsLimit.fac (ht M n) _ p
    have hb (p : ℤ) :
        b ≫ F.map (π L M n p (p + n) rfl) =
          τ LF (FC.obj M) n p (p + n) rfl ≫
            (s (L.X p) (M.X (p + n))).inv :=
      Fan.IsLimit.fac (hp M n) _ p
    refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
    · apply Fan.IsLimit.hom_ext (hp M n)
      intro p
      change (a ≫ b) ≫ F.map (π L M n p (p + n) rfl) =
        (𝟙 _) ≫ F.map (π L M n p (p + n) rfl)
      rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
        Iso.hom_inv_id, Category.comp_id, Category.id_comp]
    · apply Fan.IsLimit.hom_ext (ht M n)
      intro p
      change (b ≫ a) ≫ τ LF (FC.obj M) n p (p + n) rfl =
        (𝟙 _) ≫ τ LF (FC.obj M) n p (p + n) rfl
      rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
        Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  choose e he using hi
  have he' (M : CochainComplex (C) ℤ)
      (n p q : ℤ) (hpq : p + n = q) :
      (e M n).hom ≫ τ LF (FC.obj M) n p q hpq =
        F.map (π L M n p q hpq) ≫ (s (L.X p) (M.X q)).hom := by
    subst q
    exact he M n p
  have comm (M : CochainComplex (C) ℤ)
      (n m : ℤ) (hnm : n + 1 = m) :
      (e M n).hom ≫ (K.obj (FC.obj M)).d n m =
        F.map ((H.obj M).d n m) ≫ (e M m).hom := by
    apply Fan.IsLimit.hom_ext (ht M m)
    intro p
    change ((e M n).hom ≫ (K.obj (FC.obj M)).d n m) ≫
        τ LF (FC.obj M) m p (p + m) rfl =
      (F.map ((H.obj M).d n m) ≫ (e M m).hom) ≫
        τ LF (FC.obj M) m p (p + m) rfl
    have hH := hπ.2.1 L M n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    have hK := hτ.2.1 LF (FC.obj M) n m p (p + m) (p + n) (p + 1)
      hnm rfl rfl (by omega)
    apply factor_differential F
      ((H.obj M).d n m) ((K.obj (FC.obj M)).d n m)
      (π L M n p (p + n) rfl) (π L M n (p + 1) (p + m) (by omega))
      (π L M m p (p + m) rfl)
      (mapY (𝟙 (L.X p)) (M.d (p + n) (p + m)))
      (mapY (L.d p (p + 1)) (𝟙 (M.X (p + m))))
      (τ LF (FC.obj M) n p (p + n) rfl)
      (τ LF (FC.obj M) n (p + 1) (p + m) (by omega))
      (τ LF (FC.obj M) m p (p + m) rfl)
      (mapZ (𝟙 (LF.X p)) ((FC.obj M).d (p + n) (p + m)))
      (mapZ (LF.d p (p + 1)) (𝟙 ((FC.obj M).X (p + m))))
      (e M n).hom (e M m).hom
      (s (L.X p) (M.X (p + n))).hom
      (s (L.X (p + 1)) (M.X (p + m))).hom
      (s (L.X p) (M.X (p + m))).hom n.negOnePow
      hH hK (he' M n p (p + n) rfl)
      (he' M n (p + 1) (p + m) (by omega)) (he' M m p (p + m) rfl)
    · have h := hs (𝟙 (L.X p)) (M.d (p + n) (p + m))
      rw [F.map_id] at h
      exact h
    · have h := hs (L.d p (p + 1)) (𝟙 (M.X (p + m)))
      rw [F.map_id] at h
      exact h
  let E (M : CochainComplex (C) ℤ) :
      FC.obj (H.obj M) ≅ K.obj (FC.obj M) :=
    HomologicalComplex.Hom.isoOfComponents (e M) (comm M)
  refine ⟨E, ?_, ?_⟩
  swap
  · intro M n p q hpq
    exact he' M n p q hpq
  intro M N f
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (ht N n)
  intro p
  change (F.map ((H.map f).f n) ≫ (e N n).hom) ≫
      τ LF (FC.obj N) n p (p + n) rfl =
    ((e M n).hom ≫ (K.map (FC.map f)).f n) ≫
      τ LF (FC.obj N) n p (p + n) rfl
  have hmap (M N : CochainComplex (C) ℤ) (f : M ⟶ N) :
      (H.map f).f n ≫ π L N n p (p + n) rfl =
        π L M n p (p + n) rfl ≫
          mapY (𝟙 (L.X p)) (f.f (p + n)) := by
    have h := hπ.2.2 L L M N (𝟙 L) f n p (p + n) rfl
    have hid := id_first HY L f
    exact (congrArg (fun t ↦ t.f n ≫ π L N n p (p + n) rfl) hid).symm.trans h
  have hmap' : (K.map (FC.map f)).f n ≫ τ LF (FC.obj N) n p (p + n) rfl =
      τ LF (FC.obj M) n p (p + n) rfl ≫
        mapZ (𝟙 (LF.X p)) ((FC.map f).f (p + n)) := by
    have h := hτ.2.2 LF LF (FC.obj M) (FC.obj N) (𝟙 LF) (FC.map f)
      n p (p + n) rfl
    have hid := id_first HZ LF (FC.map f)
    exact (congrArg (fun t ↦ t.f n ≫ τ LF (FC.obj N) n p (p + n) rfl) hid).symm.trans h
  have hs' := hs (𝟙 (L.X p)) (f.f (p + n))
  rw [F.map_id] at hs'
  exact factor_naturality F ((H.map f).f n) ((K.map (FC.map f)).f n)
    (π L M n p (p + n) rfl) (π L N n p (p + n) rfl)
    (τ LF (FC.obj M) n p (p + n) rfl) (τ LF (FC.obj N) n p (p + n) rfl)
    (mapY
      (𝟙 (L.X p)) (f.f (p + n)))
    (mapZ
      (𝟙 (LF.X p)) ((FC.map f).f (p + n)))
    (e M n).hom (e N n).hom
    (s (L.X p) (M.X (p + n))).hom (s (L.X p) (N.X (p + n))).hom
    (he' M n p (p + n) rfl) (he' N n p (p + n) rfl) (hmap M N f) hmap' hs'

-- Specializing the generic Hom-complex interface requires extra elaboration fuel.
set_option backward.isDefEq.respectTransparency false in
/-- Assemble any natural termwise internal-Hom comparison through the specified
product projections, retaining both the differential and naturality in the target.
Source: Stacks Project, Tags 0A8X and 08DL.
(blueprint: lem-pc-hom-complex-over-equiv-projections).

Proof: the equivalence preserves each product fan. Postcompose its projections
with the given termwise isomorphisms and use uniqueness of product objects to
obtain a degreewise isomorphism. Its defining projection equation identifies the
two differential formulas by naturality of the termwise comparison, additivity,
and preservation of integer scalar multiplication. Assemble the degreewise maps
into a chain isomorphism. For naturality, postcompose in every degree with every
Hom projection, use the specified action of the Hom bifunctor, and apply the
termwise naturality equation. Product projections are jointly monic, so these
component equations imply equality. No boundedness or nonzero-open assumption is
used: the product fans and their universal properties apply to all complexes. -/
theorem exists_homComplex_overEquiv_projections (X : Scheme.{u}) (U : X.Opens)
    (P : CochainComplex (localEvaluationModules X U) ℤ) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} U.toScheme.ringCatSheaf)
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∀ (e : ∀ A B : localEvaluationModules X U,
        L.obj (SheafOfModules.homObj (R := X.sheaf.over U) A B) ≅
          SheafOfModules.homObj (R := U.toScheme.sheaf) (L.obj A) (L.obj B)),
      (∀ (A A' B B' : localEvaluationModules X U) (f : A' ⟶ A) (g : B ⟶ B'),
        L.map (SheafOfModules.homObjMap (R := X.sheaf.over U) f g) ≫
            (e A' B').hom =
          (e A B).hom ≫ SheafOfModules.homObjMap (R := U.toScheme.sheaf)
            (L.map f) (L.map g)) →
      ∃ b : ∀ M : CochainComplex (localEvaluationModules X U) ℤ,
          T.obj (homComplex (R := X.sheaf.over U) P M) ≅
            homComplex (R := U.toScheme.sheaf) (T.obj P) (T.obj M),
        (∀ (M N : CochainComplex (localEvaluationModules X U) ℤ) (a : M ⟶ N),
          T.map (((homComplexFunctor (R := X.sheaf.over U)).obj (op P)).map a) ≫
              (b N).hom =
            (b M).hom ≫ ((homComplexFunctor (R := U.toScheme.sheaf)).obj
              (op (T.obj P))).map (T.map a)) ∧
        (∀ (M : CochainComplex (localEvaluationModules X U) ℤ)
            (n r s : ℤ) (h : r + n = s),
          (b M).hom.f n ≫
              (Classical.choose (homComplex_projections_exists.{u, u, u, u}
                (R := U.toScheme.sheaf)))
                (T.obj P) (T.obj M) n r s h =
            L.map (localEvaluationProjection X U P M n r s h) ≫
              (e (P.X r) (M.X s)).hom) := by
  classical
  dsimp only
  intro e he
  let L := (Scheme.Modules.overEquiv U).functor
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  exact compare_hom_complex _ _
    (SheafOfModules.homObj (R := X.sheaf.over U))
    (fun f g ↦ SheafOfModules.homObjMap (R := X.sheaf.over U) f g)
    (SheafOfModules.homObj (R := U.toScheme.sheaf))
    (fun f g ↦ SheafOfModules.homObjMap (R := U.toScheme.sheaf) f g) L
    (homComplexFunctor.{u, u, u, u} (R := X.sheaf.over U))
    (homComplexFunctor.{u, u, u, u} (R := U.toScheme.sheaf))
    (Classical.choose (homComplex_projections_exists (R := X.sheaf.over U)))
    (Classical.choose (homComplex_projections_exists (R := U.toScheme.sheaf)))
    (Classical.choose_spec (homComplex_projections_exists (R := X.sheaf.over U)))
    (Classical.choose_spec (homComplex_projections_exists (R := U.toScheme.sheaf)))
    e (fun f g ↦ he _ _ _ _ f g) P

end AlgebraicGeometry

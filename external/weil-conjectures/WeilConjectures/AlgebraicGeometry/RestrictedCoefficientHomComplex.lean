/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.ReflectsIso.Balanced
public import WeilConjectures.Algebra.Homology.BilinearHomComplex
public import WeilConjectures.Algebra.Homology.HomComplexComponents
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHom
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators

/-! # Coefficient Hom complexes over a ring-sheaf extension

Source: Stacks Project, Algebraization, Tag 099I
(auxiliary; not a blueprint node).
-/

@[expose] public section

set_option autoImplicit false
universe u v
open CategoryTheory CategoryTheory.Limits Opposite

-- Limit preservation gives a small proof of the required sheaf-composition instance.
attribute [local instance 0] CategoryTheory.hasSheafCompose_of_preservesMulticospan
attribute [local instance 20000] CategoryTheory.hasSheafCompose_of_preservesLimitsOfSize

namespace SheafOfModules

private theorem productComplexComparison
    {D : Type u} [Category D] [Preadditive D]
    (K L : CochainComplex D ℤ) (T : ℤ → ℤ → D)
    (π : ∀ n p q : ℤ, p + n = q → (K.X n ⟶ T p q))
    (ρ : ∀ n p q : ℤ, p + n = q → (L.X n ⟶ T p q))
    (hπ : ∀ n, IsLimit (Fan.mk (K.X n) (fun p ↦ π n p (p + n) rfl)))
    (hρ : ∀ n, IsLimit (Fan.mk (L.X n) (fun p ↦ ρ n p (p + n) rfl)))
    (post : ∀ p q q', T p q' ⟶ T p q)
    (pre : ∀ p p' q, T p' q ⟶ T p q)
    (hdK : ∀ n m p q q' p' : ℤ, n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      K.d n m ≫ π m p q h = π n p q' h' ≫ post p q q' -
        n.negOnePow • (π n p' q h'' ≫ pre p p' q))
    (hdL : ∀ n m p q q' p' : ℤ, n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      L.d n m ≫ ρ m p q h = ρ n p q' h' ≫ post p q q' -
        n.negOnePow • (ρ n p' q h'' ≫ pre p p' q)) :
    ∃ e : K ≅ L, ∀ (n p q : ℤ) (h : p + n = q),
      e.hom.f n ≫ ρ n p q h = π n p q h := by
  let a (n : ℤ) := (hπ n).conePointUniqueUpToIso (hρ n)
  have ha (n p q : ℤ) (h : p + n = q) :
      (a n).hom ≫ ρ n p q h = π n p q h := by
    subst q
    exact IsLimit.conePointUniqueUpToIso_hom_comp (hπ n) (hρ n) ⟨p⟩
  let E : K ≅ L := HomologicalComplex.Hom.isoOfComponents a (by
    intro n m hnm
    apply Fan.IsLimit.hom_ext (hρ m)
    intro p
    change ((a n).hom ≫ L.d n m) ≫ ρ m p (p + m) rfl =
      (K.d n m ≫ (a m).hom) ≫ ρ m p (p + m) rfl
    rw [Category.assoc,
      hdL n m p (p + m) (p + n) (p + m - n) hnm rfl rfl (by omega),
      Preadditive.comp_sub, Linear.comp_units_smul,
      ← Category.assoc, ha, ← Category.assoc, ha, Category.assoc, ha,
      hdK n m p (p + m) (p + n) (p + m - n) hnm rfl rfl (by omega)])
  exact ⟨E, ha⟩

private theorem mapTwoTermDifferential
    {D E : Type u} [Category D] [Category E] [Preadditive D] [Preadditive E]
    (r : D ⥤ E) [r.Additive] {K K' T T₁ T₂ : D} {U U₁ U₂ : E}
    (d : K ⟶ K') (π : K' ⟶ T) (p₁ : K ⟶ T₁) (p₂ : K ⟶ T₂)
    (t₁ : T₁ ⟶ T) (t₂ : T₂ ⟶ T) (c : r.obj T ⟶ U)
    (c₁ : r.obj T₁ ⟶ U₁) (c₂ : r.obj T₂ ⟶ U₂)
    (u₁ : U₁ ⟶ U) (u₂ : U₂ ⟶ U) (s : ℤˣ)
    (hd : d ≫ π = p₁ ≫ t₁ - s • (p₂ ≫ t₂))
    (h₁ : r.map t₁ ≫ c = c₁ ≫ u₁) (h₂ : r.map t₂ ≫ c = c₂ ≫ u₂) :
    r.map d ≫ (r.map π ≫ c) =
      (r.map p₁ ≫ c₁) ≫ u₁ - s • ((r.map p₂ ≫ c₂) ≫ u₂) := by
  rw [← Category.assoc, ← r.map_comp, hd, r.map_sub, r.map_units_smul,
    Preadditive.sub_comp, Linear.units_smul_comp]
  simp only [r.map_comp, Category.assoc, h₁, h₂]

private theorem projectionIntertwine
    {D E : Type u} [Category D] [Category E] (r : D ⥤ E)
    {A A' B B' : D} {C C' T T' : E}
    (m : A ⟶ A') (p : A ⟶ B) (p' : A' ⟶ B') (t : B ⟶ B')
    (v : C ⟶ C') (ρ : C ⟶ T) (ρ' : C' ⟶ T') (u : T ⟶ T')
    (e : r.obj A ⟶ C) (e' : r.obj A' ⟶ C')
    (c : r.obj B ⟶ T) (c' : r.obj B' ⟶ T')
    (hm : m ≫ p' = p ≫ t) (hv : v ≫ ρ' = ρ ≫ u)
    (he : e ≫ ρ = r.map p ≫ c) (he' : e' ≫ ρ' = r.map p' ≫ c')
    (hc : r.map t ≫ c' = c ≫ u) :
    (r.map m ≫ e') ≫ ρ' = (e ≫ v) ≫ ρ' := by
  rw [Category.assoc, he', ← Category.assoc, ← r.map_comp, hm, r.map_comp,
    Category.assoc, hc, ← Category.assoc, ← he, Category.assoc,
    ← hv, ← Category.assoc]

variable {C : Type u} [SmallCategory C] {J : GrothendieckTopology C}
  {R B : Sheaf J CommRingCat.{u}} (φ : R ⟶ B)

set_option backward.isDefEq.respectTransparency false in
private theorem coefficientRestriction_preservesLimits :
    PreservesLimitsOfSize.{u, u} (restrictScalars.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)) := by
    let r := restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
    let U := SheafOfModules.forget.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⋙
      PresheafOfModules.toPresheaf.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R).obj
    have : PreservesLimitsOfSize.{u, u} (r ⋙ U) :=
      inferInstanceAs (PreservesLimitsOfSize.{u, u}
        (SheafOfModules.forget.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B) ⋙
          PresheafOfModules.toPresheaf.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B).obj))
    have : ReflectsLimitsOfSize.{u, u} U := reflectsLimits_of_reflectsIsomorphisms
    exact preservesLimits_of_reflects_of_preserves r U

private theorem genericComplexComparison
    {A E : Type u} [Category.{v} A] [Category.{v} E]
    [Preadditive A] [Preadditive E]
    (r : A ⥤ E) [r.Additive] [PreservesLimitsOfSize.{0, 0} r]
    (H : Aᵒᵖ ⥤ E ⥤ A) (K : Eᵒᵖ ⥤ E ⥤ E)
    (G : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex A ℤ)
    (T : (CochainComplex E ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (c : Functor.uncurry.obj H ⋙ r ≅
      r.op.prod (𝟭 E) ⋙ Functor.uncurry.obj K)
    (dG : ProductHomComplexData H G)
    (ρ : ∀ (L M : CochainComplex E ℤ) (n p q : ℤ), p + n = q →
      (((T.obj (op L)).obj M).X n ⟶ (K.obj (op (L.X p))).obj (M.X q)))
    (hρ : ∀ (L M : CochainComplex E ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((T.obj (op L)).obj M).X n)
        (fun p ↦ ρ L M n p (p + n) rfl))))
    (hdρ : ∀ (L M : CochainComplex E ℤ) (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      ((T.obj (op L)).obj M).d n m ≫ ρ L M m p q h =
        ρ L M n p q' h' ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
          ((𝟙 _).op, M.d q' q) - n.negOnePow •
        (ρ L M n p' q h'' ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
          ((L.d p p').op, 𝟙 _)))
    (hmρ : ∀ (L L' M M' : CochainComplex E ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (h : p + n = q),
      (((T.map f.op).app M) ≫ (T.obj (op L')).map g).f n ≫ ρ L' M' n p q h =
        ρ L M n p q h ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
          ((f.f p).op, g.f q)) :
    let rc := r.mapHomologicalComplex (.up ℤ)
    ∃ e : Functor.uncurry.obj G ⋙ rc ≅
        rc.op.prod (𝟭 _) ⋙ Functor.uncurry.obj T,
      ∀ (L : CochainComplex A ℤ) (M : CochainComplex E ℤ)
        (n p q : ℤ) (h : p + n = q),
        (e.hom.app (op L, M)).f n ≫
          ρ (rc.obj L) M n p q h =
            r.map (dG.π L M n p q h) ≫
              c.hom.app (op (L.X p), M.X q) := by
  let rc := r.mapHomologicalComplex (.up ℤ)
  let π := dG.π
  have hπ := dG.isLimit
  have hd := dG.differential
  have hm := dG.naturality
  have hc {A₀ A₁ : A} {N N' : E} (f : A₁ ⟶ A₀) (g : N ⟶ N') :
      r.map ((Functor.uncurry.obj H).map
          (X := (op A₀, N)) (Y := (op A₁, N')) (f.op, g)) ≫
        c.hom.app (op A₁, N') =
      c.hom.app (op A₀, N) ≫ (Functor.uncurry.obj K).map
        (X := (op (r.obj A₀), N)) (Y := (op (r.obj A₁), N')) ((r.map f).op, g) := by
    exact c.hom.naturality (show (op A₀, N) ⟶ (op A₁, N') from (f.op, g))
  let aπ (L : CochainComplex A ℤ) (M : CochainComplex E ℤ)
      (n p q : ℤ) (h : p + n = q) :
      r.obj (((G.obj (op L)).obj M).X n) ⟶
        (K.obj (op (r.obj (L.X p)))).obj (M.X q) :=
    r.map (π L M n p q h) ≫ c.hom.app (op (L.X p), M.X q)
  have hπr (L : CochainComplex A ℤ) (M : CochainComplex E ℤ) (n : ℤ) :
      IsLimit (Fan.mk (r.obj (((G.obj (op L)).obj M).X n))
        (fun p ↦ aπ L M n p (p + n) rfl)) := by
    let V (p : ℤ) := (H.obj (op (L.X p))).obj (M.X (p + n))
    let h := isLimitFanMkObjOfIsLimit r V
      (fun p ↦ π L M n p (p + n) rfl) (hπ L M n).some
    let e : Discrete.functor (fun p : ℤ ↦ r.obj (V p)) ≅
        Discrete.functor (fun p : ℤ ↦ (K.obj (op (r.obj (L.X p)))).obj (M.X (p + n))) :=
      Discrete.natIso (fun p : Discrete ℤ ↦ c.app (op (L.X p.as), M.X (p.as + n)))
    exact (IsLimit.postcomposeHomEquiv e _).symm h
  have hE (L : CochainComplex A ℤ) (M : CochainComplex E ℤ) :
      ∃ e : rc.obj ((G.obj (op L)).obj M) ≅ (T.obj (op (rc.obj L))).obj M,
        ∀ (n p q : ℤ) (h : p + n = q),
          e.hom.f n ≫ ρ (rc.obj L) M n p q h = aπ L M n p q h := by
    apply productComplexComparison
      (rc.obj ((G.obj (op L)).obj M)) ((T.obj (op (rc.obj L))).obj M)
      (fun p q ↦ (K.obj (op (r.obj (L.X p)))).obj (M.X q))
      (aπ L M) (ρ (rc.obj L) M) (hπr L M) (fun n ↦ (hρ (rc.obj L) M n).some)
      (fun p q q' ↦ (Functor.uncurry.obj K).map
        (X := (op (r.obj (L.X p)), M.X q'))
        (Y := (op (r.obj (L.X p)), M.X q)) ((𝟙 _).op, M.d q' q))
      (fun p p' q ↦ (Functor.uncurry.obj K).map
        (X := (op (r.obj (L.X p')), M.X q))
        (Y := (op (r.obj (L.X p)), M.X q)) ((r.map (L.d p p')).op, 𝟙 _))
    · intro n m p q q' p' hnm hpq hq' hp'
      exact mapTwoTermDifferential r _ _ _ _ _ _ _ _ _ _ _ _
        (hd L M n m p q q' p' hnm hpq hq' hp')
        (by simpa only [r.map_id] using hc (𝟙 (L.X p)) (M.d q' q))
        (hc (L.d p p') (𝟙 (M.X q)))
    · exact hdρ (rc.obj L) M
  choose e he using hE
  refine ⟨NatIso.ofComponents (fun X ↦ e X.1.unop X.2) ?_, ?_⟩
  rotate_left
  · exact he
  intro X Y f
  apply HomologicalComplex.hom_ext
  intro n
  apply Fan.IsLimit.hom_ext (hρ (rc.obj Y.1.unop) Y.2 n).some
  intro p
  let sourceMap := (G.map f.1).app X.2 ≫ (G.obj Y.1).map f.2
  let targetMap := (T.map (rc.map f.1.unop).op).app X.2 ≫
    (T.obj (op (rc.obj Y.1.unop))).map f.2
  change (r.map (sourceMap.f n) ≫ (e Y.1.unop Y.2).hom.f n) ≫
      ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl =
    ((e X.1.unop X.2).hom.f n ≫ targetMap.f n) ≫
      ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl
  exact projectionIntertwine r (sourceMap.f n)
    (π X.1.unop X.2 n p (p + n) rfl) (π Y.1.unop Y.2 n p (p + n) rfl)
    ((Functor.uncurry.obj H).map
      (X := (op (X.1.unop.X p), X.2.X (p + n)))
      (Y := (op (Y.1.unop.X p), Y.2.X (p + n)))
      ((f.1.unop.f p).op, f.2.f (p + n)))
    (targetMap.f n)
    (ρ (rc.obj X.1.unop) X.2 n p (p + n) rfl)
    (ρ (rc.obj Y.1.unop) Y.2 n p (p + n) rfl)
    ((Functor.uncurry.obj K).map
      (X := (op (r.obj (X.1.unop.X p)), X.2.X (p + n)))
      (Y := (op (r.obj (Y.1.unop.X p)), Y.2.X (p + n)))
      ((r.map (f.1.unop.f p)).op, f.2.f (p + n)))
    ((e X.1.unop X.2).hom.f n) ((e Y.1.unop Y.2).hom.f n)
    (c.hom.app (op (X.1.unop.X p), X.2.X (p + n)))
    (c.hom.app (op (Y.1.unop.X p), Y.2.X (p + n)))
    (hm X.1.unop Y.1.unop X.2 Y.2 f.1.unop f.2 n p (p + n) rfl)
    (hmρ (rc.obj X.1.unop) (rc.obj Y.1.unop) X.2 Y.2
      (rc.map f.1.unop) f.2 n p (p + n) rfl)
    (he X.1.unop X.2 n p (p + n) rfl) (he Y.1.unop Y.2 n p (p + n) rfl)
    (hc (f.1.unop.f p) (f.2.f (p + n)))

private theorem genericUncurriedComplexComparison
    {A E : Type u} [Category.{v} A] [Category.{v} E]
    [Preadditive A] [Preadditive E]
    (r : A ⥤ E) [r.Additive] [PreservesLimitsOfSize.{0, 0} r]
    (H : Aᵒᵖ × E ⥤ A) (K : Eᵒᵖ ⥤ E ⥤ E)
    (G : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex A ℤ)
    (T : (CochainComplex E ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex E ℤ)
    (c : H ⋙ r ≅
      r.op.prod (𝟭 E) ⋙ Functor.uncurry.obj K)
    (dG : ProductHomComplexData (Functor.curry.obj H) G)
    (ρ : ∀ (L M : CochainComplex E ℤ) (n p q : ℤ), p + n = q →
      (((T.obj (op L)).obj M).X n ⟶ (K.obj (op (L.X p))).obj (M.X q)))
    (hρ : ∀ (L M : CochainComplex E ℤ) (n : ℤ),
      Nonempty (IsLimit (Fan.mk (((T.obj (op L)).obj M).X n)
        (fun p ↦ ρ L M n p (p + n) rfl))))
    (hdρ : ∀ (L M : CochainComplex E ℤ) (n m p q q' p' : ℤ), n + 1 = m →
      ∀ (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q),
      ((T.obj (op L)).obj M).d n m ≫ ρ L M m p q h =
        ρ L M n p q' h' ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
          ((𝟙 _).op, M.d q' q) - n.negOnePow •
        (ρ L M n p' q h'' ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
          ((L.d p p').op, 𝟙 _)))
    (hmρ : ∀ (L L' M M' : CochainComplex E ℤ) (f : L' ⟶ L) (g : M ⟶ M')
      (n p q : ℤ) (h : p + n = q),
      (((T.map f.op).app M) ≫ (T.obj (op L')).map g).f n ≫ ρ L' M' n p q h =
        ρ L M n p q h ≫ (Functor.uncurry.obj K).map
          (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
          ((f.f p).op, g.f q)) :
    let rc := r.mapHomologicalComplex (.up ℤ)
    ∃ e : Functor.uncurry.obj G ⋙ rc ≅
        rc.op.prod (𝟭 _) ⋙ Functor.uncurry.obj T,
      ∀ (L : CochainComplex A ℤ) (M : CochainComplex E ℤ)
        (n p q : ℤ) (h : p + n = q),
        (e.hom.app (op L, M)).f n ≫
          ρ (rc.obj L) M n p q h =
            r.map (dG.π L M n p q h) ≫
              c.hom.app (op (L.X p), M.X q) := by
  let c' := Functor.isoWhiskerRight (Functor.currying.counitIso.app H) r ≪≫ c
  obtain ⟨e, he⟩ := genericComplexComparison r (Functor.curry.obj H) K G T c' dG
    ρ hρ hdρ hmρ
  refine ⟨e, ?_⟩
  intro L M n p q h
  have hp := he L M n p q h
  have hc (X) : c'.hom.app X = c.hom.app X := by
    change r.map (𝟙 (H.obj X)) ≫ c.hom.app X = c.hom.app X
    rw [r.map_id, Category.id_comp]
  simpa only [hc] using hp

section NormalizedComparison
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]

/-- The actual coefficient comparison map with explicit internal-Hom endpoints.
Source: Stacks Project, Algebraization, Tag 099I.
(auxiliary; not a blueprint node). -/
noncomputable def coefficientHomObjComparisonHom
    (H : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (i : H ⋙ restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
        (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R))
    (X : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) :
    (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
        (H.obj X) ⟶
      homObj (R := R)
        ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).obj
          X.1.unop) X.2 := i.hom.app X

/-- The uncurried Hom bifunctor acts by the ordinary internal-Hom map.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node).
Proof: uncurrying first precomposes and then postcomposes; the composition law for
internal-Hom maps identifies their composite with simultaneous pre- and postcomposition. -/
theorem comparisonHomMap
    {M M' N N' : SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat.{u} RingCat.{u})).obj R)} (f : M' ⟶ M) (g : N ⟶ N') :
    (Functor.uncurry.obj (homFunctor R)).map
      (X := (op M, N)) (Y := (op M', N')) (f.op, g) = homObjMap (R := R) f g := by
  change homObjMap (R := R) f (𝟙 N) ≫ homObjMap (R := R) (𝟙 M') g = _
  rw [homObjMap_comp_homObjMap, Category.id_comp, Category.id_comp]

/-- The actual Hom projection, from the named complex bifunctor to the native internal Hom.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node). -/
noncomputable def complexHomProjection
    (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor (R := R)).obj (op L)).obj M).X n ⟶
      homObj (R := R) (L.X p) (M.X q) :=
  homComplexπ L M n p q h

private theorem complexHomProjection_isLimit
    (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ) (n : ℤ) :
    Nonempty (IsLimit (Fan.mk ((((homComplexFunctor (R := R)).obj (op L)).obj M).X n)
      (fun p : ℤ ↦ complexHomProjection L M n p (p + n) rfl))) :=
  ⟨homComplexIsLimit L M n⟩

private theorem complexHomProjection_d
    (L M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
    (n m p q q' p' : ℤ) (hnm : n + 1 = m)
    (h : p + m = q) (h' : p + n = q') (h'' : p' + n = q) :
    (((homComplexFunctor (R := R)).obj (op L)).obj M).d n m ≫
        complexHomProjection L M m p q h =
      complexHomProjection L M n p q' h' ≫
        (Functor.uncurry.obj (homFunctor R)).map
          (X := (op (L.X p), M.X q')) (Y := (op (L.X p), M.X q))
          ((𝟙 _).op, M.d q' q) - n.negOnePow •
      (complexHomProjection L M n p' q h'' ≫
        (Functor.uncurry.obj (homFunctor R)).map
          (X := (op (L.X p'), M.X q)) (Y := (op (L.X p), M.X q))
          ((L.d p p').op, 𝟙 _)) := by
  refine (homComplex_d_π L M n m p q q' p' hnm h h' h'').trans ?_
  exact congrArg₂
    (fun (f : homObj (R := R) (L.X p) (M.X q') ⟶ homObj (R := R) (L.X p) (M.X q))
        (g : homObj (R := R) (L.X p') (M.X q) ⟶ homObj (R := R) (L.X p) (M.X q)) ↦
      homComplexπ L M n p q' h' ≫ f -
        n.negOnePow • (homComplexπ L M n p' q h'' ≫ g))
    (comparisonHomMap (𝟙 (L.X p)) (M.d q' q)).symm
    (comparisonHomMap (L.d p p') (𝟙 (M.X q))).symm

private theorem complexHomProjection_map
    {L L' M M' : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : L' ⟶ L) (g : M ⟶ M') (n p q : ℤ) (h : p + n = q) :
    ((((homComplexFunctor (R := R)).map f.op).app M) ≫
        ((homComplexFunctor (R := R)).obj (op L')).map g).f n ≫
          complexHomProjection L' M' n p q h =
      complexHomProjection L M n p q h ≫ (Functor.uncurry.obj (homFunctor R)).map
        (X := (op (L.X p), M.X q)) (Y := (op (L'.X p), M'.X q))
        ((f.f p).op, g.f q) := by
  refine (homComplexFunctor_map_f_π f g n p q h).trans ?_
  exact congrArg
    (fun k : homObj (R := R) (L.X p) (M.X q) ⟶ homObj (R := R) (L'.X p) (M'.X q) ↦
      homComplexπ L M n p q h ≫ k)
    (comparisonHomMap (f.f p) (g.f q)).symm

/-- A map in the contravariant input precomposes each product component.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node).
Proof: specialize the two-variable induced-map formula to the identity in the second
variable and identify the underived bifunctor map with the internal-Hom map. -/
theorem complexHomProjection_map_left
    {L L' M : CochainComplex (SheafOfModules.{u}
      ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ}
    (f : L' ⟶ L) (n p q : ℤ) (h : p + n = q) :
    (((homComplexFunctor (R := R)).map f.op).app M).f n ≫
        complexHomProjection L' M n p q h =
      complexHomProjection L M n p q h ≫
        homObjMap (R := R) (f.f p) (𝟙 (M.X q)) := by
  have hm := complexHomProjection_map f (𝟙 M) n p q h
  have hid := ((homComplexFunctor (R := R)).obj (op L')).map_id M
  rw [hid, Category.comp_id, comparisonHomMap, HomologicalComplex.id_f] at hm
  exact hm

attribute [irreducible] complexHomProjection

-- Checking the concrete Hom-component types needs this heartbeat budget.
/-- Restriction of the coefficient product complex has the normalized comparison.
Source: Stacks Project, Algebraization, Tag 099I; sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node).
Proof: restriction preserves products. Compose their projections with the underived
comparison and compare the two limiting product cones. Their projection equations
identify the differentials and the induced maps, giving a natural chain isomorphism
with the stated normalization. The explicit product data fixes the projection family. -/
theorem coefficientHomComplex_comparison
    (H : (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))ᵒᵖ ×
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R) ⥤
      SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B))
    (i : H ⋙ restrictScalars.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ) ≅
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).op.prod
        (𝟭 _) ⋙ Functor.uncurry.obj (homFunctor.{u, u, u, u} R))
    (G : (CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)ᵒᵖ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ ⥤
      CochainComplex (SheafOfModules.{u}
        ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
    (dG : ProductHomComplexData (Functor.curry.obj H) G) :
    ∃ e : Functor.uncurry.obj G ⋙
      (restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ) ≅
      ((restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
        ).mapHomologicalComplex (.up ℤ)).op.prod (𝟭 _) ⋙
        Functor.uncurry.obj (homComplexFunctor (R := R)),
      ∀ (L : CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj B)) ℤ)
        (M : CochainComplex (SheafOfModules.{u}
          ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) ℤ)
        (n p q : ℤ) (h : p + n = q),
        (e.hom.app (op L, M)).f n ≫
          complexHomProjection (((restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
              ).mapHomologicalComplex (.up ℤ)).obj L) M n p q h =
          (restrictScalars.{u}
            ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)).map
              (dG.π L M n p q h) ≫
            coefficientHomObjComparisonHom φ H i (op (L.X p), M.X q) := by
  let r := restrictScalars.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).map φ)
  have : PreservesLimitsOfSize.{u, u} r := coefficientRestriction_preservesLimits φ
  have : PreservesLimitsOfSize.{0, 0} r := preservesLimitsOfSize_shrink r
  exact genericUncurriedComplexComparison r H
    (SheafOfModules.homFunctor R) G (homComplexFunctor (R := R)) i dG
    (complexHomProjection (R := R)) complexHomProjection_isLimit
    complexHomProjection_d
    (fun L L' M M' f g n p q h ↦ complexHomProjection_map f g n p q h)

end NormalizedComparison

/-- Separate additivity supplies the product Hom-complex extension.
Source: Stacks Project, sites-cohomology.tex, Section 0A8X.
(auxiliary; not a blueprint node).
Proof: pointwise additivity in the contravariant variable gives additivity into the
functor category. Apply the existing bilinear product Hom-complex construction. -/
theorem extendProductFromSeparateAdditivity
    {A E : Type u} [Category.{v} A] [Category.{v} E]
    [Preadditive A] [Preadditive E] [HasProducts.{0} A]
    (H : Aᵒᵖ × E ⥤ A)
    (haddRight : ∀ N, ((Functor.curry.obj H).obj N).Additive)
    (haddLeft : ∀ N, ((Functor.curry.obj H).flip.obj N).Additive) :
    ∃ G : (CochainComplex A ℤ)ᵒᵖ ⥤ CochainComplex E ℤ ⥤ CochainComplex A ℤ,
      ProductHomComplexSpecification (Functor.curry.obj H) G := by
  have : ∀ N, ((Functor.curry.obj H).obj N).Additive := haddRight
  have : (Functor.curry.obj H).Additive := by
    constructor
    intro X Y f g
    apply NatTrans.ext
    funext N
    exact (haddLeft N).map_add
  exact exists_bilinearHomComplexFunctor (Functor.curry.obj H)

end SheafOfModules

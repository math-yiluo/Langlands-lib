/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHom
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
public import WeilConjectures.CategoryTheory.ProperBaseChange.BilinearHomComplexSupplement
public import WeilConjectures.Algebra.Homology.HomComplex
public import Mathlib.Algebra.Homology.Functor
public import WeilConjectures.Algebra.Homology.HomComplexComponents
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.CategoryTheory.Linear.LinearFunctor
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Generators
import Mathlib.CategoryTheory.Whiskering
public import WeilConjectures.AlgebraicGeometry.RestrictedCoefficientHomComplex

/-! # Coefficient Hom complexes over a ring-sheaf extension

Source: Stacks Project, Algebraization, Tag 099I
(blueprint: lem-weil-pbc-restricted-coefficient-hom-complex).
-/

-- After pruning, this module only keeps private declarations.
set_option linter.privateModule false

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

end SheafOfModules

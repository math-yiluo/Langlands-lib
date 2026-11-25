/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module
public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.AlgebraicGeometry.Modules.QuasicoherentKernel
import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
/-! Cycle projection comparison square.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square). -/
@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonCategoryCycle
    (X : Scheme.{u}) : Category X.Modules :=
  SheafOfModules.instCategory (R := X.ringCatSheaf)
local instance (priority := 2000) openOverHomComplexCycleProjectionComparisonPreadditiveCycle
    (X : Scheme.{u}) : Preadditive X.Modules :=
  SheafOfModules.instPreadditive X.ringCatSheaf
noncomputable local instance (priority := 2000)
    openOverHomComplexCycleProjectionComparisonAbelianCycle
    (X : Scheme.{u}) : Abelian X.Modules :=
  SheafOfModules.instAbelian X.ringCatSheaf
private theorem fan_iso {C : Type*} [Category C] {ι : Type*}
    {A B : C} {f g : ι → C} (π : ∀ i, A ⟶ f i) (τ : ∀ i, B ⟶ g i)
    (hπ : Limits.IsLimit (Limits.Fan.mk A π)) (hτ : Limits.IsLimit (Limits.Fan.mk B τ))
    (e : ∀ i, f i ≅ g i) :
    ∃ a : A ≅ B, ∀ i, a.hom ≫ τ i = π i ≫ (e i).hom := by
  let a := Limits.Fan.IsLimit.lift hτ (fun i ↦ π i ≫ (e i).hom)
  let b := Limits.Fan.IsLimit.lift hπ (fun i ↦ τ i ≫ (e i).inv)
  have ha (i) : a ≫ τ i = π i ≫ (e i).hom := Limits.Fan.IsLimit.fac hτ _ i
  have hb (i) : b ≫ π i = τ i ≫ (e i).inv := Limits.Fan.IsLimit.fac hπ _ i
  refine ⟨⟨a, b, ?_, ?_⟩, ha⟩
  · apply Limits.Fan.IsLimit.hom_ext hπ
    intro i
    change (a ≫ b) ≫ π i = (𝟙 A) ≫ π i
    rw [Category.assoc, hb, ← Category.assoc, ha, Category.assoc,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]
  · apply Limits.Fan.IsLimit.hom_ext hτ
    intro i
    change (b ≫ a) ≫ τ i = (𝟙 B) ≫ τ i
    rw [Category.assoc, ha, ← Category.assoc, hb, Category.assoc,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]

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
    (sa : F.obj A ⟶ A') (sb : F.obj B ⟶ B') (sc : F.obj E ⟶ E') (t : ℤ)
    (hH : dH ≫ c = a ≫ α - t • (b ≫ β))
    (hK : dK ≫ c' = a' ≫ α' - t • (b' ≫ β'))
    (ha : en ≫ a' = F.map a ≫ sa) (hb : en ≫ b' = F.map b ≫ sb)
    (hc : em ≫ c' = F.map c ≫ sc)
    (hα : F.map α ≫ sc = sa ≫ α') (hβ : F.map β ≫ sc = sb ≫ β') :
    (en ≫ dK) ≫ c' = (F.map dH ≫ em) ≫ c' := by
  simp only [Category.assoc, hK, Preadditive.comp_sub,
    Preadditive.comp_zsmul]
  rw [← Category.assoc en a', ha, Category.assoc,
    ← Category.assoc en b', hb, Category.assoc]
  rw [hc, ← Category.assoc (F.map dH), ← F.map_comp, hH]
  simp only [Functor.map_sub, Functor.map_zsmul, Functor.map_comp,
    Preadditive.sub_comp, Preadditive.zsmul_comp, Category.assoc, hα, hβ]

set_option backward.isDefEq.respectTransparency true in
/-- Restriction of a Hom complex has a chain isomorphism compatible with its projection.
Source: Stacks Project, Tags 0A8X and 08DL, product construction of the Hom complex.
(blueprint: new-t4-open-over-hom-complex-cycle-projection-comparison-cycle-square).
Proof: Restriction to an open preserves products, computed sectionwise, and passing
through the open-site equivalence preserves limits. Apply the universal properties
of the limiting product fans of the fixed Hom projections to the isomorphisms e.
This constructs mutually inverse degreewise maps, carrying every product projection
to its e comparison. To check the chain-map equation, compose with every projection:
the signed differential formula for Hom complexes reduces it to the two naturality
equations he and additivity of restriction. Thus the maps form a chain isomorphism.
Its projection identity at p = -n and q = 0 is the displayed equation. The same
argument applies to empty opens and unbounded complexes. -/
theorem openOver_homComplex_chain_projection_iso (X : Scheme.{u})
    (V : X.Opens) (W : V.toScheme.Opens)
    (e : ∀ M N : X.Modules,
      (Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
        V.toScheme.ringCatSheaf W).obj (SheafOfModules.homObj (R := X.sheaf) M N) ≅
      SheafOfModules.homObj (R := V.toScheme.sheaf.over W)
        ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
          V.toScheme.ringCatSheaf W).obj M)
        ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
          V.toScheme.ringCatSheaf W).obj N))
    (he : ∀ (M M' N N' : X.Modules) (f : M' ⟶ M) (g : N ⟶ N'),
      (Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
        V.toScheme.ringCatSheaf W).map (SheafOfModules.homObjMap
          (R := X.sheaf) f g) ≫ (e M' N').hom =
        (e M N).hom ≫ SheafOfModules.homObjMap
          (R := V.toScheme.sheaf.over W)
          ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
            V.toScheme.ringCatSheaf W).map f)
          ((Scheme.Modules.restrictFunctor V.ι ⋙ SheafOfModules.overFunctor
            V.toScheme.ringCatSheaf W).map g))
    (T J : CochainComplex X.Modules ℤ) (n : ℤ) :
    let F := Scheme.Modules.restrictFunctor V.ι ⋙
      SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
    let P := homComplex (R := X.sheaf) T J
    let A := (moduleOpenOverComplexFunctor X V W).obj T
    let K := (moduleOpenOverComplexFunctor X V W).obj J
    let Q := homComplex (R := V.toScheme.sheaf.over W) A K
    let π := (Classical.choose (homComplex_projections_exists
      (R := V.toScheme.sheaf.over W))) A K n (-n) 0 (by omega)
    ∃ h : (moduleOpenOverComplexFunctor X V W).obj P ≅ Q,
      h.hom.f n ≫ π = F.map (homologyEvaluationProjection X T J n) ≫
        (e (T.X (-n)) (J.X 0)).hom := by
  classical
  let F := Scheme.Modules.restrictFunctor V.ι ⋙
    SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
  let P := homComplex (R := X.sheaf) T J
  let A := (moduleOpenOverComplexFunctor X V W).obj T
  let K := (moduleOpenOverComplexFunctor X V W).obj J
  let Q := homComplex (R := V.toScheme.sheaf.over W) A K
  let π := Classical.choose (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))
  let τ := Classical.choose
    (homComplex_projections_exists.{u, u, u, u} (R := V.toScheme.sheaf.over W))
  have hπ := Classical.choose_spec (homComplex_projections_exists.{u, u, u, u} (R := X.sheaf))
  have hτ := Classical.choose_spec
    (homComplex_projections_exists.{u, u, u, u} (R := V.toScheme.sheaf.over W))
  let G := SheafOfModules.overFunctor V.toScheme.ringCatSheaf W
  let R := SheafOfModules.forget.{u} (V.toScheme.ringCatSheaf.over W) ⋙
    PresheafOfModules.toPresheaf (V.toScheme.ringCatSheaf.over W).obj
  have : PreservesLimitsOfShape (Discrete ℤ) (G ⋙ R) := by
    change PreservesLimitsOfShape (Discrete ℤ)
      ((SheafOfModules.forget.{u} V.toScheme.ringCatSheaf ⋙
        PresheafOfModules.toPresheaf V.toScheme.ringCatSheaf.obj) ⋙
        (Functor.whiskeringLeft _ _ _).obj (Over.forget W).op)
    infer_instance
  have : ReflectsLimitsOfShape (Discrete ℤ) R :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  have hG : PreservesLimitsOfShape (Discrete ℤ) G :=
    preservesLimitsOfShape_of_reflects_of_preserves _ R
  have : PreservesLimitsOfSize.{u, u} (Scheme.Modules.restrictFunctor V.ι) :=
    Scheme.Modules.preservesLimitsOfSize_restrictFunctor V.ι
  have : PreservesLimitsOfSize.{0, 0} (Scheme.Modules.restrictFunctor V.ι) :=
    preservesSmallestLimits_of_preservesLimits.{u, u} _
  have hRes : PreservesLimitsOfShape (Discrete ℤ)
      (Scheme.Modules.restrictFunctor V.ι) := by infer_instance
  have : PreservesLimitsOfShape (Discrete ℤ) F :=
    @comp_preservesLimitsOfShape _ _ _ _ (Discrete ℤ) _ _ _
      (Scheme.Modules.restrictFunctor V.ι) G hRes hG
  have hAddG : G.Additive := moduleOverFunctor_additive V.toScheme.toRingedSpace W
  have hAddRes : (Scheme.Modules.restrictFunctor V.ι).Additive := by infer_instance
  have : F.Additive := @Functor.instAdditiveComp _ _ _ _ _ _
    (Scheme.Modules.restrictFunctor V.ι) hAddRes _ _ _ G hAddG
  have hp (i : ℤ) : IsLimit (Fan.mk (F.obj (P.X i))
      (fun p : ℤ ↦ F.map (π T J i p (p + i) rfl))) :=
    isLimitFanMkObjOfIsLimit F _ _ (Classical.choice (hπ.1 T J i))
  have ht (i : ℤ) : IsLimit (Fan.mk (Q.X i)
      (fun p : ℤ ↦ τ A K i p (p + i) rfl)) := Classical.choice (hτ.1 A K i)
  have hi (i : ℤ) := fan_iso _ _ (hp i) (ht i)
    (fun p : ℤ ↦ e (T.X p) (J.X (p + i)))
  choose a ha using hi
  have ha' (i p q : ℤ) (hpq : p + i = q) :
      (a i).hom ≫ τ A K i p q hpq =
        F.map (π T J i p q hpq) ≫ (e (T.X p) (J.X q)).hom := by
    subst q
    exact ha i p
  have comm (i j : ℤ) (hij : i + 1 = j) :
      (a i).hom ≫ Q.d i j = F.map (P.d i j) ≫ (a j).hom := by
    apply (hτ.1 A K j).some.hom_ext
    intro l
    obtain ⟨p⟩ := l
    change ((a i).hom ≫ Q.d i j) ≫ τ A K j p (p + j) rfl =
      (F.map (P.d i j) ≫ (a j).hom) ≫ τ A K j p (p + j) rfl
    have hH := hπ.2.1 T J i j p (p + j) (p + i) (p + 1)
      hij rfl rfl (by omega)
    have hQ := hτ.2.1 A K i j p (p + j) (p + i) (p + 1)
      hij rfl rfl (by omega)
    have hα := he (T.X p) (T.X p) (J.X (p + i)) (J.X (p + j))
      (𝟙 _) (J.d (p + i) (p + j))
    have hβ := he (T.X (p + 1)) (T.X p) (J.X (p + j)) (J.X (p + j))
      (T.d p (p + 1)) (𝟙 _)
    set_option backward.isDefEq.respectTransparency false in
      simp only [Functor.map_id] at hα hβ
    change P.d i j ≫ π T J j p (p + j) rfl = _ at hH
    change Q.d i j ≫ τ A K j p (p + j) rfl = _ at hQ
    simp only [Units.smul_def] at hH hQ
    exact factor_differential F (P.d i j) (Q.d i j)
      (π T J i p (p + i) rfl) (π T J i (p + 1) (p + j) (by omega))
      (π T J j p (p + j) rfl)
      (SheafOfModules.homObjMap (R := X.sheaf) (𝟙 (T.X p))
        (J.d (p + i) (p + j)))
      (SheafOfModules.homObjMap (R := X.sheaf) (T.d p (p + 1)) (𝟙 (J.X (p + j))))
      (τ A K i p (p + i) rfl) (τ A K i (p + 1) (p + j) (by omega))
      (τ A K j p (p + j) rfl)
      (SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W) (𝟙 (A.X p))
        (K.d (p + i) (p + j)))
      (SheafOfModules.homObjMap (R := V.toScheme.sheaf.over W)
        (A.d p (p + 1)) (𝟙 (K.X (p + j))))
      (a i).hom (a j).hom
      (e (T.X p) (J.X (p + i))).hom
      (e (T.X (p + 1)) (J.X (p + j))).hom
      (e (T.X p) (J.X (p + j))).hom (i.negOnePow : ℤ)
      hH hQ (ha' i p (p + i) rfl) (ha' i (p + 1) (p + j) (by omega))
      (ha' j p (p + j) rfl) hα hβ
  let h : (moduleOpenOverComplexFunctor X V W).obj P ≅ Q :=
    HomologicalComplex.Hom.isoOfComponents a comm
  refine ⟨h, ?_⟩
  exact ha' n (-n) 0 (by omega)
end CategoryTheory

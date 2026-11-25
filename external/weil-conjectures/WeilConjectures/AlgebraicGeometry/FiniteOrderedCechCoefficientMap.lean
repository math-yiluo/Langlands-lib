/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AlternatingCechTotalComplex

/-! # The coefficient map into the ordered Čech total complex

Source: Stacks Project, Cohomology, Tags 01EQ and 01ET.
(auxiliary; not a blueprint node)
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {X : Scheme.{u}} {r : ℕ} (V : Fin r → X.Opens)
  {F : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
  {G : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
  (e : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
    (.up ℤ) 0).obj F ⟶ G)

private theorem coefficient_closed : e.f 0 ≫ G.d 0 1 = 0 := by
  rw [e.comm]
  simp

/-- The coefficient components satisfy the cochain identity.
Source: Stacks Project, Tag 01EQ.
(auxiliary; not a blueprint node)
Proof: the horizontal identity is functoriality of the Čech functor and the
vertical term vanishes by the augmentation cochain identity. -/
theorem coefficient_comm (n m : ℤ) :
    (((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
      ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) n 0 n (Int.add_zero n)) ≫
        ((alternatingCechTotalFunctor V).obj G).d n m =
      ((alternatingCechModuleFunctor V).obj F).d n m ≫
        (((alternatingCechModuleFunctor V).map (e.f 0)).f m ≫
          ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) m 0 m
            (Int.add_zero m)) := by
  by_cases h : n + 1 = m
  · subst m
    let B := (alternatingCechDoubleFunctor V).obj G
    change (((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
      B.ιTotal (.up ℤ) n 0 n (Int.add_zero n)) ≫ (B.total (.up ℤ)).d n (n + 1) = _
    rw [Category.assoc, HomologicalComplex₂.total_d, Preadditive.comp_add,
      HomologicalComplex₂.ι_D₁, HomologicalComplex₂.ι_D₂,
      HomologicalComplex₂.d₁_eq' _ _ (i₁' := n + 1) (by simp),
      HomologicalComplex₂.d₂_eq _ _ n (i₂' := 1) (by simp) _ (by simp)]
    have hs : ComplexShape.ε₁ (.up ℤ) (.up ℤ) (.up ℤ) (n, 0) = 1 := rfl
    simp only [hs, one_smul, Preadditive.comp_add]
    rw [← Category.assoc]
    change (((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
      ((alternatingCechModuleFunctor V).obj (G.X 0)).d n (n + 1)) ≫ _ + _ = _
    rw [((alternatingCechModuleFunctor V).map (e.f 0)).comm]
    simp only [Category.assoc]
    suffices hz : ((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
        (ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (n, 0) •
          (((alternatingCechModuleFunctor V).map (G.d 0 1)).f n ≫
            B.ιTotal (.up ℤ) n 1 (n + 1) (by simp))) = 0 by
      erw [hz]
      simp only [add_zero]
      erw [HomologicalComplex₂.ιTotalOrZero_eq _ _ _ _ _ (by simp)]
      rfl
    have hzero : ((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
        ((alternatingCechModuleFunctor V).map (G.d 0 1)).f n = 0 := by
      rw [← HomologicalComplex.comp_f, ← Functor.map_comp, coefficient_closed,
        Functor.map_zero, HomologicalComplex.zero_f]
    let f := ((alternatingCechModuleFunctor V).map (e.f 0)).f n
    let g := ((alternatingCechModuleFunctor V).map (G.d 0 1)).f n
    let t : ((alternatingCechModuleFunctor V).obj (G.X 1)).X n ⟶
        (B.total (.up ℤ)).X (n + 1) := B.ιTotal (.up ℤ) n 1 (n + 1) (by simp)
    let s := ComplexShape.ε₂ (.up ℤ) (.up ℤ) (.up ℤ) (n, 0)
    change f ≫ (s • (g ≫ t)) = 0
    calc
      _ = s • ((f ≫ g) ≫ t) := (Linear.comp_units_smul f s (g ≫ t)).trans
        (congrArg (fun k ↦ s • k) (Category.assoc f g t).symm)
      _ = s • (0 ≫ t) := congrArg (fun k ↦ s • (k ≫ t)) hzero
      _ = 0 := by simp only [zero_comp, smul_zero]
  · rw [HomologicalComplex.shape ((alternatingCechTotalFunctor V).obj G) n m h,
      HomologicalComplex.shape ((alternatingCechModuleFunctor V).obj F) n m h]
    simp

/-- The coefficient augmentation into the resolution-degree-zero summands.
Source: Stacks Project, Tag 01EQ.
(auxiliary; not a blueprint node) -/
def orderedCechCoefficientMap :
    (alternatingCechModuleFunctor V).obj F ⟶ (alternatingCechTotalFunctor V).obj G where
  f n := ((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
    ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) n 0 n (Int.add_zero n)
  comm' n m _ := coefficient_comm V e n m

/-- The coefficient map commutes with maps respecting coefficient augmentations.
Source: Stacks Project, Tag 01EQ, componentwise functoriality.
(auxiliary; not a blueprint node)
Proof: apply the coefficient augmentation identity in every Čech degree, and
use the naturality of each total summand inclusion. -/
theorem orderedCechCoefficientMap_naturality
    {F' : SheafOfModules.{u} (moduleRings X.toRingedSpace)}
    {G' : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ}
    (e' : (HomologicalComplex.single (SheafOfModules.{u} (moduleRings X.toRingedSpace))
      (.up ℤ) 0).obj F' ⟶ G')
    (a : F ⟶ F') (v : G ⟶ G') (h : e.f 0 ≫ v.f 0 = a ≫ e'.f 0) :
    orderedCechCoefficientMap V e ≫ (alternatingCechTotalFunctor V).map v =
      (alternatingCechModuleFunctor V).map a ≫ orderedCechCoefficientMap V e' := by
  apply HomologicalComplex.hom_ext
  intro n
  dsimp only [orderedCechCoefficientMap, HomologicalComplex.comp_f]
  change (((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
    ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) n 0 n (Int.add_zero n)) ≫
      (HomologicalComplex₂.total.map ((alternatingCechDoubleFunctor V).map v)
        (.up ℤ)).f n =
    ((alternatingCechModuleFunctor V).map a).f n ≫
      (((alternatingCechModuleFunctor V).map (e'.f 0)).f n ≫
        ((alternatingCechDoubleFunctor V).obj G').ιTotal (.up ℤ) n 0 n (Int.add_zero n))
  rw [Category.assoc, HomologicalComplex₂.ιTotal_map, ← Category.assoc,
    ← Category.assoc]
  change (((alternatingCechModuleFunctor V).map (e.f 0)).f n ≫
    ((alternatingCechModuleFunctor V).map (v.f 0)).f n) ≫ _ = _
  rw [← HomologicalComplex.comp_f, ← Functor.map_comp, h, Functor.map_comp,
    HomologicalComplex.comp_f]

/-- The two coefficient augmentations agree in degree zero.
Source: Stacks Project, Tag 01EQ.
(auxiliary; not a blueprint node)
Proof: the global restriction map is natural for e in degree zero. Compose
this equality with the common (0,0) inclusion into the total. -/
theorem orderedCechCoefficientMap_zero :
    (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (e.f 0) ≫
      (alternatingCechAugmentationMap V G).f 0 =
        alternatingCechZero V F ≫ (orderedCechCoefficientMap V e).f 0 := by
  have hzero {M N : SheafOfModules.{u} (moduleRings X.toRingedSpace)} (g : M ⟶ N) :
      (RingedSpace.globalSectionsFunctor X.toRingedSpace).map g ≫ alternatingCechZero V N =
        alternatingCechZero V M ≫ ((alternatingCechModuleFunctor V).map g).f 0 := by
    have hpresheaf
        {P Q : X.Opensᵒᵖ ⥤ ModuleCat.{u} ((moduleRings X.toRingedSpace).obj.obj (op ⊤))}
        (a : P ⟶ Q) :
        a.app (op ⊤) ≫ alternatingCechPresheafZero V Q =
          alternatingCechPresheafZero V P ≫ alternatingCechTermsMap V a 0 := by
      apply ModuleCat.hom_ext
      apply LinearMap.ext
      intro s
      funext t
      exact congrArg (fun f ↦ f.hom s)
        (a.naturality (homOfLE (le_top (a := alternatingCechIntersection V t))).op).symm
    unfold alternatingCechZero
    change _ = _ ≫ (HomologicalComplex.extendMap
      (alternatingCechComplexMap V ((alternatingCechModulePresheaf (X := X)).map g))
        ComplexShape.embeddingUpNat).f 0
    erw [HomologicalComplex.extendMap_f _ _ (i := 0) (i' := 0) rfl]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    dsimp only [alternatingCechComplexMap, CochainComplex.ofHom]
    erw [← Category.assoc (alternatingCechPresheafZero V
      ((alternatingCechModulePresheaf (X := X)).obj M))
        (alternatingCechTermsMap V ((alternatingCechModulePresheaf (X := X)).map g) 0)]
    erw [← hpresheaf]
    simp only [← Category.assoc]
    congr 1
  dsimp only [orderedCechCoefficientMap]
  change (RingedSpace.globalSectionsFunctor X.toRingedSpace).map (e.f 0) ≫
      (alternatingCechZero V (G.X 0) ≫
        ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) 0 0 0 (Int.zero_add 0)) =
    alternatingCechZero V F ≫
      (((alternatingCechModuleFunctor V).map (e.f 0)).f 0 ≫
        ((alternatingCechDoubleFunctor V).obj G).ιTotal (.up ℤ) 0 0 0 (Int.add_zero 0))
  rw [← Category.assoc, hzero, Category.assoc]
  rfl

/-- Totalization of a single coefficient sheaf is its Čech complex.
Source: Stacks Project, Tag 01EQ, the resolution-degree-zero axis.
(auxiliary; not a blueprint node)
Proof: all summands off resolution degree zero are zero. Projection onto the
sole remaining summand in each total degree inverts its total inclusion. -/
theorem orderedCechCoefficientMap_single_isIso
    (M : SheafOfModules.{u} (moduleRings X.toRingedSpace)) :
    IsIso (orderedCechCoefficientMap V
      (𝟙 ((HomologicalComplex.single
        (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj M))) := by
  let S := (HomologicalComplex.single
    (SheafOfModules.{u} (moduleRings X.toRingedSpace)) (.up ℤ) 0).obj M
  let B := (alternatingCechDoubleFunctor V).obj S
  suffices hc : ∀ n : ℤ, IsIso ((orderedCechCoefficientMap V (𝟙 S)).f n) by
    have := hc
    exact HomologicalComplex.Hom.isIso_of_components _
  intro n
  have he : (orderedCechCoefficientMap V (𝟙 S)).f n =
      B.ιTotal (.up ℤ) n 0 n (Int.add_zero n) := by
    dsimp only [orderedCechCoefficientMap]
    change ((alternatingCechModuleFunctor V).map (𝟙 M)).f n ≫ _ = _
    erw [(alternatingCechModuleFunctor V).map_id M]
    simp only [HomologicalComplex.id_f, Category.id_comp]
    rfl
  rw [he]
  let a : (B.total (.up ℤ)).X n ⟶ ((alternatingCechModuleFunctor V).obj M).X n :=
    B.totalDesc (fun p q h ↦ if hq : q = 0 then by
      subst q
      exact (((alternatingCechModuleFunctor V).obj M).XIsoOfEq
        (by simpa using h)).hom
    else 0)
  refine ⟨a, ?_, ?_⟩
  · simp [a]
  · apply HomologicalComplex₂.total.hom_ext
    intro p q h
    by_cases hq : q = 0
    · subst q
      have hp : p = n := by simpa using h
      subst p
      change B.ιTotal (.up ℤ) n 0 n h ≫ a ≫
        B.ιTotal (.up ℤ) n 0 n (Int.add_zero n) = B.ιTotal (.up ℤ) n 0 n h ≫ 𝟙 _
      rw [← Category.assoc]
      have ha : B.ιTotal (.up ℤ) n 0 n h ≫ a = 𝟙 _ := by
        simp [a]
        rfl
      rw [ha, Category.id_comp, Category.comp_id]
    · have hz : IsZero ((B.X p).X q) := by
        change IsZero (((alternatingCechModuleFunctor V).obj (S.X q)).X p)
        exact (HomologicalComplex.eval _ (.up ℤ) p).map_isZero
          ((alternatingCechModuleFunctor V).map_isZero
            (HomologicalComplex.isZero_single_obj_X (.up ℤ) 0 M q hq))
      exact hz.eq_of_src _ _

end
end AlgebraicGeometry

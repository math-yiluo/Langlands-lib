/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.CondensedLocalCoefficientAdjoints
public import WeilConjectures.CategoryTheory.ModuleObjects.Free
import all WeilConjectures.AlgebraicGeometry.CondensedCoefficientComplexColimit
import all WeilConjectures.AlgebraicGeometry.CondensedConstructibleSerre
import WeilConjectures.AlgebraicGeometry.CondensedFpHomStage
import all WeilConjectures.AlgebraicGeometry.CondensedOverlapFactorTranspose

/-!
# One-way finite coefficient factorization on a finite family of qcqs schemes

Source: archived ModuleObject/Colimit/TwoColimit.lean, (Obj) overlap descent paragraph.
(auxiliary; not a blueprint node).
-/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

attribute [local instance] sheafMonoidalCategory sheafBraidedCategory
open MonObj

set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] upperStar lowerStar upperStarFromPoint
  upperStarLowerStarAdjunction overlapComparison componentComparison

section UnderlyingMaps
variable {C D : Type*} [Category C] [Category D]
  [MonoidalCategory C] [MonoidalCategory D]

private lemma extendedCocone_leg_hom {J : Type*} [Category J]
    {R : C} [MonObj R] {K : J ⥤ Mod C R}
    (c : Cocone K) {N : Mod C R} (e : c.pt ⟶ N) (i : J) :
    ((c.extend e).ι.app i).hom = (c.ι.app i).hom ≫ e.hom := rfl

private lemma comap_mapMap_hom (F : C ⥤ D) [F.LaxMonoidal]
    {R S : C} [MonObj R] [MonObj S] (χ : R ⟶ S) [IsMonHom χ]
    {P : Mod D (F.obj S)} (M : Mod C S) (a : P ⟶ (F.mapMod S).obj M) :
    ((Mod.comap (F.map χ)).map a ≫ (F.mapModComapIso χ).inv.app M).hom = a.hom := by
  simp only [Mod.comp_hom', Mod.comap_map_hom,
    CategoryTheory.Functor.mapModComapIso_inv_app_hom]
  exact Category.comp_id _

private noncomputable def comapCocone_isColimit
    {R S : C} [MonObj R] [MonObj S] (χ : R ⟶ S) [IsMonHom χ] [IsIso χ]
    {J : Type (u + 1)} [SmallCategory J]
    {K : J ⥤ Mod C S} (c : Cocone K) (hc : IsColimit c) :
    IsColimit ((Mod.comap χ).mapCocone c) := by
  let : PreservesColimitsOfSize.{u + 1, u + 1} (Mod.comap χ) :=
    (Mod.comapEquivalenceOfIsIso χ).toAdjunction.leftAdjoint_preservesColimits
  exact isColimitOfPreserves _ hc

private noncomputable def mapModCocone_isColimit
    (F : C ⥤ D) (G : D ⥤ C) [F.Monoidal] [G.LaxMonoidal]
    (adj : F ⊣ G) [adj.IsMonoidal]
    (R : C) [MonObj R] {J : Type (u + 1)} [SmallCategory J]
    {K : J ⥤ Mod C R} (c : Cocone K) (hc : IsColimit c) :
    IsColimit ((F.mapMod R).mapCocone c) := by
  let : (F.mapMod R).IsLeftAdjoint := ⟨_, ⟨adj.mapModAdjunction R⟩⟩
  exact isColimitOfPreserves _ hc

private lemma mappedCocone_leg_hom {J : Type*} [Category J]
    (F : C ⥤ D) [F.LaxMonoidal] (R : C) [MonObj R]
    {K : J ⥤ Mod C R} (c : Cocone K) (i : J) :
    (((F.mapMod R).mapCocone c).ι.app i).hom = F.map (c.ι.app i).hom := rfl

private lemma restrictedCocone_leg_hom {J : Type*} [Category J]
    {R S : C} [MonObj R] [MonObj S] (χ : R ⟶ S) [IsMonHom χ]
    {K : J ⥤ Mod C S} (c : Cocone K) (i : J) :
    (((Mod.comap χ).mapCocone c).ι.app i).hom = (c.ι.app i).hom := rfl

end UnderlyingMaps

section ScalarColimit
open MonoidalCategory
variable {C : Type (u + 2)} [Category.{u + 1} C] [MonoidalCategory C]
  [BraidedCategory C] [HasCoequalizers C]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfSize.{0, 0} (tensorRight Z)]
  {J : Type (u + 1)} [SmallCategory J] [HasColimitsOfShape J C]
  [∀ Z : C, PreservesColimitsOfShape J (tensorLeft Z)]
  [∀ Z : C, PreservesColimitsOfShape J (tensorRight Z)]
  (D : J ⥤ C)
  [∀ i, MonObj (D.obj i)] [∀ {i j} (a : i ⟶ j), IsMonHom (D.map a)]
  (c : Cocone D) [MonObj c.pt] [∀ i, IsMonHom (show D.obj i ⟶ c.pt from c.ι.app i)]
  {R : C} [MonObj R] [IsCommMonObj R]
  (φ : ∀ i, R ⟶ D.obj i) [∀ i, IsMonHom (φ i)]
  (χ : R ⟶ c.pt) [IsMonHom χ]
  (hφ : ∀ {i j} (a : i ⟶ j), φ i ≫ D.map a = φ j)
  (hχ : ∀ i, φ i ≫ c.ι.app i = χ)
  (Q : Mod (C) R)

private noncomputable def scalarDiagram :
    J ⥤ Mod (C) R where
  obj i := (Mod.comap (φ i)).obj ((Mod.extendScalars (φ i)).obj Q)
  map {i j} a := Mod.mixedScalarMap (φ i) (φ j) (φ i) (φ j) (D.map a)
    (hφ a) (hφ a) Q
  map_id i := by
    simp only [D.map_id]
    exact Mod.mixedScalarMap_id (φ i) (φ i) Q
  map_comp a b := by
    apply Mod.hom_ext
    apply (cancel_epi (Mod.extendπ (φ _) Q)).mp
    simp only [Mod.comp_hom', Mod.extendπ_mixedScalarMap_assoc,
      Mod.extendπ_mixedScalarMap, D.map_comp, comp_whiskerRight_assoc]

private noncomputable def scalarCocone :
    Cocone (scalarDiagram D φ hφ Q) where
  pt := (Mod.comap χ).obj ((Mod.extendScalars χ).obj Q)
  «ι» :=
    { app i := Mod.mixedScalarMap (φ i) χ (φ i) χ (c.ι.app i) (hχ i) (hχ i) Q
      naturality i j a := by
        change Mod.mixedScalarMap (φ i) (φ j) (φ i) (φ j) (D.map a)
          (hφ a) (hφ a) Q ≫ _ = _ ≫ 𝟙 _
        apply Mod.hom_ext
        apply (cancel_epi (Mod.extendπ (φ i) Q)).mp
        simp only [Mod.comp_hom', Category.comp_id,
          Mod.extendπ_mixedScalarMap_assoc, Mod.extendπ_mixedScalarMap,
          ← comp_whiskerRight_assoc, c.w] }

private noncomputable def scalarCocone_isColimit (hc : IsColimit c) :
    IsColimit (scalarCocone D c φ χ hφ hχ Q) := by
  apply isColimitOfReflects (Mod.forget R)
  let M := Q.X
  let S := c.pt
  let c₁ := (tensorRight M).mapCocone c
  let c₀ := (tensorRight M).mapCocone ((tensorRight R).mapCocone c)
  let K := scalarDiagram D φ hφ Q ⋙ Mod.forget R
  let cc : Cocone K := (Mod.forget R).mapCocone (scalarCocone D c φ χ hφ hχ Q)
  let q : c₁.pt ⟶ cc.pt := Mod.extendπ χ Q
  let qi : (D ⋙ tensorRight M) ⟶ K :=
    { app i := Mod.extendπ (φ i) Q
      naturality i j a := by
        exact (Mod.extendπ_mixedScalarMap
          (φ i) (φ j) (φ i) (φ j) (D.map a) (hφ a) (hφ a) Q).symm }
  have hqi (i : J) : Epi (qi.app i) := by
    dsimp [qi]
    infer_instance
  let f : c₀.pt ⟶ c₁.pt := (S ◁ χ ≫ μ[S]) ▷ M
  let g : c₀.pt ⟶ c₁.pt := (α_ S R M).hom ≫ S ◁ γ[R,M]
  let fi (i : J) : ((D.obj i ⊗ R) ⊗ M) ⟶ (D.obj i ⊗ M) :=
    (D.obj i ◁ φ i ≫ μ[D.obj i]) ▷ M
  let gi (i : J) : ((D.obj i ⊗ R) ⊗ M) ⟶ (D.obj i ⊗ M) :=
    (α_ (D.obj i) R M).hom ≫ D.obj i ◁ γ[R,M]
  have hq : f ≫ q = g ≫ q := Mod.extendπ_condition χ Q
  refine coequalizer_colimit _ _ K c₀ c₁ cc
    (isColimitOfPreserves _ (isColimitOfPreserves _ hc))
    (isColimitOfPreserves _ hc) f g fi gi qi q hq
    (Mod.isColimitExtendπ χ Q) ?_ ?_ ?_ ?_
  · intro i
    change ((c.ι.app i) ▷ R) ▷ M ≫ ((S ◁ χ ≫ μ[S]) ▷ M) =
      ((D.obj i ◁ φ i ≫ μ[D.obj i]) ▷ M) ≫ (c.ι.app i) ▷ M
    rw [← comp_whiskerRight, ← comp_whiskerRight]
    congr 1
    erw [← hχ i, whiskerLeft_comp, Category.assoc, ← whisker_exchange_assoc,
      ← tensorHom_def_assoc, ← IsMonHom.mul_hom, ← Category.assoc]
  · intro i
    change ((c.ι.app i) ▷ R) ▷ M ≫ (α_ S R M).hom ≫ S ◁ γ[R,M] =
      ((α_ (D.obj i) R M).hom ≫ D.obj i ◁ γ[R,M]) ≫ (c.ι.app i) ▷ M
    erw [associator_naturality_left_assoc, Category.assoc, ← whisker_exchange]
  · intro i
    exact Mod.extendπ_condition _ Q
  · intro i
    exact (Mod.extendπ_mixedScalarMap
      (φ i) χ (φ i) χ (c.ι.app i) (hχ i) (hχ i) Q).symm

end ScalarColimit

private abbrev CoeffIndex (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) := AsSmall.{u + 1} (Under E)

private noncomputable def coeffIndexFunctor (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) :
    CoeffIndex.{u} ℓ E ⥤ PadicAlgCl.FiniteIntermediateField ℓ :=
  (AsSmall.equiv (C := Under E)).inverse ⋙ Under.forget E

private lemma coeffIndex_le (ℓ : ℕ) [Fact ℓ.Prime]
    (E : PadicAlgCl.FiniteIntermediateField ℓ) (i : CoeffIndex.{u} ℓ E) :
    E ≤ (coeffIndexFunctor ℓ E).obj i := leOfHom (ULift.down i).hom

section RawCoefficients
variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : PadicAlgCl.FiniteIntermediateField ℓ) (Y : Scheme.{u}) (g : Y ⟶ X)

private noncomputable def rawRingDiagram :
    CoeffIndex.{u} ℓ E ⥤ Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1} :=
  ((coeffIndexFunctor ℓ E ⋙ Profinite.padicSubfieldRingObjFunctor ℓ) ⋙
    upperStarFromPoint T) ⋙ upperStar Ab.{u + 1} f ⋙ upperStar Ab.{u + 1} g

private noncomputable instance rawRingDiagramMon (i : CoeffIndex.{u} ℓ E) :
    MonObj ((rawRingDiagram T X f ℓ E Y g).obj i) :=
  inferInstanceAs (MonObj ((upperStar Ab.{u + 1} g).obj
    ((upperStar Ab.{u + 1} f).obj
      (padicSubfieldRingObj T ℓ ((coeffIndexFunctor ℓ E).obj i)))))

private instance rawRingDiagramHom {i j : CoeffIndex.{u} ℓ E} (a : i ⟶ j) :
    IsMonHom ((rawRingDiagram T X f ℓ E Y g).map a) :=
  inferInstanceAs (IsMonHom ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjMap T ℓ (leOfHom ((coeffIndexFunctor ℓ E).map a))))))

private noncomputable def rawRingCocone : Cocone (rawRingDiagram T X f ℓ E Y g) :=
  (upperStar Ab.{u + 1} g).mapCocone ((upperStar Ab.{u + 1} f).mapCocone
    ((padicAlgClRingObjCocone T ℓ).whisker (coeffIndexFunctor ℓ E)))

private noncomputable instance rawRingCoconeMon :
    MonObj (rawRingCocone T X f ℓ E Y g).pt :=
  inferInstanceAs (MonObj ((upperStar Ab.{u + 1} g).obj
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))))

private instance rawRingCoconeHom (i : CoeffIndex.{u} ℓ E) :
    IsMonHom (show (rawRingDiagram T X f ℓ E Y g).obj i ⟶
      (rawRingCocone T X f ℓ E Y g).pt from
        (rawRingCocone T X f ℓ E Y g).ι.app i) :=
  inferInstanceAs (IsMonHom ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ ((coeffIndexFunctor ℓ E).obj i)))))

private noncomputable def rawRingCocone_isColimit :
    IsColimit (rawRingCocone T X f ℓ E Y g) := by
  have : (coeffIndexFunctor.{u} ℓ E).Final := by
    dsimp only [coeffIndexFunctor]
    infer_instance
  exact isColimitOfPreserves _ (isColimitOfPreserves _
    ((CategoryTheory.Functor.Final.isColimitWhiskerEquiv (coeffIndexFunctor ℓ E) _).symm
      (isColimitPadicAlgClRingObjCocone T ℓ)))

private noncomputable def rawScalarMap (i : CoeffIndex.{u} ℓ E) :
    (upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)) ⟶
        (rawRingDiagram T X f ℓ E Y g).obj i :=
  (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
    (padicSubfieldRingObjMap T ℓ (coeffIndex_le ℓ E i)))

private instance rawScalarMapHom (i : CoeffIndex.{u} ℓ E) :
    IsMonHom (rawScalarMap T X f ℓ E Y g i) :=
  inferInstanceAs (IsMonHom ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjMap T ℓ (coeffIndex_le ℓ E i)))))

private lemma rawScalarMap_naturality {i j : CoeffIndex.{u} ℓ E} (a : i ⟶ j) :
    rawScalarMap T X f ℓ E Y g i ≫ (rawRingDiagram T X f ℓ E Y g).map a =
      rawScalarMap T X f ℓ E Y g j := by
  change (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
    (padicSubfieldRingObjMap T ℓ (coeffIndex_le ℓ E i))) ≫
      (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjMap T ℓ (leOfHom ((coeffIndexFunctor ℓ E).map a)))) =
    (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjMap T ℓ (coeffIndex_le ℓ E j)))
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    padicSubfieldRingObjMap_comp_padicSubfieldRingObjMap]

private lemma rawScalarMap_toAlgCl (i : CoeffIndex.{u} ℓ E) :
    rawScalarMap T X f ℓ E Y g i ≫ (rawRingCocone T X f ℓ E Y g).ι.app i =
      (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E)) := by
  change (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
    (padicSubfieldRingObjMap T ℓ (coeffIndex_le ℓ E i))) ≫
      (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ ((coeffIndexFunctor ℓ E).obj i))) = _
  rw [← CategoryTheory.Functor.map_comp, ← CategoryTheory.Functor.map_comp,
    padicSubfieldRingObjMap_comp_toPadicAlgCl]

variable (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
  ((upperStar Ab.{u + 1} g).obj
    ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))

private noncomputable def rawScalarDiagram :=
  scalarDiagram (rawRingDiagram T X f ℓ E Y g) (rawScalarMap T X f ℓ E Y g)
    (fun {_ _} a ↦ rawScalarMap_naturality T X f ℓ E Y g a) P

private noncomputable def rawScalarCocone : Cocone (rawScalarDiagram T X f ℓ E Y g P) := by
  have : IsMonHom (show _ ⟶ (rawRingCocone T X f ℓ E Y g).pt from
      (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E))) :=
    inferInstanceAs (IsMonHom ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))))
  exact scalarCocone (rawRingDiagram T X f ℓ E Y g) (rawRingCocone T X f ℓ E Y g)
    (rawScalarMap T X f ℓ E Y g)
    ((upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
      (padicSubfieldRingObjToPadicAlgCl T ℓ E)))
    (fun {_ _} a ↦ rawScalarMap_naturality T X f ℓ E Y g a)
    (rawScalarMap_toAlgCl T X f ℓ E Y g) P

private noncomputable def rawScalarCocone_isColimit :
    IsColimit (rawScalarCocone T X f ℓ E Y g P) := by
  have : IsMonHom (show _ ⟶ (rawRingCocone T X f ℓ E Y g).pt from
      (upperStar Ab.{u + 1} g).map ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ E))) :=
    inferInstanceAs (IsMonHom ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))))
  exact scalarCocone_isColimit _ _ _ _ _ _ P (rawRingCocone_isColimit T X f ℓ E Y g)

end RawCoefficients

section LocalColimit
variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (Y : Scheme.{u}) (g : Y ⟶ X)
  (P : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
  (a : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj P ≅
      ((upperStar Ab.{u + 1} g).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M)

private noncomputable def localScalarCocone :=
  (rawScalarCocone T X f ℓ E Y g P).extend
    ((Mod.comap ((upperStar Ab.{u + 1} g).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).map a.hom ≫
        ((upperStar Ab.{u + 1} g).mapModComapIso
          ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ E))).inv.app M)

private noncomputable def localScalarCocone_isColimit :
    IsColimit (localScalarCocone T X f ℓ E Y g P M a) :=
  IsColimit.extendIso _ (rawScalarCocone_isColimit T X f ℓ E Y g P)

private lemma localScalarCocone_leg (k : CoeffIndex ℓ E) :
    ((localScalarCocone T X f ℓ E Y g P M a).ι.app k).hom =
      (finiteCoefficientLocalAdjoint T X f ℓ E Y g P M a.hom
        ((coeffIndexFunctor ℓ E).obj k) (coeffIndex_le ℓ E k)).hom := by
  rw [localAdjoint_eq_mixed]
  unfold localScalarCocone
  rw [extendedCocone_leg_hom, comap_mapMap_hom]
  rfl

private noncomputable def localOriginalAdjoint :
    P ⟶ ((upperStar Ab.{u + 1} g).mapMod
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))).obj
        ((Mod.comap ((upperStar Ab.{u + 1} f).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M) :=
  (Mod.extendRestrictAdjunction ((upperStar Ab.{u + 1} g).map
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).homEquiv _ _
      a.hom ≫
        ((upperStar Ab.{u + 1} g).mapModComapIso
          ((upperStar Ab.{u + 1} f).map
            (padicSubfieldRingObjToPadicAlgCl T ℓ E))).inv.app M

private lemma localOriginalAdjoint_hom :
    (localOriginalAdjoint T X f ℓ E Y g P M a).hom =
      (Mod.extendUnit ((upperStar Ab.{u + 1} g).map
        ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E))) P).hom ≫
          a.hom.hom := by
  simp only [localOriginalAdjoint, Adjunction.homEquiv_unit, scalar_unit,
    Mod.comp_hom', Mod.comap_map_hom,
    CategoryTheory.Functor.mapModComapIso_inv_app_hom]
  exact Category.comp_id _

end LocalColimit

private lemma overlapComparison_symm {W U V X : Scheme.{u}}
    {p : W ⟶ U} {g : U ⟶ X} {q : W ⟶ V} {h : V ⟶ X}
    (w : p ≫ g = q ≫ h) :
    overlapComparison w.symm = (overlapComparison w).symm := by
  rw [overlapComparison_eq_original, overlapComparison_eq_original]
  have e : upperStarCongr Ab.{u + 1} w.symm =
      (upperStarCongr Ab.{u + 1} w).symm := Iso.ext (by simp [upperStarCongr])
  rw [upperStarCompIso, upperStarCompIso, e,
    Iso.trans_symm, Iso.trans_symm,
    Iso.symm_symm_eq, Iso.trans_assoc]

private lemma fp_finite_family_stage
    {J : Type u} [Finite J] (W : J → Scheme.{u})
    [∀ j, CompactSpace (W j)] [∀ j, QuasiSeparatedSpace (W j)]
    (R : ∀ j, Sheaf (Scheme.ProEt.topology (W j)) Ab.{u + 1}) [∀ j, MonObj (R j)]
    {A : Type (u + 1)} [SmallCategory A] [IsFiltered A]
    (D : ∀ j, A ⥤ Mod (Sheaf (Scheme.ProEt.topology (W j)) Ab.{u + 1}) (R j))
    (c : ∀ j, Cocone (D j)) (hc : ∀ j, IsColimit (c j))
    (P : ∀ j, Mod (Sheaf (Scheme.ProEt.topology (W j)) Ab.{u + 1}) (R j))
    (hP : ∀ j, Mod.IsFinitelyPresented (R j) (P j))
    (a : ∀ j, P j ⟶ (c j).pt) :
    ∃ (k : A) (b : ∀ j, P j ⟶ (D j).obj k),
      ∀ j, b j ≫ (c j).ι.app k = a j := by
  classical
  choose k b hb using fun j ↦ condensed_fp_hom_stage (R j) (c j) (hc j) (P j) (hP j) (a j)
  let : Fintype J := Fintype.ofFinite J
  obtain ⟨l, hl⟩ := IsFiltered.sup_objs_exists (Finset.univ.image k)
  let t (j : J) : k j ⟶ l :=
    Classical.choice (hl (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩))
  refine ⟨l, fun j ↦ b j ≫ (D j).map (t j), ?_⟩
  intro j
  rw [Category.assoc, (c j).w]
  exact hb j

private structure LocalPresentation (X : Scheme.{u})
    (R S : Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) [MonObj R] [MonObj S]
    [IsCommMonObj R]
    (χ : R ⟶ S) [IsMonHom χ]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) S) where
  Y : Scheme.{u}
  g : Y ⟶ X
  N : Mod (Sheaf (Scheme.ProEt.topology Y) Ab.{u + 1})
    ((upperStar Ab.{u + 1} g).obj R)
  fp : Mod.IsFinitelyPresented _ N
  e : (Mod.extendScalars ((upperStar Ab.{u + 1} g).map χ)).obj N ≅
    ((upperStar Ab.{u + 1} g).mapMod S).obj M

private noncomputable abbrev LocalData
    (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))) :=
  LocalPresentation X ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))
    ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)) M

section Spans
variable (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
  (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
  (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
    ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))

private noncomputable def spanDiagram (src dst : LocalData T X f ℓ E M)
    (W : Scheme.{u}) (p : W ⟶ src.Y) (q : W ⟶ dst.Y)
    (w : p ≫ src.g = q ≫ dst.g) :
    CoeffIndex ℓ E ⥤ Mod (Sheaf (Scheme.ProEt.topology W) Ab.{u + 1})
      ((upperStar Ab.{u + 1} p).obj ((upperStar Ab.{u + 1} src.g).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))) :=
  (rawScalarDiagram T X f ℓ E dst.Y dst.g dst.N ⋙
    (upperStar Ab.{u + 1} q).mapMod ((upperStar Ab.{u + 1} dst.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))) ⋙
        Mod.comap (squareRing (upperStar Ab.{u + 1} src.g) (upperStar Ab.{u + 1} p)
          (upperStar Ab.{u + 1} dst.g) (upperStar Ab.{u + 1} q)
          (overlapComparison w)
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))

private noncomputable def spanCocone (src dst : LocalData T X f ℓ E M)
    (W : Scheme.{u}) (p : W ⟶ src.Y) (q : W ⟶ dst.Y)
    (w : p ≫ src.g = q ≫ dst.g) :
    Cocone (spanDiagram T X f ℓ E M src dst W p q w) :=
  (Mod.comap (squareRing (upperStar Ab.{u + 1} src.g) (upperStar Ab.{u + 1} p)
    (upperStar Ab.{u + 1} dst.g) (upperStar Ab.{u + 1} q)
    (overlapComparison w)
    ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).mapCocone
      (((upperStar Ab.{u + 1} q).mapMod
        ((upperStar Ab.{u + 1} dst.g).obj
          ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).mapCocone
            (localScalarCocone T X f ℓ E dst.Y dst.g dst.N M dst.e))

private noncomputable def spanCocone_isColimit (src dst : LocalData T X f ℓ E M)
    (W : Scheme.{u}) (p : W ⟶ src.Y) (q : W ⟶ dst.Y)
    (w : p ≫ src.g = q ≫ dst.g) :
    IsColimit (spanCocone T X f ℓ E M src dst W p q w) := by
  exact comapCocone_isColimit _ _
    (mapModCocone_isColimit (upperStar Ab.{u + 1} q) (lowerStar Ab.{u + 1} q)
      (upperStarLowerStarAdjunction Ab.{u + 1} q) _ _
      (localScalarCocone_isColimit T X f ℓ E dst.Y dst.g dst.N M dst.e))

private noncomputable def spanPointMap (src dst : LocalData T X f ℓ E M)
    (W : Scheme.{u}) (p : W ⟶ src.Y) (q : W ⟶ dst.Y)
    (w : p ≫ src.g = q ≫ dst.g) :
    ((upperStar Ab.{u + 1} p).mapMod ((upperStar Ab.{u + 1} src.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).obj src.N ⟶
      (spanCocone T X f ℓ E M src dst W p q w).pt :=
  ((upperStar Ab.{u + 1} p).mapMod
    ((upperStar Ab.{u + 1} src.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).map
        (localOriginalAdjoint T X f ℓ E src.Y src.g src.N M src.e) ≫
    (squareModIso (upperStar Ab.{u + 1} src.g) (upperStar Ab.{u + 1} p)
      (upperStar Ab.{u + 1} dst.g) (upperStar Ab.{u + 1} q)
      (overlapComparison w)
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))
        ((Mod.comap ((upperStar Ab.{u + 1} f).map
          (padicSubfieldRingObjToPadicAlgCl T ℓ E))).obj M)).hom

set_option backward.isDefEq.respectTransparency true in
private lemma spanFactor (src dst : LocalData T X f ℓ E M)
    (W : Scheme.{u}) (p : W ⟶ src.Y) (q : W ⟶ dst.Y)
    (w : p ≫ src.g = q ≫ dst.g) (k : CoeffIndex ℓ E)
    (b : ((upperStar Ab.{u + 1} p).mapMod ((upperStar Ab.{u + 1} src.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).obj src.N ⟶
        (spanDiagram T X f ℓ E M src dst W p q w).obj k)
    (hb : b ≫ (spanCocone T X f ℓ E M src dst W p q w).ι.app k =
      spanPointMap T X f ℓ E M src dst W p q w) :
    let F := (coeffIndexFunctor ℓ E).obj k
    let hEF := coeffIndex_le ℓ E k
    ∃ s : (upperStar Ab.{u + 1} p).obj
        (finiteCoefficientLocalModel T X f ℓ E src.Y src.g src.N F hEF).X ⟶
      (upperStar Ab.{u + 1} q).obj
        (finiteCoefficientLocalModel T X f ℓ E dst.Y dst.g dst.N F hEF).X,
      s ≫ (upperStar Ab.{u + 1} q).map
        (finiteCoefficientLocalAdjoint T X f ℓ E dst.Y dst.g dst.N M dst.e.hom F hEF).hom =
      (upperStar Ab.{u + 1} p).map
        (finiteCoefficientLocalAdjoint T X f ℓ E src.Y src.g src.N M src.e.hom F hEF).hom ≫
          (overlapComparison w).hom.app M.X := by
  set_option backward.isDefEq.respectTransparency false in
    apply finiteCoefficient_overlap_factor_transpose T X f ℓ E src.Y dst.Y W src.g dst.g
      p q w M src.N dst.N src.e.hom dst.e.hom
      ((coeffIndexFunctor ℓ E).obj k) (coeffIndex_le ℓ E k)
      (squareRing (upperStar Ab.{u + 1} src.g) (upperStar Ab.{u + 1} p)
        (upperStar Ab.{u + 1} dst.g) (upperStar Ab.{u + 1} q)
        (overlapComparison w)
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (squareRing_eq _ _ _ _ _ _) b
  have hf := congrArg (fun z ↦ z.hom) hb
  have hpoint : (spanPointMap T X f ℓ E M src dst W p q w).hom =
      (upperStar Ab.{u + 1} p).map
        (localOriginalAdjoint T X f ℓ E src.Y src.g src.N M src.e).hom ≫
          (overlapComparison w).hom.app M.X := rfl
  have hpoint' := hpoint.trans (congrArg
    (fun z ↦ (upperStar Ab.{u + 1} p).map z ≫
      (overlapComparison w).hom.app M.X)
    (localOriginalAdjoint_hom T X f ℓ E src.Y src.g src.N M src.e))
  have hleg₀ := restrictedCocone_leg_hom
    (squareRing (upperStar Ab.{u + 1} src.g) (upperStar Ab.{u + 1} p)
      (upperStar Ab.{u + 1} dst.g) (upperStar Ab.{u + 1} q)
      (overlapComparison w)
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))
    (((upperStar Ab.{u + 1} q).mapMod ((upperStar Ab.{u + 1} dst.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).mapCocone
        (localScalarCocone T X f ℓ E dst.Y dst.g dst.N M dst.e)) k
  have hleg₁ := mappedCocone_leg_hom (upperStar Ab.{u + 1} q)
    ((upperStar Ab.{u + 1} dst.g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))
    (localScalarCocone T X f ℓ E dst.Y dst.g dst.N M dst.e) k
  have hleg₂ := congrArg (fun z ↦ (upperStar Ab.{u + 1} q).map z)
    (localScalarCocone_leg T X f ℓ E dst.Y dst.g dst.N M dst.e k)
  exact (congrArg (b.hom ≫ ·) (hleg₀.trans (hleg₁.trans hleg₂))).symm.trans
    (hf.trans hpoint')

end Spans

set_option backward.isDefEq.respectTransparency true in
/-- Finite-stage comparison maps in both directions on all pairwise pullbacks.

Source: archived `TwoColimit.lean`, (Obj) overlap descent paragraph.
(auxiliary; not a blueprint node).

Proof: use the filtered category of finite coefficient fields above E. On each Y_i,
form the diagram Res_EF(F tensor_E N_i). The coefficient-ring colimit is the pulled
Omega ring: inverse images preserve colimits. Tensoring and then taking the defining
scalar-extension coequalizers preserves this colimit. Extend its point through e_i
and the inverse of mapModComapIso. The resulting cocone has point g_i*Res_EOmega(M),
and its legs are exactly the underlying canonical finiteCoefficientLocalAdjoint;
the scalar-unit and transitivity identities verify this formula.

For an oriented overlap p:W -> Y_i, q:W -> Y_j, pull the j-th cocone along q and
restrict along the monoidal E-ring comparison. Both functors preserve colimits:
pullback is a left adjoint, and restriction along this ring isomorphism is an
equivalence. Pullback preserves finite free cokernel presentations, so p*N_i is
finitely presented. Its E-to-Omega adjoint, followed by the module comparison of
the commutative square, is a map into this colimit.

Index the oriented overlaps by I times I times Bool. Generic finitely presented Hom
continuity gives a stage for each map, and filteredness supplies one common upper
stage. This includes the empty family. At that field the fixed-field overlap
transposition lemma converts each E-linear factor into the required underlying
map between pulled finite local models. Its factorization equation is the given
cocone equation, using the explicit leg formula. The false Boolean case gives s;
the true case gives t. The comparison of the reversed square is the inverse of the
original comparison, so these are exactly the two equations in the conclusion.
-/
theorem exists_finiteCoefficient_family_hom_factorizations
    (T X : Scheme.{u}) (f : X ⟶ T) (ℓ : ℕ) [Fact ℓ.Prime]
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ)))
    (E : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ))
    (I : Type u) [Finite I] (Y : I → Scheme.{u}) (g : ∀ i, Y i ⟶ X)
    [∀ (i j : I), CompactSpace (pullback (g i) (g j) : Scheme.{u})]
    [∀ (i j : I), QuasiSeparatedSpace (pullback (g i) (g j) : Scheme.{u})]
    (N : ∀ i, Mod (Sheaf (Scheme.ProEt.topology (Y i)) Ab.{u + 1})
      ((upperStar Ab.{u + 1} (g i)).obj
        ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))))
    (hN : ∀ i, Mod.IsFinitelyPresented ((upperStar Ab.{u + 1} (g i)).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E))) (N i))
    (e : ∀ i, (Mod.extendScalars ((upperStar Ab.{u + 1} (g i)).map
      ((upperStar Ab.{u + 1} f).map (padicSubfieldRingObjToPadicAlgCl T ℓ E)))).obj (N i) ≅
      ((upperStar Ab.{u + 1} (g i)).mapMod
        ((upperStar Ab.{u + 1} f).obj (padicAlgClRingObj T ℓ))).obj M) :
    ∃ (F : Padic.FiniteCoefficientFields ℓ (PadicAlgCl ℓ)) (hEF : E ≤ F),
      let L := fun i ↦ finiteCoefficientLocalModel T X f ℓ E (Y i) (g i) (N i) F hEF
      let q := fun i ↦ finiteCoefficientLocalAdjoint T X f ℓ E (Y i) (g i) (N i) M
        (e i).hom F hEF
      let B := ((Mod.comap ((upperStar Ab.{u + 1} f).map
        (padicSubfieldRingObjToPadicAlgCl T ℓ F))).obj M).X
      ∀ i j, ∃ (s : (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).obj (L i).X ⟶
          (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).obj (L j).X)
        (t : (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).obj (L j).X ⟶
          (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).obj (L i).X),
        (s ≫ (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map (q j).hom =
          (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map (q i).hom ≫
            (upperStarCompIso Ab.{u + 1} (pullback.condition (f := g i) (g := g j))).hom.app
              B) ∧
        (t ≫ (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map (q i).hom =
          (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map (q j).hom ≫
            (upperStarCompIso Ab.{u + 1} (pullback.condition (f := g i) (g := g j))).inv.app
              B) := by
  classical
  let data (i : I) : LocalData T X f ℓ E M := ⟨Y i, g i, N i, hN i, e i⟩
  let J := I × I × Bool
  let src (j : J) := if j.2.2 then data j.2.1 else data j.1
  let dst (j : J) := if j.2.2 then data j.1 else data j.2.1
  let W (j : J) : Scheme.{u} := pullback (g j.1) (g j.2.1)
  let p (j : J) : W j ⟶ (src j).Y := by
    rcases j with ⟨i, j, b⟩
    cases b
    · exact pullback.fst (g i) (g j)
    · exact pullback.snd (g i) (g j)
  let q (j : J) : W j ⟶ (dst j).Y := by
    rcases j with ⟨i, j, b⟩
    cases b
    · exact pullback.snd (g i) (g j)
    · exact pullback.fst (g i) (g j)
  let w (j : J) : p j ≫ (src j).g = q j ≫ (dst j).g := by
    rcases j with ⟨i, j, b⟩
    cases b
    · exact pullback.condition
    · exact pullback.condition.symm
  let : ∀ j, CompactSpace (W j) := fun j ↦
    inferInstanceAs (CompactSpace (pullback (g j.1) (g j.2.1) : Scheme.{u}))
  let : ∀ j, QuasiSeparatedSpace (W j) := fun j ↦
    inferInstanceAs (QuasiSeparatedSpace (pullback (g j.1) (g j.2.1) : Scheme.{u}))
  let R (j : J) := (upperStar Ab.{u + 1} (p j)).obj
    ((upperStar Ab.{u + 1} (src j).g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))
  let D (j : J) := spanDiagram T X f ℓ E M (src j) (dst j) (W j) (p j) (q j) (w j)
  let c (j : J) := spanCocone T X f ℓ E M (src j) (dst j) (W j) (p j) (q j) (w j)
  let P (j : J) := ((upperStar Ab.{u + 1} (p j)).mapMod
    ((upperStar Ab.{u + 1} (src j).g).obj
      ((upperStar Ab.{u + 1} f).obj (padicSubfieldRingObj T ℓ E)))).obj (src j).N
  obtain ⟨k, b, hb⟩ := fp_finite_family_stage W R D c
    (fun j ↦ spanCocone_isColimit T X f ℓ E M (src j) (dst j) (W j) (p j) (q j) (w j))
    P (fun j ↦ fp_pullback (p j) (src j).fp)
    (fun j ↦ spanPointMap T X f ℓ E M (src j) (dst j) (W j) (p j) (q j) (w j))
  refine ⟨(coeffIndexFunctor ℓ E).obj k, coeffIndex_le ℓ E k, ?_⟩
  intro L qLocal B i j
  obtain ⟨s, hs⟩ := spanFactor T X f ℓ E M
    (src (i, j, false)) (dst (i, j, false)) (W (i, j, false))
    (p (i, j, false)) (q (i, j, false)) (w (i, j, false)) k (b (i, j, false))
    (hb (i, j, false))
  obtain ⟨t, ht⟩ := spanFactor T X f ℓ E M
    (src (i, j, true)) (dst (i, j, true)) (W (i, j, true))
    (p (i, j, true)) (q (i, j, true)) (w (i, j, true)) k (b (i, j, true))
    (hb (i, j, true))
  have hcomparison := congrArg (fun z ↦ z.hom.app B)
    (overlapComparison_eq_original (pullback.condition (f := g i) (g := g j)))
  have hs' := hs.trans (congrArg
    (fun z ↦ (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map
      (qLocal i).hom ≫ z) hcomparison)
  refine ⟨s, t, hs', ?_⟩
  change t ≫ (upperStar Ab.{u + 1} (pullback.fst (g i) (g j))).map
      (qLocal i).hom =
    (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map (qLocal j).hom ≫
      (overlapComparison
        (pullback.condition (f := g i) (g := g j)).symm).hom.app B at ht
  have ht' := ht.trans (congrArg
    (fun z ↦ (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map
      (qLocal j).hom ≫ z)
    (congrArg (fun z ↦ z.hom.app B)
      (overlapComparison_symm (pullback.condition (f := g i) (g := g j)))))
  exact ht'.trans (congrArg
    (fun z ↦ (upperStar Ab.{u + 1} (pullback.snd (g i) (g j))).map
      (qLocal j).hom ≫ z)
    (congrArg (fun z ↦ z.inv.app B)
      (overlapComparison_eq_original (pullback.condition (f := g i) (g := g j)))))

end AlgebraicGeometry.ProEtale

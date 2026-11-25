/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.SchemeOrdinaryEvaluationFormula
public import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.LocalizedOpenSheafification
import WeilConjectures.AlgebraicGeometry.OrdinaryEvaluationOverComponentIdentity
import Mathlib.CategoryTheory.Localization.Monoidal.Functor

/-! # Normalized tensor summands under the open-site equivalence

Source: Stacks Project, Tag 0A8X, ordinary tensor totalization; the open-site
reindexing construction in Mathlib `Scheme.Modules.overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands). -/

@[expose] public section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite

namespace AlgebraicGeometry

open BraidedCategory Functor MonoidalCategory.Functor

attribute [local instance] SheafOfModules.monoidalCategory SheafOfModules.symmetricCategory
-- The proof uses the equivalence API, never its large sectionwise implementation.
attribute [local irreducible] Scheme.Modules.overEquiv

attribute [local instance] ordinaryComponentIdentityOverPreadditive

attribute [local instance] ordinaryComponentIdentitySchemePreadditive

section Normalize
universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D]
private def scalarIso (b : 𝟙_ D ≅ 𝟙_ D) : 𝟭 D ≅ 𝟭 D :=
  NatIso.ofComponents (fun X ↦ (λ_ X).symm ≪≫ whiskerRightIso b X ≪≫ λ_ X)
    (by
      intro X Y f
      dsimp
      simp only [Category.assoc, whiskerRightIso_hom]
      rw [leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
        leftUnitor_naturality])
private theorem scalarIso_unit (b : 𝟙_ D ≅ 𝟙_ D) :
    (scalarIso b).hom.app (𝟙_ D) = b.hom := by
  dsimp [scalarIso]
  rw [whiskerRightIso_hom, unitors_equal, rightUnitor_naturality, unitors_inv_equal,
    Iso.inv_hom_id_assoc]
variable [BraidedCategory C] [BraidedCategory D]

private theorem normalize (F : C ⥤ D) [F.Braided]
    (e : 𝟙_ D ≅ F.obj (𝟙_ C)) :
    ∃ m : F.CoreMonoidal, m.εIso = e ∧
      ∀ A B : C, F.map (β_ A B).hom ≫ (m.μIso B A).inv =
        (m.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom := by
  let b := e ≪≫ (Functor.Monoidal.εIso F).symm
  let a : F ≅ F := NatIso.ofComponents (fun X ↦ (scalarIso b).app (F.obj X))
    (fun f ↦ (scalarIso b).hom.naturality (F.map f))
  let m := Functor.Monoidal.coreMonoidalTransport a
  refine ⟨m, ?_, ?_⟩
  · apply Iso.ext
    change (Functor.Monoidal.εIso F).hom ≫ a.hom.app (𝟙_ C) = e.hom
    have hn := (scalarIso b).hom.naturality (Functor.Monoidal.εIso F).hom
    dsimp only [Functor.id_map] at hn
    change (Functor.Monoidal.εIso F).hom ≫
      (scalarIso b).hom.app (F.obj (𝟙_ C)) = e.hom
    rw [hn, scalarIso_unit]
    simp [b]
  · intro A B
    simp only [m, Functor.Monoidal.coreMonoidalTransport_μIso_inv, Category.assoc]
    rw [a.inv.naturality_assoc]
    rw [braiding_naturality]
    congr 1
    rw [Functor.map_braiding]
    simp

end Normalize

section Descent
universe u₁ v₁ u₂ v₂ u₃ v₃
variable {C : Type u₁} [Category.{v₁} C] [MonoidalCategory C] [BraidedCategory C]
variable {D : Type u₂} [Category.{v₂} D] [MonoidalCategory D] [BraidedCategory D]
variable {E : Type u₃} [Category.{v₃} E] [MonoidalCategory E] [BraidedCategory E]
private theorem braided_descent (L : C ⥤ D) [L.Braided] (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : D ⥤ E) [F.Monoidal]
    (hbr : ∀ X Y : C,
      (Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫
        F.map (Functor.LaxMonoidal.μ L X Y)) ≫ F.map (L.map (β_ X Y).hom) =
      (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
        (Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X) ≫
          F.map (Functor.LaxMonoidal.μ L Y X))) :
    ∀ X Y : D, Functor.LaxMonoidal.μ F X Y ≫ F.map (β_ X Y).hom =
      (β_ (F.obj X) (F.obj Y)).hom ≫ Functor.LaxMonoidal.μ F Y X := by
  let t := Functor.curriedTensorPreIsoPost F
  let bp := (postcompose₂.obj F).mapIso (curriedBraidingNatIso D)
  let bi := (((whiskeringLeft₂ E).obj F).obj F).mapIso (curriedBraidingNatIso E)
  let a : curriedTensorPre F ⟶ (curriedTensorPost F).flip := t.hom ≫ bp.hom
  let b : curriedTensorPre F ⟶ (curriedTensorPost F).flip :=
    bi.hom ≫ (flipFunctor _ _ _).map t.hom
  have hab : a = b := by
    apply Localization.natTrans₂_ext L L W W
    intro X Y
    change Functor.LaxMonoidal.μ F (L.obj X) (L.obj Y) ≫
        F.map (β_ (L.obj X) (L.obj Y)).hom =
      (β_ (F.obj (L.obj X)) (F.obj (L.obj Y))).hom ≫
        Functor.LaxMonoidal.μ F (L.obj Y) (L.obj X)
    have h := hbr X Y
    apply (cancel_mono (F.map (Functor.LaxMonoidal.μ L Y X))).1
    simpa only [Category.assoc, ← F.map_comp, Functor.LaxBraided.braided] using h
  intro X Y
  exact congrArg (fun k ↦ (k.app X).app Y) hab

/-- Descend and normalize before specializing to concrete sheaf categories. -/
private theorem normalizedCoreMonoidalOfLocalization
    (L : C ⥤ D) [L.Braided] (W : MorphismProperty C)
    [L.IsLocalization W] [W.ContainsIdentities]
    (F : D ⥤ E) (G : C ⥤ E) [G.Braided]
    (h : L ⋙ F ≅ G) (e : 𝟙_ E ≅ F.obj (𝟙_ D)) :
    ∃ m : F.CoreMonoidal, m.εIso = e ∧
      ∀ A B : D, F.map (β_ A B).hom ≫ (m.μIso B A).inv =
        (m.μIso A B).inv ≫ (β_ (F.obj A) (F.obj B)).hom := by
  let : Localization.Lifting L W G F := ⟨h⟩
  let : F.Monoidal := Localization.Monoidal.functorMonoidalOfComp L W F G
  let : h.hom.IsMonoidal := Localization.Monoidal.lifting_isMonoidal L W F G
  have hb := braided_descent L W F (by
    intro A B
    change Functor.LaxMonoidal.μ (L ⋙ F) A B ≫ (L ⋙ F).map (β_ A B).hom =
      (β_ ((L ⋙ F).obj A) ((L ⋙ F).obj B)).hom ≫
        Functor.LaxMonoidal.μ (L ⋙ F) B A
    have hm (A B) := NatTrans.IsMonoidal.tensor (τ := h.hom) A B
    apply (cancel_mono (h.hom.app (B ⊗ A))).1
    simp only [Category.assoc]
    rw [h.hom.naturality, ← Category.assoc, hm A B]
    simp only [Category.assoc]
    rw [hm B A, Functor.LaxBraided.braided, braiding_naturality_assoc])
  let : F.Braided :=
    { toMonoidal := (inferInstance : F.Monoidal)
      braided := hb }
  exact normalize F e

end Descent

section TensorTotal

universe u₁ v₁ u₂ v₂
variable {C : Type u₁} [Category.{v₁} C] [Preadditive C] [MonoidalCategory C]
  [MonoidalPreadditive C] [HasCoproducts.{0} C]
  {D : Type u₂} [Category.{v₂} D] [Preadditive D] [MonoidalCategory D]
  [MonoidalPreadditive D] [HasCoproducts.{0} D]

/-- The standard comparison of total complexes, with its equation on each tensor summand. -/
private theorem exists_tensorTotalIso (R : C ⥤ D) [R.Additive]
    [PreservesColimitsOfSize.{0, 0} R] (m : R.CoreMonoidal)
    (F K : CochainComplex C ℤ) :
    ∃ c : (R.mapHomologicalComplex (.up ℤ)).obj
        (HomologicalComplex.mapBifunctor F K (curriedTensor C) (.up ℤ)) ≅
      HomologicalComplex.mapBifunctor ((R.mapHomologicalComplex (.up ℤ)).obj F)
        ((R.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor D) (.up ℤ),
      ∀ (p q n : ℤ) (h : p + q = n),
        R.map (HomologicalComplex.ιMapBifunctor F K (curriedTensor C) (.up ℤ) p q n h) ≫
          c.hom.f n = (m.μIso (F.X p) (K.X q)).inv ≫
            HomologicalComplex.ιMapBifunctor ((R.mapHomologicalComplex (.up ℤ)).obj F)
              ((R.mapHomologicalComplex (.up ℤ)).obj K) (curriedTensor D) (.up ℤ) p q n h := by
  let : R.OplaxMonoidal := m.toOplaxMonoidal
  have (A B : C) : IsIso (Functor.OplaxMonoidal.δ R A B) := (m.μIso A B).isIso_inv
  let τ := Functor.OplaxMonoidal.δNatTrans R
  refine ⟨asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) F K), ?_⟩
  intro p q n h
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX τ (.up ℤ) F K p q n h

end TensorTotal

/-- The open-site equivalence has a symmetric core monoidal structure with its prescribed unit.
Source: Stacks Project, Tag 01CD, tensor transport along an equivalence of ringed sites.

Proof: lift the braided monoidal presheaf reindexing functor through sheafification.
The lifting isomorphism is monoidal, and its tensor equation descends the braided equation.
Normalize the unit by transporting along the explicit scalar natural automorphism from
`scalarIso`; `normalize` proves that this preserves braiding and gives the prescribed unit.
The construction applies to empty opens and zero rings and does not involve complexes.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands). -/
private theorem exists_normalizedOpen_coreMonoidal (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) := by
  let : MonoidalCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.monoidalCategory (X.sheaf.over U)
  let : SymmetricCategory
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    SheafOfModules.symmetricCategory (X.sheaf.over U)
  let E := Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
  let : MonoidalCategory
      (PresheafOfModules.{u} ((moduleRings X.toRingedSpace).over U).obj) :=
    PresheafOfModules.monoidalCategory (R := (X.sheaf.over U).obj)
  let : MonoidalCategory
      (PresheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace).obj) :=
    PresheafOfModules.monoidalCategory (R := U.toScheme.sheaf.obj)
  let : SymmetricCategory
      (PresheafOfModules.{u} ((moduleRings X.toRingedSpace).over U).obj) :=
    PresheafOfModules.symmetricCategory (R := (X.sheaf.over U).obj)
  let : SymmetricCategory
      (PresheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace).obj) :=
    PresheafOfModules.symmetricCategory (R := U.toScheme.sheaf.obj)
  let L := PresheafOfModules.sheafification.{u}
    (R := (moduleRings X.toRingedSpace).over U)
    (𝟙 ((moduleRings X.toRingedSpace).over U).obj)
  let P := PresheafOfModules.pushforward₀OfCommRingCat
    (TopologicalSpace.Opens.overEquivalence U).inverse (X.sheaf.over U).obj
  let S := PresheafOfModules.sheafification.{u}
    (R₀ := (moduleRings U.toScheme.toRingedSpace).obj)
    (R := moduleRings U.toScheme.toRingedSpace)
    (𝟙 (moduleRings U.toScheme.toRingedSpace).obj)
  let W := ((Opens.grothendieckTopology X).over U).W.inverseImage
    (PresheafOfModules.toPresheaf.{u} ((moduleRings X.toRingedSpace).over U).obj)
  let : L.Braided := SheafOfModules.sheafificationBraided (X.sheaf.over U)
  let : S.Braided := SheafOfModules.sheafificationBraided U.toScheme.sheaf
  let : P.Braided :=
    { __ := (inferInstance : P.Monoidal)
      braided A B := by
        ext1
        exact ModuleCat.MonoidalCategory.tensor_ext fun _ _ ↦ rfl }
  let : (P ⋙ S).Braided := inferInstance
  obtain ⟨h⟩ := exists_localizedOpen_sheafification_iso X U
  exact normalizedCoreMonoidalOfLocalization L W E (P ⋙ S) h
    (Scheme.Modules.overEquivFunctorObjUnitIso U)


/-- The open-site tensor comparison has the prescribed unit, symmetry and total summands.
Source: Stacks Project, Tag 0A8X, tensor totalization; Mathlib `overEquiv`.
(blueprint: lem-pc-ordinary-evaluation-tensor-summands).

Proof: on presheaves reindex each pure tensor along the open-site equivalence.
The coefficient identifications preserve balancing, restriction, associativity
and exchange of factors. Descend these maps and their inverses through
sheafification. The unit map sends a local coefficient to the same coefficient;
this is `overEquivFunctorObjUnitIso`. This constructs a symmetric monoidal
structure m with that unit, rather than an arbitrary natural tensor comparison.
In bidegree (p,q) use the inverse of m's tensorator. Its naturality commutes
with both differentials. Assemble the bicomplex isomorphism and compose its
totalization with the inverse of `HomologicalComplex₂.mapTotalIso`.
The equivalence preserves all coproducts, so the image of every total summand
is exactly the displayed tensorator followed by its target summand inclusion.
This gives c and its equation. Signed differentials introduce no additional
sign in these degreewise inclusions. This construction applies to unbounded
complexes, zero modules, the empty open and the zero coefficient ring. -/
theorem exists_ordinaryEvaluation_tensor_summands (X : Scheme.{u}) (U : X.Opens) :
    let L := Equivalence.functor
      (C := localEvaluationModules X U)
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Scheme.Modules.overEquiv U)
    let T := L.mapHomologicalComplex (.up ℤ)
    ∃ m : L.CoreMonoidal,
      m.εIso = Scheme.Modules.overEquivFunctorObjUnitIso U ∧
      (∀ A B : localEvaluationModules X U,
        L.map (β_ A B).hom ≫ (m.μIso B A).inv =
          (m.μIso A B).inv ≫ (β_ (L.obj A) (L.obj B)).hom) ∧
      ∀ P F : CochainComplex (localEvaluationModules X U) ℤ,
        ∃ c : T.obj (localEvaluationTensor X U P F) ≅
            pullbackTensorTotal U.toScheme (T.obj F) (T.obj (localEvaluationDual X U P)),
          ∀ (p q n : ℤ) (h : p + q = n),
            L.map (HomologicalComplex.ιMapBifunctor F (localEvaluationDual X U P)
                (curriedTensor _) (.up ℤ) p q n h) ≫ c.hom.f n =
              (m.μIso (F.X p) ((localEvaluationDual X U P).X q)).inv ≫
                HomologicalComplex.ιMapBifunctor (T.obj F)
                  (T.obj (localEvaluationDual X U P)) (curriedTensor _) (.up ℤ) p q n h := by
  let R := Equivalence.functor
    (C := localEvaluationModules X U)
    (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
    (Scheme.Modules.overEquiv U)
  let : R.Additive := Functor.additive_of_preserves_binary_products _
  have : PreservesColimitsOfSize.{0, 0} R := by
    dsimp [R]
    infer_instance
  obtain ⟨m, hm, hs⟩ := exists_normalizedOpen_coreMonoidal X U
  refine ⟨m, hm, hs, ?_⟩
  intro P F
  exact exists_tensorTotalIso R m F (localEvaluationDual X U P)

end AlgebraicGeometry

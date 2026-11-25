/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.SectionDerivedRealization
public import WeilConjectures.AlgebraicGeometry.SectionTotalOplaxComparisonData
import WeilConjectures.AlgebraicGeometry.SectionOplaxTotalComparison

/-! # Components of the specified representative tensor comparison

The component interface gives the existing qTensor arrow its canonical cochain tensor
codomain. It changes neither the representative transformation nor its normalization.
Source: Stacks 07A4 and 06YU
(auxiliary; not a blueprint node).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe u
open CategoryTheory CategoryTheory.MonoidalCategory
namespace AlgebraicGeometry.ProEtale.ModuleRingedComparison
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)]

attribute [local irreducible] Functor.mapDerivedCategory tensor tensorComparison qTensor

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The existing chosen internal localization, with its instance arguments retained.
Source: Stacks 05RU (auxiliary; not a blueprint node).
This names the pre-existing localization instance; it constructs no new localization. -/
@[instance_reducible] instance (priority := 3000) compactInternalHasDerivedCategory
    (T : Scheme.{u}) : HasDerivedCategory.{u + 1} (internalModules Λ T) :=
  inferInstance

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The existing category structure on the internal derived category, retained compactly.
Source: Stacks 05RU (auxiliary; not a blueprint node).
The instance is precisely the pre-existing derived category instance. -/
@[instance_reducible] instance (priority := 3000) compactInternalDerivedCategory
    (T : Scheme.{u}) : Category.{u + 1} (DerivedCategory (internalModules Λ T)) :=
  inferInstance

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The existing internal derived monoidal category with its category argument retained.
Source: Stacks 06YU (auxiliary; not a blueprint node).
The body is the existing instance; all data and coherence laws are retained. -/
@[instance_reducible] instance (priority := 3000) compactInternalDerivedMonoidal
    (T : Scheme.{u}) : MonoidalCategory (DerivedCategory (internalModules Λ T)) :=
  inferInstance

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The structure data of the existing retained internal derived tensor.
Source: Stacks 06YU (auxiliary; not a blueprint node). -/
@[instance_reducible] instance (priority := 3000) compactInternalDerivedMonoidalStruct
    (T : Scheme.{u}) : MonoidalCategoryStruct (DerivedCategory (internalModules Λ T)) :=
  (compactInternalDerivedMonoidal Λ T).toMonoidalCategoryStruct

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The existing localization functor with its retained category argument.
Source: Stacks 05RU (auxiliary; not a blueprint node).
Its object map, morphism map and functor laws are precisely those of DerivedCategory.Q. -/
@[implicit_reducible] def internalLocalizationFunctor (T : Scheme.{u}) :
    CochainComplex (internalModules Λ T) ℤ ⥤ DerivedCategory (internalModules Λ T) :=
  DerivedCategory.Q

/-- The existing derived section functor in the retained category instances.
Source: Stacks 05RU (auxiliary; not a blueprint node). -/
@[implicit_reducible] def derivedSectionFunctor (T : Scheme.{u}) :
    DerivedCategory (internalModules Λ T) ⥤ DerivedCategory (modules Λ T) :=
  derivedFunctor Λ T

/-- The fixed internal left-derived pullback, retained directly as a functor.
Source: Stacks 07A6 (auxiliary; not a blueprint node).
This is the same source functor read by internalDerivedPullback, without retaining
its unused comparison-isomorphism argument in the computational expression. -/
@[implicit_reducible] def internalDerivedPullFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) :
    DerivedCategory (internalModules Λ Y) ⥤ DerivedCategory (internalModules Λ X) :=
  (CondensedRing.upperStar Λ f).leftDerivedFunctor

/-- The existing specified derived pullback comparison in the direct functor interface.
Source: Stacks 07A6 (auxiliary; not a blueprint node). -/
@[irreducible] def derivedPullSquare {X Y : Scheme.{u}} (f : X ⟶ Y) :
    internalDerivedPullFunctor Λ f ⋙ (derivedSectionFunctor Λ X) ≅
      (derivedSectionFunctor Λ Y) ⋙ derivedPullback Λ f := by
  with_unfolding_all exact derivedPullComparison Λ f

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The fixed comparison between the two canonical cochain units.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def cochainUnitComparison (T : Scheme.{u}) :
    (cochainSectionEquivalence Λ T).obj (internalCochainUnit Λ T) ≅
      sectionCochainUnit Λ T := totalUnitComparison Λ T

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The specified internal pullback unit arrow, with its cochain endpoints fixed.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def internalPullUnitArrow {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalInternalPull Λ f).obj (internalCochainUnit Λ Y) ⟶ internalCochainUnit Λ X :=
  actualInternalTotalUnit Λ f

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- The specified section pullback unit arrow, with its cochain endpoints fixed.
Source: Stacks 07A4 (auxiliary; not a blueprint node). -/
@[irreducible] def sectionPullUnitArrow {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (totalSectionPull Λ f).obj (sectionCochainUnit Λ Y) ⟶ sectionCochainUnit Λ X :=
  sectionTotalUnit Λ f

private theorem cancel_unit_comparisons {C : Type*} [Category* C]
    {A B D E : C} (a : B ≅ D) (b : A ≅ B) (v : A ⟶ E) (w : D ⟶ E)
    (h : a.inv ≫ b.inv ≫ v = w) : v = b.hom ≫ a.hom ≫ w := by
  rw [← h]
  simp only [Iso.hom_inv_id_assoc]

/-- The ordinary cochain unit square for the specified pullback comparisons.
Source: Stacks 07A4 (auxiliary; not a blueprint node).
Proof: the unit clause of the oplax total comparison identifies the conjugated
internal unit with the section unit. Compose with the forward termwise pullback
comparison and the pullback of the unit comparison. Their inverse laws cancel
both inverse factors, leaving precisely the displayed square. -/
theorem cochainPullUnitCompatibility {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (cochainSectionEquivalence Λ X).map (internalPullUnitArrow Λ f) ≫
        (cochainUnitComparison Λ X).hom =
      (termwisePullComparison Λ f (internalCochainUnit Λ Y)).hom ≫
        (totalSectionPull Λ f).map (cochainUnitComparison Λ Y).hom ≫
        sectionPullUnitArrow Λ f := by
  have h := cancel_unit_comparisons
    ((totalSectionPull Λ f).mapIso (totalUnitComparison Λ Y))
    (termwisePullComparison Λ f _)
    ((totalSectionEquivalence Λ X).map (actualInternalTotalUnit Λ f) ≫
      (totalUnitComparison Λ X).hom) (sectionTotalUnit Λ f)
    (by
      simpa only [conjugatedInternalTotalUnit, Functor.mapIso_inv, Category.assoc] using
        (section_oplax_total_comparison Λ f).2.2.2.2.2.2.1.1)
  simpa only [internalPullUnitArrow, cochainUnitComparison, sectionPullUnitArrow,
    Functor.mapIso_hom, internalCochainUnit, sectionCochainUnit,
    totalSectionEquivalence] using h

/-- The signed-total functor has the canonical cochain tensor as its object map.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: the functor is the uncurried canonical cochain tensor. -/
theorem totalTensor_obj_tensor (X : Scheme.{u})
    (P Q : CochainComplex (modules Λ X) ℤ) :
    (totalTensor Λ X).obj (P, Q) = P ⊗ Q := by
  rfl

/-- The canonical signed-total functor acts on a pair by tensoring its maps.
Source: Stacks 06YN (auxiliary; not a blueprint node).
Proof: the map of the uncurried tensor is the right whisker followed by the left
whisker, which is the defining formula for tensorHom. -/
theorem totalTensor_map (X : Scheme.{u})
    {A A' B B' : CochainComplex (modules Λ X) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
    (totalTensor Λ X).map (Prod.mkHom a b) = a ⊗ₘ b := by
  change (a ▷ B) ≫ (A' ◁ b) = a ⊗ₘ b
  exact (MonoidalCategory.tensorHom_def a b).symm

/-- The canonical internal localization tensor map, with its component type fixed.
Source: Stacks 06YU and 07A4
(auxiliary; not a blueprint node). -/
@[irreducible] def internalQTensorArrow (T : Scheme.{u})
    (A B : CochainComplex (internalModules Λ T) ℤ) :
    (internalLocalizationFunctor Λ T).obj A ⊗ (internalLocalizationFunctor Λ T).obj B ⟶
      (internalLocalizationFunctor Λ T).obj (A ⊗ B) :=
  by
    with_unfolding_all
      exact Functor.LaxMonoidal.μ (DerivedCategory.Q (C := internalModules Λ T)) A B

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (modules Λ T)] in
/-- Naturality of the canonical internal localization tensor map.
Source: Stacks 06YU and 07A4
(auxiliary; not a blueprint node).
Proof: this is the naturality axiom of the fixed lax monoidal localization functor,
with its source and target written using the canonical tensor components. -/
theorem internalQTensorArrow_naturality (T : Scheme.{u})
    {A A' B B' : CochainComplex (internalModules Λ T) ℤ} (a : A ⟶ A') (b : B ⟶ B') :
    ((internalLocalizationFunctor Λ T).map a ⊗ₘ (internalLocalizationFunctor Λ T).map b) ≫
        internalQTensorArrow Λ T A' B' =
      internalQTensorArrow Λ T A B ≫ (internalLocalizationFunctor Λ T).map (a ⊗ₘ b) := by
  unfold internalQTensorArrow internalLocalizationFunctor
  simpa only using
    Functor.LaxMonoidal.μ_natural (DerivedCategory.Q (C := internalModules Λ T)) a b

/-- The fixed localization comparison with the cached cochain equivalence as target.
Source: Stacks 05RU and 06YU
(auxiliary; not a blueprint node). -/
@[irreducible] def cochainLocalizationIso (T : Scheme.{u})
    (P : CochainComplex (internalModules Λ T) ℤ) :
    (derivedSectionFunctor Λ T).obj ((internalLocalizationFunctor Λ T).obj P) ≅
      DerivedCategory.Q.obj ((cochainSectionEquivalence Λ T).obj P) :=
  by with_unfolding_all exact sectionLocalizationComparison Λ T P

/-- Naturality of the fixed localization comparison with canonical cochain types.
Source: Stacks 05RU and 06YU
(auxiliary; not a blueprint node).
Proof: use mapDerivedCategoryFactors.hom.naturality of the fixed exact section functor.
Its source is derivedEquivalence.functor and its target is localization of the fixed
termwise cochain equivalence, by their defining equations. -/
theorem cochainLocalizationIso_naturality (T : Scheme.{u})
    {P Q : CochainComplex (internalModules Λ T) ℤ} (a : P ⟶ Q) :
    (derivedSectionFunctor Λ T).map ((internalLocalizationFunctor Λ T).map a) ≫
        (cochainLocalizationIso Λ T Q).hom =
      (cochainLocalizationIso Λ T P).hom ≫
        DerivedCategory.Q.map ((cochainSectionEquivalence Λ T).map a) := by
  have hn := (equivalence Λ T).functor.mapDerivedCategoryFactors.hom.naturality a
  unfold cochainLocalizationIso
  change (derivedFunctor Λ T).map (DerivedCategory.Q.map a) ≫
      (sectionLocalizationComparison Λ T Q).hom =
    (sectionLocalizationComparison Λ T P).hom ≫
      DerivedCategory.Q.map ((cochainSectionEquivalence Λ T).map a)
  simpa only [sectionLocalizationComparison, Iso.app_hom, derivedFunctor,
    cochainSectionEquivalence, Functor.comp_map] using hn

/-- The specified derived tensor comparison with canonical internal tensor types.
Source: Stacks 06YU
(auxiliary; not a blueprint node). -/
@[irreducible] def derivedSectionTensorIso (T : Scheme.{u})
    (M N : DerivedCategory (internalModules Λ T)) :
    (derivedSectionFunctor Λ T).obj (M ⊗ N) ≅
      (tensor Λ T).obj ((derivedSectionFunctor Λ T).obj M,
        (derivedSectionFunctor Λ T).obj N) :=
  by with_unfolding_all exact (tensorComparison Λ T).app (M, N)

/-- Naturality of the specified derived tensor comparison in canonical types.
Source: Stacks 06YU
(auxiliary; not a blueprint node).
Proof: apply tensorComparison.hom.naturality to the pair of maps; the map of the
uncurried tensor is the canonical tensor of those maps. -/
theorem derivedSectionTensorIso_naturality (T : Scheme.{u})
    {M M' N N' : DerivedCategory (internalModules Λ T)} (a : M ⟶ M') (b : N ⟶ N') :
    (derivedSectionFunctor Λ T).map (a ⊗ₘ b) ≫
        (derivedSectionTensorIso Λ T M' N').hom =
      (derivedSectionTensorIso Λ T M N).hom ≫
        (tensor Λ T).map (Prod.mkHom ((derivedSectionFunctor Λ T).map a)
          ((derivedSectionFunctor Λ T).map b)) := by
  simpa only [derivedSectionFunctor, derivedEquivalence, Functor.asEquivalence,
    derivedSectionTensorIso, Iso.app_hom, Functor.comp_map,
    Functor.prod_map, Functor.uncurry_obj_map, CondensedRing.derivedTensor,
    curriedTensor_map_app, curriedTensor_obj_map, ← MonoidalCategory.tensorHom_def] using
      (tensorComparison Λ T).hom.naturality (Prod.mkHom a b)

/-- The existing qTensor component with its canonical signed-total codomain.
Source: Stacks 07A4 and 06YU
(auxiliary; not a blueprint node). -/
@[irreducible] def qTensorArrow (T : Scheme.{u})
    (P Q : CochainComplex (modules Λ T) ℤ) :
    (tensor Λ T).obj (DerivedCategory.Q.obj P, DerivedCategory.Q.obj Q) ⟶
      DerivedCategory.Q.obj (P ⊗ Q) :=
  (qTensor Λ T).app (P, Q)

/-- Naturality of the specified component, using the canonical cochain tensor map.
Source: Stacks 07A4 and 06YU
(auxiliary; not a blueprint node).
Proof: apply naturality of qTensor to the pair of chain maps and use totalTensor_map
for its signed-total image. -/
theorem qTensorArrow_naturality (T : Scheme.{u})
    {P P' Q Q' : CochainComplex (modules Λ T) ℤ} (a : P ⟶ P') (b : Q ⟶ Q') :
    (tensor Λ T).map (Prod.mkHom (DerivedCategory.Q.map a) (DerivedCategory.Q.map b)) ≫
        qTensorArrow Λ T P' Q' =
      qTensorArrow Λ T P Q ≫ DerivedCategory.Q.map (a ⊗ₘ b) := by
  simpa only [qTensorArrow, Functor.comp_map, Functor.prod_map, totalTensor_map] using
    (qTensor Λ T).naturality (Prod.mkHom a b)

private theorem normalize_tensor
    {C D : Type*} [Category* C] [Category* D] (F : C × C ⥤ D)
    {M M' N N' : C} (a : M ≅ M') (b : N ≅ N') {U V : D}
    (θ : U ≅ F.obj (M, N)) (v : U ⟶ V) (q : F.obj (M', N') ⟶ V)
    (h : q = F.map (Prod.mkHom a.inv b.inv) ≫ θ.inv ≫ v) :
    v = θ.hom ≫ F.map (Prod.mkHom a.hom b.hom) ≫ q := by
  rw [h, ← F.map_comp_assoc]
  simp only [prod_comp, Prod.mkHom, Iso.hom_inv_id]
  change v = θ.hom ≫ F.map (𝟙 _) ≫ θ.inv ≫ v
  rw [F.map_id, Category.id_comp, Iso.hom_inv_id_assoc]

/-- The defining representative square, with all component types fixed canonically.
Source: Stacks 06YU and 07A4
(auxiliary; not a blueprint node).
Proof: the first clause of TensorRepresentativeCondition determines qTensor on every
pair of internal complexes. Multiply its formula on the left by the forward tensor
comparison and the tensor of the forward localization comparisons. Functoriality and
both inverse laws cancel the prescribed inverse factors. The localized total comparison
is exactly localization of the cochain tensor comparison after the localization factor.
-/
theorem qTensorArrow_normalization (T : Scheme.{u})
    (A B : CochainComplex (internalModules Λ T) ℤ) :
    (derivedSectionFunctor Λ T).map
        (internalQTensorArrow Λ T A B) ≫
        (cochainLocalizationIso Λ T (A ⊗ B)).hom ≫
        DerivedCategory.Q.map (cochainTensorComparison Λ T A B).hom =
      (derivedSectionTensorIso Λ T ((internalLocalizationFunctor Λ T).obj A)
          ((internalLocalizationFunctor Λ T).obj B)).hom ≫
        (tensor Λ T).map (Prod.mkHom (cochainLocalizationIso Λ T A).hom
          (cochainLocalizationIso Λ T B).hom) ≫
        qTensorArrow Λ T ((cochainSectionEquivalence Λ T).obj A)
          ((cochainSectionEquivalence Λ T).obj B) := by
  have hq : TensorRepresentativeCondition Λ T (qTensor Λ T) := by
    unfold qTensor
    exact (tensor_representatives Λ T).exists.choose_spec
  have h := normalize_tensor (tensor Λ T)
    (cochainLocalizationIso Λ T A) (cochainLocalizationIso Λ T B)
    (derivedSectionTensorIso Λ T ((internalLocalizationFunctor Λ T).obj A)
        ((internalLocalizationFunctor Λ T).obj B))
    ((derivedSectionFunctor Λ T).map
      (internalQTensorArrow Λ T A B) ≫
      localizedTotalComparison Λ T A B) _ (by
        simpa only [derivedSectionFunctor, derivedEquivalence, Functor.asEquivalence,
          internalLocalizationFunctor, internalQTensorArrow, cochainLocalizationIso,
          derivedSectionTensorIso, internalLocalizationTensorMap_app,
          Iso.app_inv, Category.assoc] using hq.1 A B)
  dsimp only [derivedSectionFunctor, internalLocalizationFunctor,
    cochainLocalizationIso, derivedSectionTensorIso, qTensorArrow,
    localizedTotalComparison, cochainTensorComparison, sectionLocalizationComparison,
    totalTensor, Functor.comp_obj, Functor.uncurry_obj_obj, CondensedRing.derivedTensor,
    curriedTensor_obj_obj, cochainSectionEquivalence] at h ⊢
  simp only [sectionTotalComparison_eq, Iso.app_hom] at h
  convert h using 1 <;> with_unfolding_all rfl

end AlgebraicGeometry.ProEtale.ModuleRingedComparison

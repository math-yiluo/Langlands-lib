/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientCompletionModel
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Basic
import WeilConjectures.CategoryTheory.PrincipalQuotientCompletion.PrincipalQuotientRoosDerived

/-! # Existence of the universal principal quotient completion

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941.
-/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u v r w
open CategoryTheory CategoryTheory.Limits Opposite
namespace CategoryTheory.PrincipalQuotientCompletion

open MonoidalCategory in
private theorem closedUnit_component_natural
    {A : Type*} [Category A] [Preadditive A] [HasZeroObject A] [MonoidalCategory A]
    [(curriedTensor A).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor A).obj M).PreservesZeroMorphisms]
    (D : CochainComplex A ℤ) (u : 𝟙_ A ⟶ D.X 0)
    {P P' : CochainComplex A ℤ} (f : P ⟶ P')
    [HomologicalComplex.HasMapBifunctor D P (curriedTensor A) (.up ℤ)]
    [HomologicalComplex.HasMapBifunctor D P' (curriedTensor A) (.up ℤ)]
    (i : ℤ) :
    f.f i ≫ (λ_ (P'.X i)).inv ≫ u ▷ P'.X i ≫
        HomologicalComplex.ιMapBifunctor D P' (curriedTensor A) (.up ℤ) 0 i i
          (zero_add i) =
      ((λ_ (P.X i)).inv ≫ u ▷ P.X i ≫
        HomologicalComplex.ιMapBifunctor D P (curriedTensor A) (.up ℤ) 0 i i
          (zero_add i)) ≫
        (HomologicalComplex.mapBifunctorMap (𝟙 D) f (curriedTensor A) (.up ℤ)).f i := by
  simp only [Category.assoc, HomologicalComplex.ι_mapBifunctorMap,
    HomologicalComplex.id_f, Functor.map_id, NatTrans.id_app, Category.id_comp,
    curriedTensor_obj_map]
  rw [← whisker_exchange_assoc, ← leftUnitor_inv_naturality_assoc]

variable {C : Type u} [Category.{v} C] [EssentiallySmall.{r} C]
  {J : GrothendieckTopology C}
    [J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r})]
    [HasSheafify J AddCommGrpCat.{r}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{r}]
    (R : Sheaf J CommRingCat.{r})

local instance (I : Type r) : HasColimitsOfShape (Discrete I)
    (PresheafOfModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R).obj) :=
  PresheafOfModules.hasColimitsOfShape _ _

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
private theorem tensorUnit_eq :
    @MonoidalCategory.tensorUnit _ _ (SheafOfModules.monoidalCategory R).toMonoidalCategoryStruct =
      SheafOfModules.unit (SheafOfModules.derivedChangeRingIndependentCoefficients J R) := rfl

attribute [local irreducible] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

private theorem quotient_transition
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) (n : ℕ) :
    quotientMap R t P (n + 1) ≫
        ((quotientTower R t).obj P).asFunctor.map (homOfLE (Nat.le_succ n)).op =
      quotientMap R t P n := by
  let γ := koszulStrictAugmentation R P t ≫ koszulTensorTowerComparison R P t
  have hγ (m : ℕ) : γ.app (op m) = koszulRepresentativeQuotient R P t m :=
    koszulRepresentativeAugmentation_quotient R P t m
  have hn := γ.naturality (homOfLE (Nat.le_succ n)).op
  change 𝟙 P ≫ γ.app (op n) =
    γ.app (op (n + 1)) ≫ (reductionTensorTower R P t).map _ at hn
  change koszulRepresentativeQuotient R P t (n + 1) ≫
      (reductionTensorTower R P t).map _ = koszulRepresentativeQuotient R P t n
  simpa only [Category.id_comp, hγ] using hn.symm

open MonoidalCategory in
private theorem tensorUnitInclusion_natural
    {P P' : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ} (f : P ⟶ P') :
    f ≫ koszulTensorUnitInclusion R P' = koszulTensorUnitInclusion R P ≫
      (((curriedTensor _).map₂CochainComplex).obj
        ((CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit
          (SheafOfModules.derivedChangeRingIndependentCoefficients J R)))).map f := by
  ext i : 1
  change f.f i ≫ koszulTensorUnitComponent R P' i =
    koszulTensorUnitComponent R P i ≫
      (HomologicalComplex.mapBifunctorMap (𝟙 _) f (curriedTensor _) (.up ℤ)).f i
  let D := (CochainComplex.singleFunctor _ 0).obj (SheafOfModules.unit
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))
  have hu : MonoidalCategory.tensorUnit _ = SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R) := tensorUnit_eq R
  let u : MonoidalCategory.tensorUnit _ ⟶ D.X 0 := eqToHom hu ≫
    (HomologicalComplex.singleObjXSelf (.up ℤ) 0
      (SheafOfModules.unit
        (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).inv
  have hh := closedUnit_component_natural D u f i
  dsimp only [u, D] at hh
  simp only [tensorUnit_eq] at hh
  exact hh

private theorem quotient_natural
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    {P P' : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ}
    (f : P ⟶ P') (n : ℕ) :
    f ≫ quotientMap R t P' n = quotientMap R t P n ≫
      (HomologicalComplex.complexOfFunctorsToFunctorToComplex.map
        ((quotientTower R t).map f)).app (op n) := by
  let B := (MonoidalCategory.curriedTensor (ringedSiteModules.{r}
    (SheafOfModules.derivedChangeRingIndependentCoefficients J R))).map₂CochainComplex
  let q := (CochainComplex.singleFunctor _ 0).map
    (cokernel.π (endoPow (globalSectionMultiplication R t) (n + 1)))
  change f ≫ (koszulTensorUnitInclusion R P' ≫ (B.map q).app P') =
    (koszulTensorUnitInclusion R P ≫ (B.map q).app P) ≫
      (B.obj (principalReduction R t n)).map f
  rw [← Category.assoc, tensorUnitInclusion_natural, Category.assoc,
    (B.map q).naturality, Category.assoc]
  rfl

private noncomputable def strictAugmentation
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    (P : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ) :
    P ⟶ (quotientRoos R t).obj P :=
  roosAugment (quotientMap R t P) (quotient_transition R t P)

private theorem strictAugmentation_natural
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    {P P' : CochainComplex (ringedSiteModules.{r}
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)) ℤ} (f : P ⟶ P') :
    f ≫ strictAugmentation R t P' =
      strictAugmentation R t P ≫ (quotientRoos R t).map f := by
  have hp : f ≫ quotientProduct R t P' = quotientProduct R t P ≫
      roosPmap ((quotientTower R t).map f) := by
    apply Pi.hom_ext
    intro n
    simp only [quotientProduct, Category.assoc, Pi.lift_comp_π, roosPmap, Pi.map_π,
      Pi.lift_comp_π_assoc]
    exact quotient_natural R t f n
  ext k : 1
  obtain ⟨p, hp'⟩ := (Equiv.addRight (1 : ℤ)).surjective k
  change p + 1 = k at hp'
  subst k
  apply (cancel_mono (roosχ ((quotientTower R t).obj P') p).hom).1
  simp only [HomologicalComplex.comp_f, Category.assoc]
  rw [show (strictAugmentation R t P').f (p + 1) ≫
      (roosχ ((quotientTower R t).obj P') p).hom =
      biprod.lift 0 ((quotientProduct R t P').f (p + 1)) from
    roosAugment_χ _ _ p]
  rw [show ((quotientRoos R t).map f).f (p + 1) ≫
      (roosχ ((quotientTower R t).obj P') p).hom =
      (roosχ ((quotientTower R t).obj P) p).hom ≫
        biprod.map ((roosPmap ((quotientTower R t).map f)).f p)
          ((roosPmap ((quotientTower R t).map f)).f (p + 1)) from roosF_map_χ _ p]
  rw [← Category.assoc, show (strictAugmentation R t P).f (p + 1) ≫
      (roosχ ((quotientTower R t).obj P) p).hom =
      biprod.lift 0 ((quotientProduct R t P).f (p + 1)) from roosAugment_χ _ _ p]
  apply biprod.hom_ext
  · simp
  · simp only [Category.assoc, biprod.lift_snd, biprod.map_snd,
      biprod.lift_snd_assoc]
    exact congrArg (fun g ↦ g.f (p + 1)) hp

variable [HasDerivedCategory.{w}
  (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))]

/-- Principal quotient completion exists on the unbounded derived category, with
its universal counit and its prescribed quotient augmentation.

Source: Stacks Project, sites-cohomology.tex, Tags 06YS, 06YT and 0941;
steps 2, 4, 7 and 8 of lem-pur-finite-free-completion-exchange
(blueprint: lem-pur-principal-quotient-completion-exists).

Proof: The quotient maps form a strict natural augmentation. Its product is killed
by 1 minus the transition shift, so the canonical Roos lift defines an augmentation
with zero shifted-product component and quotient-product second component. Tensor
homotopies with each quotient, take products, and take the induced signed cone
homotopy; thus quotientRoos followed by localization factors through the homotopy
category. A quasi-isomorphism between K-flat complexes remains a quasi-isomorphism
after tensoring with each quotient, by the K-flat tensor comparison. Exact countable
products preserve these quasi-isomorphisms, and the cone triangle shows the same
for quotientRoos. Every complex admits a K-flat resolution with flat terms (06YS).
The resolving-class construction therefore gives its universal left derived functor,
whose counit is invertible on all K-flat complexes, regardless of termwise flatness.
Transport its counit from the homotopy category to cochains. The localized strict
augmentation is a natural map Q → quotientRoos ⋙ Q. Lift it through the universal
counit to obtain the completion unit. The factorization identity is unit_computes;
the explicit Roos lift gives coordinates. No regularity of the section is needed:
the definition derives tensor with the ordinary cokernel quotient itself. -/
theorem nonempty_model
    (t : (SheafOfModules.unit
      (SheafOfModules.derivedChangeRingIndependentCoefficients J R)).sections)
    [HasExactLimitsOfShape (Discrete ℕ)
      (ringedSiteModules.{r} (SheafOfModules.derivedChangeRingIndependentCoefficients J R))] :
    Nonempty (Model R t) := by
  classical
  obtain ⟨L, ε, hL, hε⟩ := exists_derivedQuotientRoos R t
  let := hL
  let α : DerivedCategory.Q ⋙ 𝟭 _ ⟶ quotientRoos R t ⋙ DerivedCategory.Q :=
    { app := fun P ↦ DerivedCategory.Q.map (strictAugmentation R t P)
      naturality := by
        intro P P' f
        simpa only [Functor.comp_map, Functor.id_map, ← Functor.map_comp] using
          congrArg DerivedCategory.Q.map (strictAugmentation_natural R t f) }
  refine ⟨{ completion := L
            counit := ε
            universal := hL
            computes := hε
            unit := L.leftDerivedLift ε (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟭 _) α
            augmentation := strictAugmentation R t
            coordinates := ?_
            unit_computes := ?_ }⟩
  · intro P p
    exact roosAugment_χ _ _ p
  · intro P
    exact L.leftDerived_fac_app ε (HomologicalComplex.quasiIso _ (.up ℤ)) (𝟭 _) α P

end CategoryTheory.PrincipalQuotientCompletion

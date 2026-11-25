/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.CategoryTheory.Functor.OfSequence
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.FromJoel.CategoryTheory.Monoidal.KFlat
public import WeilConjectures.Algebra.Homology.PrincipalKoszulQuotientTowers
/-! # Canonical principal Koszul and quotient towers

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(blueprint: def-pur-principal-koszul-quotient-towers).

The principal Koszul complexes are represented by mapping cones of multiplication on the
single complex. The transitions are the strict `t/id` and quotient maps,
with their tensor augmentations.
-/

@[expose] public section

set_option autoImplicit false

universe uC vC r ux vx

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory

variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}

private lemma endoPow_succ_left {D : Type ux} [Category.{vx, ux} D]
    {X : D} (f : X ⟶ X) (n : ℕ) : endoPow f (n + 1) = f ≫ endoPow f n := by
  induction n with
  | zero => simp [endoPow]
  | succ n ih =>
    simpa only [endoPow, Category.assoc] using congrArg (· ≫ f) ih

variable [EssentiallySmall.{r} C]
variable (R : Sheaf J CommRingCat.{r})

set_option hygiene false in
local notation "𝓞" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞

attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients

attribute [local instance 20000] principalKoszulHasSheafCompose




/-- The quotient augmentation from the principal Koszul cone to the degree-zero quotient.

Source: Stacks Project, algebraization.tex Tag 0A0E (blueprint:
def-pur-principal-koszul-quotient-towers).
-/
noncomputable def principalAugmentation
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    principalKoszul R t m ⟶ principalReduction R t m := by
  let f := (CochainComplex.singleFunctor (𝒜) 0).map
    (endoPow (globalSectionMultiplication R t) (m + 1))
  let g := (CochainComplex.singleFunctor (𝒜) 0).map
    (cokernel.π (endoPow (globalSectionMultiplication R t) (m + 1)))
  letI : HomologicalComplex.HasHomotopyCofiber f := inferInstance
  exact CochainComplex.mappingCone.descShortComplex
    (ShortComplex.mk f g (by
      dsimp [f, g]
      rw [← Functor.map_comp]
      rw [cokernel.condition]
      simp))





set_option backward.isDefEq.respectTransparency false in
/-- The augmentations commute with the specified strict transitions.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers).
Proof: the two composites vanish on the degree `-1` summand of the cone, and on its
other summand both are the quotient map to `O/t^(m+1)`. Cone extensionality gives equality. -/
theorem principalAugmentation_naturality
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    principalKoszulTransition R t m ≫ principalAugmentation R t m =
      principalAugmentation R t (m + 1) ≫ principalReductionTransition R t m := by
  let F := CochainComplex.singleFunctor 𝒜 0
  let a := globalSectionMultiplication R t
  let S (n : ℕ) : ShortComplex (CochainComplex 𝒜 ℤ) :=
    ShortComplex.mk (F.map (endoPow a (n + 1)))
      (F.map (cokernel.π (endoPow a (n + 1)))) (by
        rw [← F.map_comp, cokernel.condition, F.map_zero])
  let f : S (m + 1) ⟶ S m :=
    { τ₁ := F.map a
      τ₂ := 𝟙 _
      τ₃ := principalReductionTransition R t m
      comm₁₂ := (principalKoszul_transition_square R t m).symm
      comm₂₃ := by
        dsimp only [S, principalReductionTransition]
        rw [Category.id_comp, ← F.map_comp, cokernel.π_desc] }
  exact CochainComplex.mappingCone.map_descShortComplex (S (m + 1)) (S m) f



/-- The strict quotient comparison; its naturality is the first proof step of the node.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def principalTowerComparison (t : (SheafOfModules.unit 𝓞).sections) :
    principalKoszulTower R t ⟶ principalReductionTower R t :=
  NatTrans.ofOpSequence (principalAugmentation R t) (by
    simpa only [principalKoszulTower, principalReductionTower,
      Functor.ofOpSequence_map_homOfLE_succ] using
      principalAugmentation_naturality R t)


/-- Rearrange a strict tower map degree by degree.
Source: Stacks Tag 0941 (blueprint: def-pur-principal-koszul-quotient-towers). -/
def koszulTowerComplexMap {X Y : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ} (f : X ⟶ Y) :
    koszulTowerComplex R X ⟶ koszulTowerComplex R Y where
  f i := { app := fun n ↦ (f.app n).f i
           naturality := fun n m g ↦ congrArg (fun h ↦ h.f i) (f.naturality g) }
  comm' i j _ := NatTrans.ext (by funext n; exact (f.app n).comm i j)


private theorem tensorClosedUnitLeft_comm
    {A : Type*} [Category* A] [Preadditive A] [MonoidalCategory A]
    [(MonoidalCategory.curriedTensor A).PreservesZeroMorphisms]
    [∀ Z, ((MonoidalCategory.curriedTensor A).obj Z).PreservesZeroMorphisms]
    (D P : CochainComplex A ℤ)
    [HomologicalComplex.HasMapBifunctor D P (MonoidalCategory.curriedTensor A)
      (ComplexShape.up ℤ)]
    (u : MonoidalCategory.tensorUnit A ⟶ D.X 0) (hu : u ≫ D.d 0 1 = 0)
    (i j : ℤ) (hij : (ComplexShape.up ℤ).Rel i j) :
    ((MonoidalCategory.leftUnitor (P.X i)).inv ≫
      MonoidalCategory.whiskerRight u (P.X i) ≫
      HomologicalComplex.ιMapBifunctor D P (MonoidalCategory.curriedTensor A)
        (ComplexShape.up ℤ) 0 i i (zero_add i)) ≫
      (HomologicalComplex.mapBifunctor D P (MonoidalCategory.curriedTensor A)
        (ComplexShape.up ℤ)).d i j =
    P.d i j ≫ (MonoidalCategory.leftUnitor (P.X j)).inv ≫
      MonoidalCategory.whiskerRight u (P.X j) ≫
      HomologicalComplex.ιMapBifunctor D P (MonoidalCategory.curriedTensor A)
        (ComplexShape.up ℤ) 0 j j (zero_add j) := by
  simp only [Category.assoc, HomologicalComplex.mapBifunctor.d_eq,
    Preadditive.comp_add, HomologicalComplex.mapBifunctor.ι_D₁,
    HomologicalComplex.mapBifunctor.ι_D₂]
  rw [HomologicalComplex.mapBifunctor.d₁_eq' _ _ _ _
      (show (ComplexShape.up ℤ).Rel 0 1 from rfl),
    HomologicalComplex.mapBifunctor.d₂_eq _ _ _ _ 0 hij j (zero_add j)]
  dsimp only [MonoidalCategory.curriedTensor_map_app,
    MonoidalCategory.curriedTensor_obj_map]
  have hs₁ : ComplexShape.ε₁ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (0, i) = 1 := rfl
  have hs₂ : ComplexShape.ε₂ (ComplexShape.up ℤ) (ComplexShape.up ℤ)
      (ComplexShape.up ℤ) (0, i) = 1 := by simp
  have hz : MonoidalCategory.whiskerRight (0 : MonoidalCategory.tensorUnit A ⟶ D.X 1)
      (P.X i) = 0 := by
    simpa only [MonoidalCategory.curriedTensor_map_app, zero_app] using
      congrArg (fun f ↦ f.app (P.X i))
        ((MonoidalCategory.curriedTensor A).map_zero (MonoidalCategory.tensorUnit A)
          (D.X 1))
  rw [hs₁, hs₂, one_smul, one_smul,
    ← MonoidalCategory.comp_whiskerRight_assoc, hu, hz, zero_comp, comp_zero, zero_add,
    ← MonoidalCategory.whisker_exchange_assoc,
    ← MonoidalCategory.leftUnitor_inv_naturality_assoc]





/-- The canonical strict tensor comparison.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulTensorTowerComparison (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) :
    koszulTensorTower R P t ⟶ reductionTensorTower R P t :=
  Functor.whiskerRight (principalTowerComparison R t) (koszulTensorFunctor R P)



set_option backward.isDefEq.respectTransparency false in
/-- The augmentation followed by the quotient comparison is the prescribed quotient map.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers).
Proof: the cone inclusion followed by its cokernel augmentation equals the degree-zero
quotient projection (`mappingCone.inr_descShortComplex`). Applying the tensor functor and
precomposing with its unit inclusion gives the asserted equation. -/
theorem koszulRepresentativeAugmentation_quotient (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    koszulRepresentativeAugmentation R P t m ≫
        (koszulTensorTowerComparison R P t).app (op m) =
      koszulRepresentativeQuotient R P t m := by
  change (koszulTensorUnitInclusion R P ≫ (koszulTensorFunctor R P).map _) ≫
      (koszulTensorFunctor R P).map (principalAugmentation R t m) =
    koszulTensorUnitInclusion R P ≫ (koszulTensorFunctor R P).map _
  rw [Category.assoc, ← Functor.map_comp]
  let F := CochainComplex.singleFunctor 𝒜 0
  let a := endoPow (globalSectionMultiplication R t) (m + 1)
  let S : ShortComplex (CochainComplex 𝒜 ℤ) :=
    ShortComplex.mk (F.map a) (F.map (cokernel.π a)) (by
      rw [← F.map_comp, cokernel.condition, F.map_zero])
  exact congrArg (fun f ↦ koszulTensorUnitInclusion R P ≫
    (koszulTensorFunctor R P).map f)
      (CochainComplex.mappingCone.inr_descShortComplex S)



end CategoryTheory

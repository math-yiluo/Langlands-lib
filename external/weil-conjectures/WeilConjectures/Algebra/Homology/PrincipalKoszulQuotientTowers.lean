/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import Mathlib.Algebra.Homology.Functor
public import Mathlib.CategoryTheory.Functor.OfSequence
public import WeilConjectures.Algebra.Homology.KFlatIndependentCoefficients
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
/-! # Canonical principal Koszul and quotient towers

Source: Stacks Project, algebraization.tex Tag 0A0E and sites-cohomology.tex Tag 0941
(auxiliary; not a blueprint node).

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

/-- Iterated composite of an endomorphism.

Source: Stacks Project, algebraization.tex Tag 0A0E; this is the power of the regular
section used in the principal Koszul complex (auxiliary; not a blueprint node).
-/
noncomputable def endoPow {D : Type ux} [Category.{vx, ux} D] {X : D} (f : X ⟶ X) :
    ℕ → (X ⟶ X)
  | 0 => 𝟙 X
  | n + 1 => endoPow f n ≫ f

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

/-- Cache the existing sheaf-composition property on an essentially small site.
Source: Mathlib, `CategoryTheory.Sites.Whiskering` (auxiliary; not a blueprint node).
Proof: apply the existing instance. Naming this proof avoids repeated search when
constructing the actual single-complex maps and their cones. -/
theorem principalKoszulHasSheafCompose :
    J.HasSheafCompose (forget₂ CommRingCat.{r} RingCat.{r}) := by infer_instance

attribute [local instance 20000] principalKoszulHasSheafCompose

/-- Multiplication by a global section on the unit module sheaf.

Source: Stacks Project, algebraization.tex Tag 0A0E (auxiliary; not a blueprint node).
-/
noncomputable def globalSectionMultiplication
    (t : (SheafOfModules.unit 𝓞).sections) :
    SheafOfModules.unit 𝓞 ⟶ SheafOfModules.unit 𝓞 :=
  (SheafOfModules.unit 𝓞).unitHomEquiv.symm t

/-- The specified power multiplication map on the degree-zero ring complex.

Source: Stacks Project, algebraization.tex Tag 0A0E (auxiliary; not a blueprint node).
This named map shares the actual single-functor construction between the principal
cone and its component API, without unfolding the single-functor coherence record. -/
noncomputable def principalKoszulScalarComplex
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :=
  (CochainComplex.singleFunctor (𝒜) 0).map
    (endoPow (globalSectionMultiplication R t) (m + 1))

/-- Tensor with the representative in the K-flat (second) variable. The canonical symmetry
identifies this model with `P ⊗ Q_m`, including its maps and augmentations.
Source: Stacks Tags 06YN and 0941
(auxiliary; not a blueprint node). -/
noncomputable def koszulTensorFunctor (P : CochainComplex 𝒜 ℤ) :
    CochainComplex 𝒜 ℤ ⥤ CochainComplex 𝒜 ℤ :=
  (MonoidalCategory.curriedTensor 𝒜).map₂CochainComplex.flip.obj P

end CategoryTheory

namespace CategoryTheory

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
attribute [local instance 20000] principalKoszulHasSheafCompose


private lemma endoPow_succ_left {D : Type ux} [Category.{vx, ux} D]
    {X : D} (f : X ⟶ X) (n : ℕ) : endoPow f (n + 1) = f ≫ endoPow f n := by
  induction n with
  | zero => simp [endoPow]
  | succ n ih =>
    simpa only [endoPow, Category.assoc] using congrArg (· ≫ f) ih

end

end CategoryTheory

namespace CategoryTheory

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
variable {C : Type uC} [Category.{vC} C]
variable {J : GrothendieckTopology C}
variable [EssentiallySmall.{r} C]
variable (R : Sheaf J CommRingCat.{r})
attribute [local instance] SheafOfModules.isMonoidal_W_independentCoefficients
attribute [local instance] SheafOfModules.monoidalCategory
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients
attribute [local instance]
  SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients
attribute [local instance 20000] principalKoszulHasSheafCompose

set_option hygiene false in
local notation "𝓞" => (sheafCompose J
  (forget₂ CommRingCat.{r} RingCat.{r})).obj R
set_option hygiene false in
local notation "𝒜" => ringedSiteModules.{r} 𝓞


/-- The two-term principal Koszul complex in degrees `-1,0`, as a mapping cone.

Source: Stacks Project, algebraization.tex Tag 0A0E (blueprint:
def-pur-principal-koszul-quotient-towers).
-/
noncomputable def principalKoszul
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    CochainComplex (𝒜) ℤ :=
  CochainComplex.mappingCone (principalKoszulScalarComplex R t m)

/-- The quotient sheaf `O/t^(m+1)O` as a categorical cokernel.

Source: Stacks Project, algebraization.tex Tag 0A0E (blueprint:
def-pur-principal-koszul-quotient-towers).
-/
noncomputable def principalQuotient
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    𝒜 :=
  cokernel (endoPow (globalSectionMultiplication R t) (m + 1))

/-- The quotient complex concentrated in degree zero.

Source: Stacks Project, algebraization.tex Tag 0A0E (blueprint:
def-pur-principal-koszul-quotient-towers).
-/
noncomputable def principalReduction
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    CochainComplex (𝒜) ℤ :=
  (CochainComplex.singleFunctor (𝒜) 0).obj
    (principalQuotient R t m)

/-- The square defining the strict `t/id` Koszul transition.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers).
Proof: powers of one endomorphism commute by induction, and the single functor preserves
composition and identity. This is the transition calculation of the node's first proof step. -/
theorem principalKoszul_transition_square
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    (CochainComplex.singleFunctor 𝒜 0).map
        (endoPow (globalSectionMultiplication R t) (m + 2)) ≫ 𝟙 _ =
      (CochainComplex.singleFunctor 𝒜 0).map (globalSectionMultiplication R t) ≫
        (CochainComplex.singleFunctor 𝒜 0).map
          (endoPow (globalSectionMultiplication R t) (m + 1)) := by
  rw [Category.comp_id, ← Functor.map_comp, ← endoPow_succ_left]

/-- The strict Koszul transition: multiplication by `t` in degree `-1`, identity in degree 0.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def principalKoszulTransition
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    principalKoszul R t (m + 1) ⟶ principalKoszul R t m :=
  CochainComplex.mappingCone.map _ _
    ((CochainComplex.singleFunctor 𝒜 0).map (globalSectionMultiplication R t))
    (𝟙 _) (principalKoszul_transition_square R t m)

/-- The quotient map kills the next power.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers).
Proof: move one factor `t` to the left in `t^(m+2)` and use the cokernel equation for
`t^(m+1)`. This is the quotient transition calculation of the node's first proof step. -/
theorem principalQuotient_transition_zero
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    endoPow (globalSectionMultiplication R t) (m + 2) ≫
      cokernel.π (endoPow (globalSectionMultiplication R t) (m + 1)) = 0 := by
  rw [endoPow_succ_left _ (m + 1), Category.assoc,
    cokernel.condition, comp_zero]

/-- The strict quotient transition induced by the identity of the ring sheaf.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def principalReductionTransition
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    principalReduction R t (m + 1) ⟶ principalReduction R t m :=
  (CochainComplex.singleFunctor 𝒜 0).map
    (cokernel.desc _ (cokernel.π (endoPow (globalSectionMultiplication R t) (m + 1)))
      (principalQuotient_transition_zero R t m))

/-- The strict Koszul tower of complexes, indexed by `m+1`.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def principalKoszulTower (t : (SheafOfModules.unit 𝓞).sections) :
    ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ := Functor.ofOpSequence (principalKoszulTransition R t)

/-- The strict quotient tower of complexes, indexed by `m+1`.
Source: Stacks Tag 0A0E (blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def principalReductionTower (t : (SheafOfModules.unit 𝓞).sections) :
    ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ := Functor.ofOpSequence (principalReductionTransition R t)

/-- Rearrange a tower of complexes as a complex in the abelian category of strict towers.
Source: Stacks Tag 0941 (blueprint: def-pur-principal-koszul-quotient-towers). -/
def koszulTowerComplex (X : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ) :
    CochainComplex (ℕᵒᵖ ⥤ 𝒜) ℤ where
  X i :=
    { obj := fun n ↦ (X.obj n).X i
      map := fun f ↦ (X.map f).f i
      map_id := fun n ↦ by simp
      map_comp := fun f g ↦ by simp }
  d i j := { app := fun n ↦ (X.obj n).d i j }
  shape i j h := NatTrans.ext (by funext n; exact (X.obj n).shape i j h)
  d_comp_d' i j k _ _ := NatTrans.ext (by funext n; exact (X.obj n).d_comp_d i j k)

/-- Degreewise inclusion of `1 ⊗ x` into the total tensor with the degree-zero unit.
Source: Stacks Tags 03EK and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulTensorUnitComponent (P : CochainComplex 𝒜 ℤ) (i : ℤ) :
    P.X i ⟶ ((koszulTensorFunctor R P).obj
      ((CochainComplex.singleFunctor 𝒜 0).obj (SheafOfModules.unit 𝓞))).X i :=
  (MonoidalCategory.leftUnitor (P.X i)).inv ≫
    MonoidalCategory.whiskerRight
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit 𝓞)).inv (P.X i) ≫
    HomologicalComplex.ιMapBifunctor _ _ (MonoidalCategory.curriedTensor 𝒜)
      (ComplexShape.up ℤ) 0 i i (zero_add i)

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

set_option backward.isDefEq.respectTransparency false in
/-- The unit inclusion commutes with the total tensor differential.
Source: Stacks Tags 03EK and 0941
(blueprint: def-pur-principal-koszul-quotient-towers).
Proof: on the `(0,i)` summand, the first differential is zero and the second is
`1 ⊗ d_P` with sign `(-1)^0=1`. Naturality of the left unitor gives the equation. -/
theorem koszulTensorUnitComponent_comm (P : CochainComplex 𝒜 ℤ) (i j : ℤ) :
    P.d i j ≫ koszulTensorUnitComponent R P j =
      koszulTensorUnitComponent R P i ≫
        ((koszulTensorFunctor R P).obj
          ((CochainComplex.singleFunctor 𝒜 0).obj (SheafOfModules.unit 𝓞))).d i j := by
  by_cases hij : (ComplexShape.up ℤ).Rel i j
  · exact (tensorClosedUnitLeft_comm
      ((CochainComplex.singleFunctor 𝒜 0).obj (SheafOfModules.unit 𝓞)) P
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
        (SheafOfModules.unit 𝓞)).inv (by simp) i j hij).symm
  · simp only [HomologicalComplex.shape _ _ _ hij, comp_zero, zero_comp]

/-- The canonical chain map `P → O[0] ⊗ P` (inverse unit constraint).
Source: Stacks Tags 03EK and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulTensorUnitInclusion (P : CochainComplex 𝒜 ℤ) :
    P ⟶ (koszulTensorFunctor R P).obj
      ((CochainComplex.singleFunctor 𝒜 0).obj (SheafOfModules.unit 𝓞)) where
  f := koszulTensorUnitComponent R P
  comm' i j _ := (koszulTensorUnitComponent_comm R P i j).symm

/-- The strict tensor Koszul tower.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulTensorTower (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ :=
  principalKoszulTower R t ⋙ koszulTensorFunctor R P

/-- The strict tensor quotient tower.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def reductionTensorTower (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) : ℕᵒᵖ ⥤ CochainComplex 𝒜 ℤ :=
  principalReductionTower R t ⋙ koszulTensorFunctor R P

/-- The canonical quotient map from the representative to a reduction level.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulRepresentativeQuotient (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    P ⟶ (reductionTensorTower R P t).obj (op m) :=
  koszulTensorUnitInclusion R P ≫ (koszulTensorFunctor R P).map
    ((CochainComplex.singleFunctor 𝒜 0).map
      (cokernel.π (endoPow (globalSectionMultiplication R t) (m + 1))))

/-- The canonical level map from `P` into its tensor Koszul tower.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulRepresentativeAugmentation (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    P ⟶ (koszulTensorTower R P t).obj (op m) :=
  koszulTensorUnitInclusion R P ≫ (koszulTensorFunctor R P).map
    (CochainComplex.mappingCone.inr
      ((CochainComplex.singleFunctor 𝒜 0).map
        (endoPow (globalSectionMultiplication R t) (m + 1))))

set_option backward.isDefEq.respectTransparency false in
/-- Compatibility of the canonical strict augmentation.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers).
Proof: the cone transition is the identity on its degree-zero summand, so its composite
with the cone inclusion equals the next cone inclusion. Tensor functoriality gives the claim. -/
theorem koszulRepresentativeAugmentation_naturality (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) (m : ℕ) :
    koszulRepresentativeAugmentation R P t m =
      koszulRepresentativeAugmentation R P t (m + 1) ≫
        (koszulTensorTower R P t).map (homOfLE (Nat.le_succ m)).op := by
  dsimp only [koszulRepresentativeAugmentation, koszulTensorTower, Functor.comp_map,
    principalKoszulTower]
  rw [Functor.ofOpSequence_map_homOfLE_succ, Category.assoc, ← Functor.map_comp]
  dsimp only [principalKoszulTransition, principalKoszulScalarComplex]
  simp [CochainComplex.mappingCone.map]

/-- The canonical strict augmentation from the constant representative tower.
Source: Stacks Tags 0A0E and 0941
(blueprint: def-pur-principal-koszul-quotient-towers). -/
noncomputable def koszulStrictAugmentation (P : CochainComplex 𝒜 ℤ)
    (t : (SheafOfModules.unit 𝓞).sections) :
    (Functor.const ℕᵒᵖ).obj P ⟶ koszulTensorTower R P t :=
  NatTrans.ofOpSequence (koszulRepresentativeAugmentation R P t)
    (koszulRepresentativeAugmentation_naturality R P t)

end

end CategoryTheory

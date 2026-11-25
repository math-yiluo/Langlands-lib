/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.QuotientSectionTensor.QuotientSectionTensorNormalization
import all WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Coefficient.CoefficientScalarTensorRealization
import all WeilConjectures.AlgebraicGeometry.InternalPullNormalizationExistence
import all WeilConjectures.CategoryTheory.Derived.DerivedTensorRightExact

/-! # Ordinary signed-total maps for the quotient tensor square

The source and target computation maps are actual localization counits. The two
ordinary paths retain the canonical balancing isomorphism and signed tensorators.

## References

* Stacks 03EL and 07A4
* Stacks 06YY, 07A4 and 0G7E
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

attribute [local irreducible] CategoryTheory.Functor.leftDerivedFunctor
  CategoryTheory.Functor.mapDerivedCategory DerivedCategory.monoidalClosed
  CategoryTheory.Mod.monoidalClosed
  CategoryTheory.Sheaf.monoidalCategory
  DerivedCategory.monoidalCategoryOfMonoidalClosedBraidedCategory
  AlgebraicGeometry.ProEtale.upperStarFromPoint
  CategoryTheory.Mod.extendScalars CategoryTheory.Mod.comap
  AlgebraicGeometry.ProEtale.CondensedRing.upperStar
  AlgebraicGeometry.ProEtale.CondensedRing.internalScalarMonoidal
  AlgebraicGeometry.ProEtale.CondensedRing.monoidal_upperStar

universe u u₁ u₂ u₃ u₄

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale.QuotientTensorFlatModel

open QuotientChange QuotientSectionTensor IntegralQuotient

variable {R S : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}}
  [MonObj R] [IsCommMonObj R] [MonObj S] [IsCommMonObj S]
  (a : R ⟶ S) [IsMonHom a] {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- Termwise geometric pullback of a complex. -/
abbrev pullComplex (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] :=
  (CondensedRing.upperStar B f).mapHomologicalComplex (.up ℤ)

/-- Termwise coefficient extension of a complex. -/
abbrev scalarComplex (T : Scheme.{u}) := (extension a T).mapHomologicalComplex (.up ℤ)

/-- The signed-total ordinary pullback tensorator. -/
def totalPull (B : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
    [MonObj B] [IsCommMonObj B] (P Q : CochainComplex (Modules B Y) ℤ) :
    (pullComplex f B).obj (P ⊗ Q) ⟶
      (pullComplex f B).obj P ⊗ (pullComplex f B).obj Q :=
  letI : (CondensedRing.upperStar B f).OplaxMonoidal :=
    (CondensedRing.monoidal_upperStar B f).toOplaxMonoidal
  ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
    (CondensedRing.upperStar B f)).app P).app Q

/-- The ordinary balancing comparison prolonged to complexes. -/
def totalBalance (P : CochainComplex (Modules R Y) ℤ) :
    (pullComplex f S).obj ((scalarComplex a Y).obj P) ⟶
      (scalarComplex a X).obj ((pullComplex f R).obj P) :=
  (NatTrans.mapHomologicalComplex (CondensedRing.pullIso a f).inv (.up ℤ)).app P

/-- The ordinary path that balances before taking the two tensorators. -/
def ordinaryLeft (P Q : CochainComplex (Modules R Y) ℤ) :
    (pullComplex f S).obj ((scalarComplex a Y).obj (P ⊗ Q)) ⟶
      (scalarComplex a X).obj ((pullComplex f R).obj P) ⊗
        (scalarComplex a X).obj ((pullComplex f R).obj Q) :=
  totalBalance a f (P ⊗ Q) ≫
    (scalarComplex a X).map (totalPull f R P Q) ≫
    totalScalar a X ((pullComplex f R).obj P) ((pullComplex f R).obj Q)

/-- The ordinary path that takes the tensorators before balancing the factors. -/
def ordinaryRight (P Q : CochainComplex (Modules R Y) ℤ) :
    (pullComplex f S).obj ((scalarComplex a Y).obj (P ⊗ Q)) ⟶
      (scalarComplex a X).obj ((pullComplex f R).obj P) ⊗
        (scalarComplex a X).obj ((pullComplex f R).obj Q) :=
  (pullComplex f S).map (totalScalar a Y P Q) ≫
    totalPull f S ((scalarComplex a Y).obj P) ((scalarComplex a Y).obj Q) ≫
    (totalBalance a f P ⊗ₘ totalBalance a f Q)

private theorem signed_square
    {C₁ : Type u₁} [Category.{u + 1} C₁] [Abelian C₁]
    [IsGrothendieckAbelian.{u + 1} C₁] [MonoidalCategory C₁]
    [MonoidalPreadditive C₁] [MonoidalClosed C₁] [BraidedCategory C₁]
    {C₂ : Type u₂} [Category.{u + 1} C₂] [Abelian C₂]
    [IsGrothendieckAbelian.{u + 1} C₂] [MonoidalCategory C₂]
    [MonoidalPreadditive C₂] [MonoidalClosed C₂] [BraidedCategory C₂]
    {C₃ : Type u₃} [Category.{u + 1} C₃] [Abelian C₃]
    [IsGrothendieckAbelian.{u + 1} C₃] [MonoidalCategory C₃]
    [MonoidalPreadditive C₃] [MonoidalClosed C₃] [BraidedCategory C₃]
    {C₄ : Type u₄} [Category.{u + 1} C₄] [Abelian C₄]
    [IsGrothendieckAbelian.{u + 1} C₄] [MonoidalCategory C₄]
    [MonoidalPreadditive C₄] [MonoidalClosed C₄] [BraidedCategory C₄]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (H : C₁ ⥤ C₃) (K : C₃ ⥤ C₄)
    [F.Additive] [G.Additive] [H.Additive] [K.Additive]
    [F.IsLeftAdjoint] [G.IsLeftAdjoint] [H.IsLeftAdjoint] [K.IsLeftAdjoint]
    [F.Monoidal] [G.Monoidal] [H.Monoidal] [K.Monoidal]
    (τ : H ⋙ K ⟶ F ⋙ G) [NatTrans.IsMonoidal τ]
    (P Q : CochainComplex C₁ ℤ) :
    (NatTrans.mapHomologicalComplex τ (.up ℤ)).app (P ⊗ Q) ≫
        (G.mapHomologicalComplex (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) F).app P).app Q) ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) G).app
          ((F.mapHomologicalComplex (.up ℤ)).obj P)).app
            ((F.mapHomologicalComplex (.up ℤ)).obj Q) =
      (K.mapHomologicalComplex (.up ℤ)).map
          (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) H).app P).app Q) ≫
        ((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ) K).app
          ((H.mapHomologicalComplex (.up ℤ)).obj P)).app
            ((H.mapHomologicalComplex (.up ℤ)).obj Q) ≫
        ((NatTrans.mapHomologicalComplex τ (.up ℤ)).app P ⊗ₘ
          (NatTrans.mapHomologicalComplex τ (.up ℤ)).app Q) := by
  have h := Functor.mapHomologicalComplexδNatTrans_naturality τ P Q
  rw [Functor.mapHomologicalComplexδNatTrans_comp,
    Functor.mapHomologicalComplexδNatTrans_comp] at h
  exact h.trans (Category.assoc _ _ _)

/-- The ordinary balancing square, including all signed-total summands. -/
theorem ordinary_square (P Q : CochainComplex (Modules R Y) ℤ) :
    ordinaryLeft a f P Q = ordinaryRight a f P Q := by
  let := CondensedRing.internalScalarMonoidal a X
  let := CondensedRing.internalScalarMonoidal a Y
  let := CondensedRing.monoidal_upperStar R f
  let := CondensedRing.monoidal_upperStar S f
  have : NatTrans.IsMonoidal (CondensedRing.pullIso a f).inv :=
    CondensedRing.scalarPull_monoidal a f
  have h := signed_square (CondensedRing.upperStar R f) (extension a X)
    (extension a Y) (CondensedRing.upperStar S f) (CondensedRing.pullIso a f).inv P Q
  dsimp only [ordinaryLeft, ordinaryRight, totalBalance, totalPull, totalScalar]
  set_option backward.isDefEq.respectTransparency true in
    exact h

/-- Compute the scalar/geometric composite on one factor. -/
def factorCompute (P : CochainComplex (Modules R Y) ℤ) :
    (D a X).obj ((L R f).obj (DerivedCategory.Q.obj P)) ⟶
      DerivedCategory.Q.obj ((scalarComplex a X).obj ((pullComplex f R).obj P)) :=
  (D a X).map (computePull f P) ≫ compute a X ((pullComplex f R).obj P)

/-- The common target comparison, without cancelling a tensor localization map. -/
def targetCompute (P Q : CochainComplex (Modules R Y) ℤ) :=
  factorCompute a f P ⊗ₘ factorCompute a f Q

/-- Compute the source by scalar extension followed by geometric pullback. -/
def sourceCompute (P Q : CochainComplex (Modules R Y) ℤ) :
    (L S f).obj ((D a Y).obj (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj Q)) ⟶
      DerivedCategory.Q.obj ((pullComplex f S).obj ((scalarComplex a Y).obj (P ⊗ Q))) :=
  (L S f).map ((D a Y).map (Functor.LaxMonoidal.μ DerivedCategory.Q P Q)) ≫
    (L S f).map (compute a Y (P ⊗ Q)) ≫
    computePull f ((scalarComplex a Y).obj (P ⊗ Q))

/-- The localization tensorator on the common target complexes. -/
abbrev targetLocalization (P Q : CochainComplex (Modules R Y) ℤ) :=
  Functor.LaxMonoidal.μ DerivedCategory.Q
    ((scalarComplex a X).obj ((pullComplex f R).obj P))
    ((scalarComplex a X).obj ((pullComplex f R).obj Q))

/-- Convert a localized ordinary tensor to the tensor of the localized factors. -/
def targetTensor (P Q : CochainComplex (Modules R Y) ℤ)
    [IsIso (targetLocalization a f P Q)] :=
  inv (targetLocalization a f P Q)

private theorem compute_scalar_isIso (T : Scheme.{u})
    (P : CochainComplex (Modules R T) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P) :
    IsIso (compute a T P) := by
  have hs : IsIso ((scalarCounit a T).app
      ((HomotopyCategory.quotient _ _).obj P)) := by
    unfold scalarCounit D
    exact (extension a T).isIso_leftDerivedFunctorCounit_app_of_kFlat P hP
  unfold compute
  infer_instance

private theorem compute_pull_isIso (P : CochainComplex (Modules R Y) ℤ) :
    IsIso (computePull f P) := by
  have hp : IsIso (pullCounit (Λ := R) f) := by
    unfold pullCounit L CondensedRing.moduleObjectDerivedPullback
    exact Functor.isIso_leftDerivedFunctorCounit (CondensedRing.upperStar R f)
  unfold computePull
  infer_instance

variable [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules R T)]
  [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)]

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)] in
/-- The common target computation is invertible on K-flat factors. -/
theorem targetCompute_isIso (P Q : CochainComplex (Modules R Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q) :
    IsIso (targetCompute a f P Q) := by
  have hp := QuotientChange.pull_preserves_kFlat (Λ := R) f P hP
  have hq := QuotientChange.pull_preserves_kFlat (Λ := R) f Q hQ
  have := compute_pull_isIso f P
  have := compute_pull_isIso f Q
  have := compute_scalar_isIso a X ((pullComplex f R).obj P) hp
  have := compute_scalar_isIso a X ((pullComplex f R).obj Q) hq
  unfold targetCompute factorCompute
  infer_instance

omit [∀ T : Scheme.{u}, HasDerivedCategory.{u + 1} (ModuleRingedComparison.modules S T)] in
/-- Tensor normalization makes the target localization tensorator invertible. -/
theorem targetLocalization_isIso
    (bX : TensorIso a X) (hbX : QuotientSectionTensor.TensorNormalized a X bX)
    (P Q : CochainComplex (Modules R Y) ℤ)
    (hP : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat P)
    (hQ : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat Q)
    (hPflat : ∀ i : ℤ, ObjectProperty.flat (P.X i))
    (hQflat : ∀ i : ℤ, ObjectProperty.flat (Q.X i)) :
    IsIso (targetLocalization a f P Q) := by
  let FP := (pullComplex f R).obj P
  let FQ := (pullComplex f R).obj Q
  have hp := QuotientChange.pull_preserves_kFlat (Λ := R) f P hP
  have hq := QuotientChange.pull_preserves_kFlat (Λ := R) f Q hQ
  have hpf : ∀ i : ℤ, ObjectProperty.flat (FP.X i) := fun i ↦
    Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar R f) (hPflat i)
  have hqf : ∀ i : ℤ, ObjectProperty.flat (FQ.X i) := fun i ↦
    Functor.PreservesFlat.flat_obj (F := CondensedRing.upperStar R f) (hQflat i)
  have ht : (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat (FP ⊗ FQ) :=
    (HomologicalComplex.quasiIso _ (.up ℤ)).kFlat.prop_tensor hp hq
  have := compute_scalar_isIso a X FP hp
  have := compute_scalar_isIso a X FQ hq
  have := compute_scalar_isIso a X (FP ⊗ FQ) ht
  have := Functor.tensorator_Q_isIso FP FQ hq
  let := CondensedRing.internalScalarMonoidal a X
  have hδ : IsIso (totalScalar a X FP FQ) := by
    change IsIso (((Functor.OplaxMonoidal.mapHomologicalComplexδNatTrans (.up ℤ)
      (extension a X)).app FP).app FQ)
    infer_instance
  have hn := hbX FP FQ hp hq hpf hqf
  have hi : IsIso (bX.hom.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) ≫
      (compute a X FP ⊗ₘ compute a X FQ) ≫ targetLocalization a f P Q) := by
    rw [hn]
    infer_instance
  have : IsIso ((bX.hom.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) ≫
      (compute a X FP ⊗ₘ compute a X FQ)) ≫ targetLocalization a f P Q) := by
    simpa only [Category.assoc] using hi
  exact IsIso.of_isIso_comp_left
    (bX.hom.app (DerivedCategory.Q.obj FP, DerivedCategory.Q.obj FQ) ≫
      (compute a X FP ⊗ₘ compute a X FQ)) (targetLocalization a f P Q)

end AlgebraicGeometry.ProEtale.QuotientTensorFlatModel

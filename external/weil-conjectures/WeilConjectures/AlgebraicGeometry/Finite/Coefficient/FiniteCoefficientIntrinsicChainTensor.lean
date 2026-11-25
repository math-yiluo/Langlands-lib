/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.SixFunctors.Etale.EtaleFiniteCoefficientHomArrow
public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModuleIntrinsicComparison
public import WeilConjectures.Algebra.Homology.KFlatCoefficientUniverse
public import WeilConjectures.Algebra.Homology.SmoothPurity.KFlatSupplement
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Homology.BifunctorShift
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Limits.EssentiallySmall
public import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientIntrinsicTensor
import WeilConjectures.AlgebraicGeometry.ProEtale.Constant.ProEtaleConstantModuleEncoding
import WeilConjectures.CategoryTheory.Sites.PushforwardMonoidal
import WeilConjectures.Mathlib.Algebra.Homology.Bifunctor
/-! # Pure-tensor normalization for the finite intrinsic comparison on complexes -/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme WeilConjectures
namespace FiniteCoefficientTotalComparison

/-- A total-complex tensor comparison with the functor and instance data shared.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
def ChainIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] : Type _ :=
  (G.mapHomologicalComplex (.up ℤ)).obj (HomologicalComplex.tensorObj P Q) ≅
    HomologicalComplex.mapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)

end FiniteCoefficientTotalComparison

private def curryTensorComparison
    {C D : Type*} [Category C] [Category D] [MonoidalCategory C] [MonoidalCategory D]
    (G : C ⥤ D) (e : FiniteCoefficientTotalComparison.Ordinary G) :
    (Functor.postcompose₂.obj G).obj (curriedTensor C) ⟶
      (((Functor.whiskeringLeft₂ D).obj G).obj G).obj (curriedTensor D) :=
  { app := fun M ↦
      { app := fun N ↦ e.hom.app (M, N)
        naturality := by
          intro N N' f
          simpa using e.hom.naturality (X := (M, N)) (Y := (M, N')) (𝟙 M, f) }
    naturality := by
      intro M M' f
      apply NatTrans.ext
      funext N
      simpa using e.hom.naturality (X := (M, N)) (Y := (M', N)) (f, 𝟙 N) }

private def liftTensorIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] :
    FiniteCoefficientTotalComparison.ChainIso G P Q := by
  let τ := curryTensorComparison G e
  have (M N : C) : IsIso ((τ.app M).app N) := (e.app (M, N)).isIso_hom
  exact asIso (HomologicalComplex.mapBifunctorComparison τ (.up ℤ) P Q)

private theorem liftTensorIso_ι
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D] [HasZeroObject C]
    [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (p q k : ℤ) (h : p + q = k) :
    G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫
        (liftTensorIso G e P Q).hom.f k =
      (e.app (P.X p, Q.X q)).hom ≫
        HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
          ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h := by
  exact HomologicalComplex.map_ιMapBifunctor_mapBifunctorComparisonX
    (curryTensorComparison G e) (.up ℤ) P Q p q k h

namespace FiniteCoefficientTotalComparison

/-- A normalized tensor comparison on all total summands.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
def normalizedTensorEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h

/-- Total normalization for a specified ordinary tensor normalization.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
def Normalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive]
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
  ∃ e, N e ∧ normalizedTensorEquation G e P Q a

end FiniteCoefficientTotalComparison

private def totalIsoEquation
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)]
    (a : FiniteCoefficientTotalComparison.ChainIso G P Q) : Prop :=
      ∀ (p q k : ℤ) (h : p + q = k),
        G.map (HomologicalComplex.ιTensorObj P Q p q k h) ≫ a.hom.f k =
          (e.app (P.X p, Q.X q)).hom ≫
            HomologicalComplex.ιMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
              ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ) p q k h

private theorem normalizedTotalIso
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (e : FiniteCoefficientTotalComparison.Ordinary G)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] :
    ∃! a, totalIsoEquation G e P Q a := by
  refine ⟨liftTensorIso G e P Q, liftTensorIso_ι G e P Q, ?_⟩
  intro a ha
  apply Iso.ext
  ext k : 1
  apply HomologicalComplex.mapBifunctor.hom_ext_of_map G
  intro p q h
  exact (ha p q k h).trans (liftTensorIso_ι G e P Q p q k h).symm

private theorem normalizedTotalIsoForNormalization
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasZeroObject C] [MonoidalCategory C] [MonoidalPreadditive C] [MonoidalCategory D]
    [(curriedTensor D).PreservesZeroMorphisms]
    [∀ M, ((curriedTensor D).obj M).PreservesZeroMorphisms]
    (G : C ⥤ D) [G.Additive] [PreservesColimitsOfSize.{0, 0} G]
    (N : (FiniteCoefficientTotalComparison.Ordinary G) → Prop)
    (hE : ∃ e, N e) (hN : ∀ e d, N e → N d → d = e)
    (P Q : CochainComplex C ℤ) [HomologicalComplex.HasTensor P Q]
    [HomologicalComplex.HasMapBifunctor ((G.mapHomologicalComplex (.up ℤ)).obj P)
      ((G.mapHomologicalComplex (.up ℤ)).obj Q) (curriedTensor D) (.up ℤ)] :
    ∃! a, FiniteCoefficientTotalComparison.Normalization G N P Q a := by
  obtain ⟨e, he⟩ := hE
  obtain ⟨a, ha, hu⟩ := normalizedTotalIso G e P Q
  refine ⟨a, ⟨e, he, ha⟩, ?_⟩
  rintro b ⟨d, hd, hb⟩
  have hde := hN e d he hd
  subst d
  exact hu b hb

namespace AlgebraicGeometry.ProEtale
variable (X : Scheme.{u}) (A : Type u) [CommRing A] [Finite A]
attribute [local instance] finiteCoefficientIntrinsicMonoidal

private def nuAdjointMap
    (M : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (N : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (f : (ProEtale.finiteCoefficientIntrinsicComparison X A).obj M ⟶ N) :
    (ProEtale.comparisonUpperStar (ModuleCat.{u + 1}
      (ULift.{u + 1, u} A)) X).obj M ⟶
      (Scheme.proEtaleModuleRestriction X A).obj
        N := by
  let a := (PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap X
      A)).homEquiv _ N f
  exact ⟨{ app := a.app
           naturality := fun _ _ g ↦ by
             ext x
             exact ConcreteCategory.congr_hom (a.naturality g) x }⟩

omit [Finite A] in
private theorem nu_tensor_hom_ext
    (M N : Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A)))
    (V : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A))
    (f g : (ProEtale.finiteCoefficientIntrinsicComparison X A).obj (M ⊗ N) ⟶ V)
    (h : ∀ (U : X.Etale) (x : M.obj.obj (op U)) (y : N.obj.obj (op U)),
      f.val.app (op (X.toProEt.obj U)) (finiteCoefficientComparisonSection X A (M ⊗ N) U
        (finiteCoefficientEtalePure X A M N U x y)) =
      g.val.app (op (X.toProEt.obj U)) (finiteCoefficientComparisonSection X A (M ⊗ N) U
        (finiteCoefficientEtalePure X A M N U x y))) : f = g := by
  have ha : nuAdjointMap X A (M ⊗ N) V f = nuAdjointMap X A (M ⊗ N) V g := by
    apply ((ProEtale.comparisonAdjunction (ModuleCat.{u + 1}
      (ULift.{u + 1, u} A)) X).homEquiv _ _).injective
    apply Sheaf.hom_ext_of_μ_comp
    apply NatTrans.ext
    funext U
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro x y
    exact h U.unop x y
  apply ((PresheafOfModules.sheafificationAdjunction
    (ProEtale.finiteCoefficientIntrinsicScalarMap X
      A)).homEquiv _ V).injective
  ext U x
  exact congrArg (fun z ↦ z.hom.app U x) ha

private theorem nu_preservesColimits :
    PreservesColimitsOfSize.{0, 0} (finiteCoefficientIntrinsicComparison X A) := by
  have := (ProEtale.finiteCoefficientIntrinsicRealization_exact X
    A).1
  unfold finiteCoefficientIntrinsicComparison
  infer_instance

/-- The intrinsic tensor preserves zero maps in its first variable.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicTensorZero :
    (@curriedTensor.{u + 1, u + 2}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) _
        (finiteCoefficientIntrinsicMonoidal X A)).PreservesZeroMorphisms :=
  @SheafOfModules.preservesZeroMorphisms_curriedTensor_independentCoefficients.{u + 1, u, u + 1}
     X.ProEt _ (essentiallySmallSelf.{0, u, u + 1} _)
      (Scheme.ProEt.topology X) (Scheme.proEtaleConstantRing X A)

/-- The intrinsic tensor preserves zero maps in its second variable.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicTensorObjZero
    (M : Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) :
    ((@curriedTensor.{u + 1, u + 2}
      (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)) _
        (finiteCoefficientIntrinsicMonoidal X A)).obj M).PreservesZeroMorphisms :=
  @SheafOfModules.preservesZeroMorphisms_curriedTensor_obj_independentCoefficients.{u + 1, u, u + 1}
     X.ProEt _ (essentiallySmallSelf.{0, u, u + 1} _)
      (Scheme.ProEt.topology X) (Scheme.proEtaleConstantRing X A) M

/-- The source totalization instance, shared before using its normalized comparison.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicSourceHasTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    HomologicalComplex.HasTensor P Q := by infer_instance

/-- The target totalization instance, shared before using its normalized comparison.
Source: Stacks 06YN (blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
instance finiteCoefficientIntrinsicTargetHasTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    HomologicalComplex.HasMapBifunctor
      (((finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex (.up ℤ)).obj P)
      (((finiteCoefficientIntrinsicComparison X A).mapHomologicalComplex (.up ℤ)).obj Q)
      (curriedTensor (Scheme.proEtaleRingModules X (Scheme.proEtaleConstantRing X A)))
      (.up ℤ) := by infer_instance

attribute [local irreducible] finiteCoefficientIntrinsicComparison comparisonUpperStar
  SheafOfModules.monoidalCategory Sheaf.monoidalCategory

omit [Finite A] in
private theorem ordinaryNormalization_unique
    (e d : FiniteCoefficientTotalComparison.Ordinary
      (finiteCoefficientIntrinsicComparison X A))
    (he : FiniteCoefficientTensorNormalization X A e)
    (hd : FiniteCoefficientTensorNormalization X A d) : d = e := by
  apply Iso.ext
  apply NatTrans.ext
  funext M
  apply nu_tensor_hom_ext X A M.1 M.2 _
  intro U x y
  exact (hd M.1 M.2 U x y).trans (he M.1 M.2 U x y).symm

/-- The total comparison is normalized on each tensor summand by the ordinary comparison.
Source: Stacks 03EK and 06YN
(blueprint: lem-sf-finite-intrinsic-chain-tensor-generators).
The ordinary normalization uniquely fixes the map on all local pure tensors.
The displayed summand equation is equivalent to its total-section version by
naturality of the comparison unit, the ordinary pure-tensor formula, and the two
adjunctions followed by sheaf-tensor extensionality. -/
def FiniteCoefficientChainTensorNormalization :=
  FiniteCoefficientTotalComparison.Normalization (finiteCoefficientIntrinsicComparison X A)
    (FiniteCoefficientTensorNormalization X A)

/-- The termwise finite intrinsic comparison has a unique normalized total tensor isomorphism.
Source: Stacks 03EK and 06YN
(blueprint: lem-sf-finite-intrinsic-chain-tensor-generators).
Proof: choose the ordinary comparison normalized on pure sections. The comparison
preserves coproducts because it is a composite of a left adjoint and an equivalence.
The total-bifunctor comparison is an isomorphism and satisfies the summand equation.
For uniqueness, the two adjunctions and sheaf-tensor extensionality first identify
the ordinary comparison. Coproduct extensionality then identifies every degree map
of the total comparison. Additivity respects the signed differential. -/
theorem finiteCoefficientIntrinsicChainTensor_existsUnique
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    ∃! a : FiniteCoefficientTotalComparison.ChainIso
      (finiteCoefficientIntrinsicComparison X A) P Q,
      FiniteCoefficientChainTensorNormalization X A P Q a := by
  have := nu_preservesColimits X A
  exact normalizedTotalIsoForNormalization (finiteCoefficientIntrinsicComparison X A)
    (FiniteCoefficientTensorNormalization X A) (finiteCoefficientIntrinsicTensor_generators X A)
    (ordinaryNormalization_unique X A) P Q

/-- The normalized chain comparison, shared before coefficient specialization.
Its value is determined by the preceding uniqueness theorem.
Source: Stacks 03EK, 06YN
(blueprint: lem-sf-finite-intrinsic-chain-tensor-generators). -/
def finiteCoefficientIntrinsicChainTensor
    (P Q : CochainComplex (Sheaf X.smallEtaleTopology
      (ModuleCat.{u + 1} (ULift.{u + 1, u} A))) ℤ) :
    FiniteCoefficientTotalComparison.ChainIso (finiteCoefficientIntrinsicComparison X A) P Q :=
  (finiteCoefficientIntrinsicChainTensor_existsUnique X A P Q).choose

end AlgebraicGeometry.ProEtale

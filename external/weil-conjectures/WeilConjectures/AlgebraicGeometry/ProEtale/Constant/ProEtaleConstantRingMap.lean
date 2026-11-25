/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Finite.ProEtaleFiniteModulesSupplement
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.SixFunctors.ProEtale.FiniteCoefficient.UpperLowerStar.Defs
public import WeilConjectures.AlgebraicGeometry.ProEtaleDerivedCategory
public import Mathlib.AlgebraicGeometry.Sites.Proetale
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import Mathlib.CategoryTheory.Sites.Equivalence
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.CategoryTheory.Sites.Sheafification
public import WeilConjectures.CategoryTheory.Adjunction.LiftsGroupRingObjects
public import Mathlib.CategoryTheory.Monoidal.CommGrp_
public import Mathlib.CategoryTheory.Monoidal.Ring
public import Mathlib.CategoryTheory.Adjunction.Limits
public import WeilConjectures.CategoryTheory.Adjunction.LiftedCommRingBranch
import Mathlib.CategoryTheory.Sites.LocallyBijective
import WeilConjectures.Mathlib.CategoryTheory.Sites.ConstantSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.Proetale

/-!
# The canonical inverse-image map for finite pro-etale coefficients

The coefficient objects are the recorded sheafifications of continuous functions on
connected components. The direct-image map is constructed on these functions by
precomposition with the fibre-product projection and then extended by sheafification.

## References

* Stacks Tags 04B3, 0H7J and 09A5
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

namespace ProEtale

variable {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
  [Ring Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ]

/-- Pull a continuous function back to the fibre product and take its sheafified section.
This sends a constant `a` to its constant scalar section on the fibre product. -/
noncomputable def finiteCoefficientDirectImageApp (W : V.ProEtᵒᵖ) :
    (finiteCoefficientPresheaf V Λ).obj W ⟶
      ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ)).obj.obj W :=
  RingCat.ofHom
    { toFun := fun s ↦ s.comp
        ⟨(pullback.fst W.unop.hom f).continuous.connectedComponentsMap,
          (pullback.fst W.unop.hom f).continuous.connectedComponentsMap_continuous⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl
      map_zero' := rfl
      map_add' := fun _ _ ↦ rfl } ≫
    (toSheafify (Scheme.ProEt.topology U) (finiteCoefficientPresheaf U Λ)).app
      ((Scheme.proEtaleBaseChange f).op.obj W)

/-- The fibre-product section maps commute with restriction. -/
theorem finiteCoefficientDirectImageApp_naturality
    {W W' : V.ProEtᵒᵖ} (a : W ⟶ W') :
    (finiteCoefficientPresheaf V Λ).map a ≫ finiteCoefficientDirectImageApp f Λ W' =
      finiteCoefficientDirectImageApp f Λ W ≫
        ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (finiteCoefficientRingSheaf U Λ)).obj.map a := by
  let p (W : V.ProEtᵒᵖ) : (finiteCoefficientPresheaf V Λ).obj W ⟶
      (finiteCoefficientPresheaf U Λ).obj ((Scheme.proEtaleBaseChange f).op.obj W) :=
    RingCat.ofHom
      { toFun := fun s ↦ s.comp
          ⟨(pullback.fst W.unop.hom f).continuous.connectedComponentsMap,
            (pullback.fst W.unop.hom f).continuous.connectedComponentsMap_continuous⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl
        map_zero' := rfl
        map_add' := fun _ _ ↦ rfl }
  have hp : (finiteCoefficientPresheaf V Λ).map a ≫ p W' =
      p W ≫ (finiteCoefficientPresheaf U Λ).map
        ((Scheme.proEtaleBaseChange f).op.map a) := by
    apply RingCat.hom_ext
    apply RingHom.ext
    intro s
    change C(ConnectedComponents W.unop.left, Λ) at s
    apply ContinuousMap.ext
    intro c
    obtain ⟨x, rfl⟩ := ConnectedComponents.surjective_coe c
    change s (ConnectedComponents.mk _) = s (ConnectedComponents.mk _)
    congr 2
    have hproj : ((Scheme.proEtaleBaseChange f).map a.unop).left ≫
        pullback.fst W.unop.hom f =
        pullback.fst W'.unop.hom f ≫ a.unop.left := by
      exact pullback.lift_fst _ _ _
    exact (congrArg (fun g : ((Scheme.proEtaleBaseChange f).obj W'.unop).left ⟶
      W.unop.left ↦ g x) hproj).symm
  let η := toSheafify (Scheme.ProEt.topology U) (finiteCoefficientPresheaf U Λ)
  change (finiteCoefficientPresheaf V Λ).map a ≫ (p W' ≫ η.app _) =
    (p W ≫ η.app _) ≫ (finiteCoefficientRingSheaf U Λ).obj.map _
  calc
    _ = ((finiteCoefficientPresheaf V Λ).map a ≫ p W') ≫ η.app _ :=
      (Category.assoc _ _ _).symm
    _ = (p W ≫ (finiteCoefficientPresheaf U Λ).map
        ((Scheme.proEtaleBaseChange f).op.map a)) ≫ η.app _ :=
      congrArg (fun g ↦ g ≫ η.app _) hp
    _ = p W ≫ ((finiteCoefficientPresheaf U Λ).map
        ((Scheme.proEtaleBaseChange f).op.map a) ≫ η.app _) := Category.assoc _ _ _
    _ = p W ≫ (η.app _ ≫ (finiteCoefficientRingSheaf U Λ).obj.map _) :=
      congrArg (fun g ↦ p W ≫ g) (η.naturality ((Scheme.proEtaleBaseChange f).op.map a))
    _ = _ := (Category.assoc _ _ _).symm

/-- The presheaf map underlying rho: pull functions back along the first projection.
On each open fibre it is the specified constant section, so its value is precisely
what the open-fibre gluing construction gives. -/
noncomputable def finiteCoefficientDirectImagePresheafMap :
    finiteCoefficientPresheaf V Λ ⟶
      ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ)).obj where
  app := finiteCoefficientDirectImageApp f Λ
  naturality _ _ a := finiteCoefficientDirectImageApp_naturality f Λ a

/-- The ring-sheaf map rho, obtained by the sheafification universal property. -/
noncomputable def finiteCoefficientDirectImageMap :
    finiteCoefficientRingSheaf V Λ ⟶
      (Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
        (finiteCoefficientRingSheaf U Λ) :=
  ((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientDirectImagePresheafMap f Λ)

/-- The canonical map c_f is the ring-sheaf adjunct of rho. -/
noncomputable def finiteCoefficientInverseImageMap :
    (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).obj
      (finiteCoefficientRingSheaf V Λ) ⟶ finiteCoefficientRingSheaf U Λ :=
  ((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientDirectImageMap f Λ)

/-- The canonical comparison from constant-presheaf sheafification preserves constants. -/
noncomputable def finiteCoefficientConstantComparison (T : Scheme.{u}) :
    (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of Λ) ⟶
      finiteCoefficientRingSheaf T Λ :=
  ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _).symm
    (finiteCoefficientScalarMap T Λ)

/-- Constant sections give the unique constant-sheaf identification. -/
theorem finiteCoefficientConstantComparison_isIso (T : Scheme.{u}) :
    IsIso (finiteCoefficientConstantComparison Λ T) ∧
      ∀ e : (constantSheaf (Scheme.ProEt.topology T) RingCat.{u + 1}).obj (RingCat.of Λ) ⟶
          finiteCoefficientRingSheaf T Λ,
        toSheafify (Scheme.ProEt.topology T)
            ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ)) ≫ e.hom =
          finiteCoefficientScalarMap T Λ → e = finiteCoefficientConstantComparison Λ T := by
  have hunit : toSheafify (Scheme.ProEt.topology T)
      ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ)) ≫
        (finiteCoefficientConstantComparison Λ T).hom = finiteCoefficientScalarMap T Λ := by
    exact Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _)
      (finiteCoefficientScalarMap T Λ)
  constructor
  · apply (Sheaf.isLocallyBijective_iff_isIso _).mp
    constructor
    · change Presheaf.IsLocallyInjective _ (finiteCoefficientConstantComparison Λ T).hom
      rw [← Presheaf.comp_isLocallyInjective_iff _
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ))), hunit]
      infer_instance
    · change Presheaf.IsLocallySurjective _ (finiteCoefficientConstantComparison Λ T).hom
      rw [← Presheaf.comp_isLocallySurjective_iff _
        (toSheafify (Scheme.ProEt.topology T)
          ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ))), hunit]
      infer_instance
  · intro e he
    apply Sheaf.hom_ext
    exact sheafify_hom_ext _ _ _ (finiteCoefficientRingSheaf T Λ).property (he.trans hunit.symm)

private theorem finiteCoefficientComparison_unit (T : Scheme.{u}) :
    toSheafify (Scheme.ProEt.topology T)
        ((Functor.const T.ProEtᵒᵖ).obj (RingCat.of Λ)) ≫
      (finiteCoefficientConstantComparison Λ T).hom = finiteCoefficientScalarMap T Λ :=
  Equiv.apply_symm_apply
    ((sheafificationAdjunction (Scheme.ProEt.topology T) RingCat.{u + 1}).homEquiv _ _)
    (finiteCoefficientScalarMap T Λ)

private theorem finiteCoefficientInverseImageMap_square :
    (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).map
        (finiteCoefficientConstantComparison Λ V) ≫ finiteCoefficientInverseImageMap f Λ =
      Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} (RingCat.of Λ) ≫
        finiteCoefficientConstantComparison Λ U := by
  let adj := Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}
  change _ ≫ (adj.homEquiv _ _).symm _ = (adj.homEquiv _ _).symm _ ≫ _
  rw [← adj.homEquiv_naturality_left_symm, ← adj.homEquiv_naturality_right_symm]
  congr 1
  apply Sheaf.hom_ext
  apply sheafify_hom_ext _ _ _
    (((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
      (finiteCoefficientRingSheaf U Λ)).property)
  have hd : toSheafify (Scheme.ProEt.topology V) (finiteCoefficientPresheaf V Λ) ≫
      (finiteCoefficientDirectImageMap f Λ).hom = finiteCoefficientDirectImagePresheafMap f Λ :=
    Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv
        (finiteCoefficientPresheaf V Λ)
        ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          (finiteCoefficientRingSheaf U Λ))) _
  have hr : toSheafify (Scheme.ProEt.topology V)
      ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of Λ)) ≫
      (Scheme.proEtaleConstantDirectImageMap f RingCat.{u + 1} (RingCat.of Λ)).hom =
      Functor.whiskerLeft (Scheme.proEtaleBaseChange f).op
        (toSheafify (Scheme.ProEt.topology U)
          ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of Λ))) :=
    Equiv.apply_symm_apply
      ((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv
        ((Functor.const V.ProEtᵒᵖ).obj (RingCat.of Λ))
        ((Scheme.proEtaleSheafDirectImage f RingCat.{u + 1}).obj
          ((constantSheaf (Scheme.ProEt.topology U) RingCat.{u + 1}).obj
            (RingCat.of Λ)))) _
  change toSheafify _ _ ≫ ((finiteCoefficientConstantComparison Λ V).hom ≫
      (finiteCoefficientDirectImageMap f Λ).hom) =
    toSheafify _ _ ≫ ((Scheme.proEtaleConstantDirectImageMap f RingCat.{u + 1}
      (RingCat.of Λ)).hom ≫ _)
  rw [← Category.assoc, finiteCoefficientComparison_unit, ← Category.assoc, hr]
  change (finiteCoefficientConstants V Λ ≫ toSheafify _ _) ≫
    (finiteCoefficientDirectImageMap f Λ).hom = _
  rw [Category.assoc, hd]
  apply NatTrans.ext
  funext W
  change (finiteCoefficientConstants V Λ).app W ≫
      finiteCoefficientDirectImageApp f Λ W =
    (toSheafify (Scheme.ProEt.topology U)
      ((Functor.const U.ProEtᵒᵖ).obj (RingCat.of Λ))).app _ ≫
        (finiteCoefficientConstantComparison Λ U).hom.app _
  rw [← NatTrans.comp_app, finiteCoefficientComparison_unit]
  ext a
  rfl

private theorem constantInverseImageMap_isIso (A : RingCat.{u + 1}) :
    IsIso (Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} A) := by
  let T := ⊤_ V.ProEt
  let hT := terminalIsTerminal (C := V.ProEt)
  let hGT := hT.isTerminalObj (Scheme.proEtaleBaseChange f)
  let adjV := constantSheafAdj (Scheme.ProEt.topology V) RingCat.{u + 1} hT
  let adjU := constantSheafAdj (Scheme.ProEt.topology U) RingCat.{u + 1} hGT
  let adj := (adjV.comp (Scheme.proEtaleSheafAdjunction f RingCat.{u + 1})).ofNatIsoRight
    ((Scheme.proEtaleBaseChange f).sheafPushforwardContinuousCompSheafSectionsObjIso
      RingCat.{u + 1} (Scheme.ProEt.topology V) (Scheme.ProEt.topology U) (op T))
  have he : Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} A =
      (adj.leftAdjointUniq adjU).hom.app A := by
    apply (adj.homEquiv _ _).injective
    rw [Adjunction.homEquiv_leftAdjointUniq_hom_app]
    rw [Adjunction.homEquiv_ofNatIsoRight_apply]
    change (adjV.comp (Scheme.proEtaleSheafAdjunction f RingCat.{u + 1})).homEquiv _ _
      (Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} A) ≫ 𝟙 _ = _
    rw [Category.comp_id, Adjunction.comp_homEquiv]
    change adjV.homEquiv _ _
      ((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _
        (((Scheme.proEtaleSheafAdjunction f RingCat.{u + 1}).homEquiv _ _).symm
          (Scheme.proEtaleConstantDirectImageMap f RingCat.{u + 1} A))) = _
    rw [Equiv.apply_symm_apply]
    change ((constantPresheafAdj RingCat.{u + 1} hT).comp
      (sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1})).homEquiv _ _
        (Scheme.proEtaleConstantDirectImageMap f RingCat.{u + 1} A) = _
    rw [Adjunction.comp_homEquiv]
    change (constantPresheafAdj RingCat.{u + 1} hT).homEquiv _ _
      ((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv _ _
        (((sheafificationAdjunction (Scheme.ProEt.topology V) RingCat.{u + 1}).homEquiv
          _ _).symm _)) = _
    rw [Equiv.apply_symm_apply]
    change 𝟙 A ≫ _ = _
    rw [Category.id_comp]
    rfl
  rw [he]
  infer_instance

/-- The canonical coefficient inverse-image map is an isomorphism, for finite rings
without a commutativity hypothesis and for arbitrary scheme morphisms. -/
theorem finiteCoefficientInverseImageMap_isIso :
    IsIso (finiteCoefficientInverseImageMap f Λ) := by
  have := (finiteCoefficientConstantComparison_isIso Λ V).1
  have := (finiteCoefficientConstantComparison_isIso Λ U).1
  have := constantInverseImageMap_isIso f (RingCat.of Λ)
  have hs := finiteCoefficientInverseImageMap_square f Λ
  have : IsIso ((Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).map
      (finiteCoefficientConstantComparison Λ V) ≫ finiteCoefficientInverseImageMap f Λ) := by
    rw [hs]
    infer_instance
  exact IsIso.of_isIso_comp_left
    ((Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).map
      (finiteCoefficientConstantComparison Λ V)) (finiteCoefficientInverseImageMap f Λ)

end ProEtale

namespace ProEtale

/-- For commutative coefficients the constant-preserving identifications carry c_f
exactly to the structure map of the recorded pro-etale inverse-image construction.
The equality is written as a commuting square, avoiding any arbitrary choice of inverse. -/
theorem finiteCoefficientInverseImageMap_constant
    {U V : Scheme.{u}} (f : U ⟶ V) (Λ : Type (u + 1))
    [CommRing Λ] [Finite Λ] [TopologicalSpace Λ] [DiscreteTopology Λ] :
    (Scheme.proEtaleSheafInverseImage f RingCat.{u + 1}).map
        (finiteCoefficientConstantComparison Λ V) ≫ finiteCoefficientInverseImageMap f Λ =
      Scheme.proEtaleConstantInverseImageMap f RingCat.{u + 1} (RingCat.of Λ) ≫
        finiteCoefficientConstantComparison Λ U := by
  exact finiteCoefficientInverseImageMap_square f Λ

end ProEtale

end AlgebraicGeometry

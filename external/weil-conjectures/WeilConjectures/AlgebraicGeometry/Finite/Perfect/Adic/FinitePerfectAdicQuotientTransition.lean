/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Finite.Perfect.Adic.FinitePerfectAdicMarkedOrigin
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsTransition

/-! # The ordinary quotient arrows in fixed-scalar chart coordinates

Source: Stacks Project, Tags 03CY and 09C6.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option synthInstance.maxSize 2048
universe t
open CategoryTheory CategoryTheory.Limits Opposite
namespace AlgebraicGeometry.Scheme
attribute [local instance] finitePerfectAdicAlgebraDerived
attribute [local instance] finitePerfectModelsAbLocallyBijective

/-- Ordinary fixed-scalar coordinates of the finite quotient on the chart: ordinary scalar
extension to the finite quotient ring, followed by the fixed coefficient encoding and
restriction to the chart. Its termwise application to a K-flat complex computes
`finitePerfectAdicQuotientCoordinates`.
Source: Stacks Tags 03CY, 099R and 06YY. -/
def finitePerfectAdicQuotientStrictCoordinates
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ) :
    CompletedAdicModules X d ⥤ Sheaf (ProEt.topology V.left)
      (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) :=
  completedAdicChange X (completedAdicCommProjection X d n) ⋙
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
      (completedAdicFiniteCommRing X d n) (φ n) V

instance finitePerfectAdicQuotientStrictCoordinates_additive
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ) :
    (finitePerfectAdicQuotientStrictCoordinates X d φ V n).Additive :=
  inferInstanceAs (completedAdicChange X (completedAdicCommProjection X d n) ⋙
    finiteCoefficientSliceRestriction X (A ⧸ d.ideal ^ (n + 1))
      (completedAdicFiniteCommRing X d n) (φ n) V).Additive

/-- Restriction of scalars along the consecutive finite quotient map, on chart sheaves. -/
abbrev finitePerfectAdicStepRestrict (X : Scheme.{t}) {A : Type t} [CommRing A]
    (d : AdicCoefficientDatum A) (V : X.Etale) (n : ℕ) :
    Sheaf (ProEt.topology V.left) (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1)))) ⥤
      Sheaf (ProEt.topology V.left)
        (ModuleCat.{t + 1} (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))) :=
  sheafCompose (ProEt.topology V.left) (ModuleCat.restrictScalars.{t + 1, t + 1, t + 1}
    (RingHom.ulift.{t + 1, t + 1} (Ideal.Quotient.factorPowSucc d.ideal (n + 1))))



/-- A consecutive arrow of fixed-scalar coordinates is the ordinary quotient arrow: on every
chart object it sends the sheafified pure tensor `b ⊗ x` to `q(b) ⊗ x`. Since sheafified pure
tensors generate, this determines the arrow uniquely.
Source: Stacks Project, Tag 09C6. -/
def FinitePerfectAdicQuotientTransition
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (V : X.Etale) (n : ℕ)
    (δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n) : Prop :=
  ∀ (N : CompletedAdicModules X d) (U : V.left.ProEt)
    (b : (completedAdicFiniteCommRing X d (n + 1)).obj.obj
      (op (finitePerfectAdicChartObject V U)))
    (x : N.val.obj (op (finitePerfectAdicChartObject V U))),
    (δ.app N).hom.app (op U)
        (completedAdicChangeTensor X (completedAdicCommProjection X d (n + 1)) N
          (op (finitePerfectAdicChartObject V U)) b x) =
      completedAdicChangeTensor X (completedAdicCommProjection X d n) N
        (op (finitePerfectAdicChartObject V U))
        ((completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app
          (op (finitePerfectAdicChartObject V U)) b) x

/-- The semilinear quotient arrow `b ⊗ x ↦ q(b) ⊗ x` between consecutive ordinary scalar
extensions along the finite projections. -/
def completedAdicChangeQuotientTransition
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ) :
    completedAdicChange X (completedAdicCommProjection X d (n + 1)) ⟶
      completedAdicChange X (completedAdicCommProjection X d n) ⋙
        SheafOfModules.restrictScalars ((sheafCompose (ProEt.topology X)
          (forget₂ CommRingCat.{t + 1} RingCat.{t + 1})).map
            (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n))) :=
  SheafOfModules.changeOfRingsTransitionOfEq _ _ _
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))
    (completedAdicChangeData X (completedAdicCommProjection X d (n + 1))).choose_spec.choose
    (completedAdicChangeData X
      (completedAdicCommProjection X d (n + 1))).choose_spec.choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose_spec.choose

/-- The quotient transition sends the sheafified pure tensor `b ⊗ x` to `q(b) ⊗ x`. -/
theorem completedAdicChangeQuotientTransition_tensor
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (N : CompletedAdicModules X d) (W : X.ProEtᵒᵖ)
    (b : (completedAdicFiniteCommRing X d (n + 1)).obj.obj W) (x : N.val.obj W) :
    ((completedAdicChangeQuotientTransition X d n).app N).val.app W
        (completedAdicChangeTensor X (completedAdicCommProjection X d (n + 1)) N W b x) =
      completedAdicChangeTensor X (completedAdicCommProjection X d n) N W
        ((completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app W b) x :=
  SheafOfModules.changeOfRingsTransitionOfEq_tmul _ _ _
    (completedAdicCommProjection_comp X d (n + 1) n (Nat.le_succ n))
    (completedAdicChangeData X (completedAdicCommProjection X d (n + 1))).choose_spec.choose
    (completedAdicChangeData X
      (completedAdicCommProjection X d (n + 1))).choose_spec.choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose
    (completedAdicChangeData X (completedAdicCommProjection X d n)).choose_spec.choose_spec.choose
    N W b x

/-- The quotient transition is semilinear over the quotient map. -/
theorem completedAdicChangeQuotientTransition_smul
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A) (n : ℕ)
    (N : CompletedAdicModules X d) (W : X.ProEtᵒᵖ)
    (s : (completedAdicFiniteCommRing X d (n + 1)).obj.obj W)
    (x : ((completedAdicChange X (completedAdicCommProjection X d (n + 1))).obj N).val.obj W) :
    ((completedAdicChangeQuotientTransition X d n).app N).val.app W (s • x) =
      (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app W s •
        (show ((completedAdicChange X (completedAdicCommProjection X d n)).obj N).val.obj W from
          ((completedAdicChangeQuotientTransition X d n).app N).val.app W x) :=
  (((completedAdicChangeQuotientTransition X d n).app N).val.app W).hom.map_smul s x

/-- The finite comparisons intertwine the constant and the actual quotient maps on constant
sections. -/
theorem finitePerfectAdic_quotientCommMap_scalar
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (n : ℕ) (W : X.ProEtᵒᵖ)
    (c : ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1))) :
    (completedAdicQuotientCommMap X d (n + 1) n (Nat.le_succ n)).hom.app W
        ((φ (n + 1)).hom.app W ((proEtaleModuleScalarUnit X _).app W c)) =
      (φ n).hom.app W ((proEtaleModuleScalarUnit X _).app W
        (ULift.up (Ideal.Quotient.factorPowSucc d.ideal (n + 1) c.down))) := by
  have h := ConcreteCategory.congr_hom (NatTrans.congr_app
    (congrArg (fun f ↦ f.hom) (hcompat.1 n)) W) ((proEtaleModuleScalarUnit X _).app W c)
  refine h.symm.trans ?_
  change (φ n).hom.app W ((adicConstantMap X _).hom.app W
    ((proEtaleModuleScalarUnit X _).app W c)) = _
  congr 1
  let q : CommRingCat.of (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 2))) ⟶
      CommRingCat.of (ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1))) :=
    CommRingCat.ofHom (RingHom.ulift (adicQuotientMap d.ideal (n + 2) (n + 1) (Nat.le_succ _)))
  have hn := congrArg (fun f ↦ f.app W c)
    (toSheafify_naturality (ProEt.topology X) ((Functor.const X.ProEtᵒᵖ).map q))
  exact hn.symm

/-- The consecutive arrow of fixed-scalar coordinates induced by
`completedAdicChangeQuotientTransition`. -/
def finitePerfectAdicQuotientStrictTransition
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (V : X.Etale) (n : ℕ) :
    finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
      finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
        finitePerfectAdicStepRestrict X d V n where
  app N := ⟨
    { app := fun U ↦ ModuleCat.ofHom (R := ULift.{t + 1} (A ⧸ d.ideal ^ (n + 1 + 1)))
        (X := ((finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1)).obj N).obj.obj U)
        (Y := ((finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
          finitePerfectAdicStepRestrict X d V n).obj N).obj.obj U)
        { toFun := fun x ↦ ((completedAdicChangeQuotientTransition X d n).app N).val.app
            (op (finitePerfectAdicChartObject V U.unop)) x
          map_add' := fun x y ↦ map_add _ x y
          map_smul' := fun c x ↦ by
            change ((completedAdicChangeQuotientTransition X d n).app N).val.app
                (op (finitePerfectAdicChartObject V U.unop))
                ((φ (n + 1)).hom.app (op (finitePerfectAdicChartObject V U.unop))
                  ((proEtaleModuleScalarUnit X _).app _ c) •
                  (show ((completedAdicChange X (completedAdicCommProjection X d (n + 1))).obj
                    N).val.obj (op (finitePerfectAdicChartObject V U.unop)) from x)) =
              (φ n).hom.app (op (finitePerfectAdicChartObject V U.unop))
                ((proEtaleModuleScalarUnit X _).app _
                  (ULift.up (Ideal.Quotient.factorPowSucc d.ideal (n + 1) c.down))) •
                (show ((completedAdicChange X (completedAdicCommProjection X d n)).obj N).val.obj
                    (op (finitePerfectAdicChartObject V U.unop)) from
                  ((completedAdicChangeQuotientTransition X d n).app N).val.app
                    (op (finitePerfectAdicChartObject V U.unop)) x)
            rw [completedAdicChangeQuotientTransition_smul,
              finitePerfectAdic_quotientCommMap_scalar X d φ hcompat] }
      naturality := fun _ _ f ↦ by
        ext x
        exact PresheafOfModules.naturality_apply
          ((completedAdicChangeQuotientTransition X d n).app N).val
          ((MorphismProperty.Over.map ⊤ (show WeaklyEtale V.hom from inferInstance)).op.map f)
          x }⟩
  naturality N N' a := by
    have hn := (completedAdicChangeQuotientTransition X d n).naturality a
    apply Sheaf.hom_ext
    apply NatTrans.ext
    funext U
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    exact (congrArg (fun f ↦ f.val.app (op (finitePerfectAdicChartObject V U.unop)) x) hn)

/-- The ordinary quotient arrows exist between the fixed-scalar coordinates. This uses the
compatibility of the finite comparisons `φ` with the quotient maps.
Source: Stacks Project, Tags 03CY and 09C6.

Proof sketch: the unit of ordinary scalar extension along the finite projection, composed with
the identification of restriction along the composite projection, transposes to an arrow of
ordinary scalar extensions; since `φ` intertwines the constant and the actual quotient maps,
its fixed-scalar encoding is semilinear over the constant quotient map. -/
theorem finitePerfectAdic_quotient_transition_exists
    (X : Scheme.{t}) {A : Type t} [CommRing A] (d : AdicCoefficientDatum A)
    (φ : ∀ n : ℕ, adicConstantRing X (A ⧸ d.ideal ^ (n + 1)) ⟶
      completedAdicFiniteCommRing X d n)
    (hcompat : FinitePerfectModelsCompatible X d φ) (V : X.Etale) (n : ℕ) :
    ∃ δ : finitePerfectAdicQuotientStrictCoordinates X d φ V (n + 1) ⟶
        finitePerfectAdicQuotientStrictCoordinates X d φ V n ⋙
          finitePerfectAdicStepRestrict X d V n,
      FinitePerfectAdicQuotientTransition X d φ V n δ :=
  ⟨finitePerfectAdicQuotientStrictTransition X d φ hcompat V n, fun N _ b x ↦
    completedAdicChangeQuotientTransition_tensor X d n N _ b x⟩

end AlgebraicGeometry.Scheme

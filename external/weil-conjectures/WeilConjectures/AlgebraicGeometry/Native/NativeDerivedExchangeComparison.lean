/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Native.NativeDerivedBaseChange
public import WeilConjectures.AlgebraicGeometry.Native.NativeModuleConstructibilityComparison
public import WeilConjectures.AlgebraicGeometry.NativeEncoding.NativeAdicEncodingCore
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructible
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionFinite
public import WeilConjectures.NumberTheory.Padics.CoefficientExtensionSupplement
public import Mathlib.RingTheory.Ideal.Quotient.Index
public import WeilConjectures.Topology.ProfiniteCondensedRing
public import WeilConjectures.CategoryTheory.RingObjects.Condensed.EllAdic
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Basic
public import WeilConjectures.CategoryTheory.Right.RightDerivedFunctorOfQuasiIsoResolutions
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.CategoryTheory.SheafTensor
public import WeilConjectures.CategoryTheory.SheafTensorStructure
public import Mathlib.CategoryTheory.Sites.Monoidal
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.Basic
public import Mathlib.CategoryTheory.Monoidal.Preadditive
public import WeilConjectures.CategoryTheory.PresheafTensorInternalHom
public import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Preadditive
public import Mathlib.CategoryTheory.Comma.StructuredArrow.Small
public import Mathlib.CategoryTheory.Sites.Localization
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Sheafification
public import Mathlib.CategoryTheory.Adjunction.Limits
public import Mathlib.CategoryTheory.Monoidal.Braided.Reflection
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import Mathlib.CategoryTheory.ObjectProperty.Kernels
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.UpperLowerStar
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Hom
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Bounded.BoundedConstructibleBaseChange
public import Mathlib.CategoryTheory.Adjunction.Mates
public import WeilConjectures.Algebra.Homology.RingedTensorCorner.ProjectionMateExact
public import WeilConjectures.AlgebraicGeometry.ModuleObjectProjectionMap
public import WeilConjectures.AlgebraicGeometry.ProEtaleCoefficients.PadicIntegersInvertEll
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Colimit.Compatibility
public import WeilConjectures.CategoryTheory.ModuleObjects.EllAdicRationalization
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.SixFunctors.ChangeOfCoefficients
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalPushforward
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRationalExchange
import WeilConjectures.AlgebraicGeometry.Native.NativeScalarForgetting
import WeilConjectures.AlgebraicGeometry.Exact.ExactCondensedExchangeComparison
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.BoundedConstructiblePullback
import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.EllAdic.EllAdicBoundedTriangulated
import WeilConjectures.CategoryTheory.Adjunction.Derived.DerivedForgetMate
import WeilConjectures.CategoryTheory.Derived.DerivedExactCube
import WeilConjectures.CategoryTheory.ProperBaseChange.ExchangeMateCube
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Proper.ProperBaseChangeRational

/-! # Comparison of native exchange with the restricted condensed exchange

## References

* Stacks 03EK
* Stacks 09T5 and 070Y
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option Elab.async false
universe u v₁ v₂ w₁ w₂
open CategoryTheory CategoryTheory.Limits MonoidalCategory MonObj
open scoped CategoryTheory.Obj
namespace AlgebraicGeometry.ProEtale

/-- Scalar forgetting followed by the normalized ring-realization transport, before
section-ring presentation. The chosen isomorphisms form a single family normalized on
every finite-extension chart and natural in scheme maps. -/
def nativeExchangeEncoding (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :=
  AdicSheaf.forgetAb l X ⋙ Mod.comap (nativeModuleCoefficientIso l X).hom

/-- Scalar forgetting and transport are equivalences. -/
@[instance] theorem nativeExchangeEncoding_isEquivalence (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeExchangeEncoding l X).IsEquivalence := by
  have : (AdicSheaf.forgetAb l X).IsEquivalence :=
    nativeScalarForgetting_isEquivalence l X
  have : (Mod.comap (nativeModuleCoefficientIso l X).hom).IsEquivalence :=
    (Mod.comapEquivalenceOfIsIso (nativeModuleCoefficientIso l X).hom).isEquivalence_functor
  dsimp only [nativeExchangeEncoding]
  infer_instance

/-- Scalar transport leaves addition of underlying maps unchanged. -/
@[instance] theorem nativeExchangeEncoding_additive (l : ℕ) [Fact l.Prime] (X : Scheme.{u}) :
    (nativeExchangeEncoding l X).Additive := by
  refine ⟨?_⟩
  intro M N f g
  rfl

attribute [irreducible] nativeExchangeEncoding

/-- The same real encoding, transported along a specified equality of bundled
coefficient rings. Equality fixes the multiplication as well as the underlying sheaf. -/
def nativeExchangeEncodingAt (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    AdicSheaf l X ⥤ Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X) :=
  hΛ.symm ▸ nativeExchangeEncoding l X

/-- Equality transport preserves the encoding equivalence. -/
@[instance] theorem nativeExchangeEncodingAt_isEquivalence (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    (nativeExchangeEncodingAt l Λ hΛ X).IsEquivalence := by
  subst Λ
  change (nativeExchangeEncoding l X).IsEquivalence
  infer_instance

/-- Equality transport preserves additivity. -/
@[instance] theorem nativeExchangeEncodingAt_additive (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l)) (X : Scheme.{u}) :
    (nativeExchangeEncodingAt l Λ hΛ X).Additive := by
  subst Λ
  change (nativeExchangeEncoding l X).Additive
  infer_instance

attribute [irreducible] nativeExchangeEncodingAt

/-- The underlying arrow of a morphism in a full subcategory. -/
def nativeUnderlyingExchangeArrow {C : Type*} [Category C] (P : ObjectProperty C)
    {A B : P.FullSubcategory} (f : A ⟶ B) : Arrow C :=
  Arrow.mk (P.ι.map f)

/-- The inclusion of a full subcategory preserves invertibility. -/
theorem nativeUnderlyingExchangeArrow_isIso {C : Type*} [Category C] (P : ObjectProperty C)
    {A B : P.FullSubcategory} (f : A ⟶ B) (hf : IsIso f) :
    IsIso (nativeUnderlyingExchangeArrow P f).hom := by
  let := hf
  change IsIso (P.ι.map f)
  infer_instance

attribute [irreducible] nativeUnderlyingExchangeArrow

private theorem finiteComparison_eq_chart (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField l) :
    (CondensedQbarCoefficientRealization.fieldDiagramIso l T).hom.app E =
      chartComparison T E := by
  unfold CondensedQbarCoefficientRealization.fieldDiagramIso
  change (CondensedQbarCoefficientRealization.finiteFieldComparisonIso E l T).hom.hom = _
  let adj := pointUpperStarLowerStarAdjunction.comp
    (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))
  apply (adj.homEquiv _ _).injective
  change adj.homEquiv _ _ _ = adj.homEquiv _ _ ((adj.homEquiv _ _).symm _)
  rw [Equiv.apply_symm_apply]
  ext S f
  exact CondensedQbarCoefficientRealization.finiteFieldComparison_test E l T S.unop f.down

private lemma finiteLeg_native (ℓ : ℕ) [Fact ℓ.Prime]
    (T : Scheme.{u}) (E : PadicAlgCl.FiniteIntermediateField ℓ)
    (V : T.ProEtᵒᵖ)
    (s : ((sheafCompose (Scheme.ProEt.topology T)
      (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj
        (continuousMapRingSheaf T E)).obj.obj V) (x : V.unop.left) :
    (((((padicAlgClSheafCocone T ℓ).ι.app E ≫
      padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) =
        (s.down x : PadicAlgCl ℓ) := by
  let J := Scheme.ProEt.topology T
  let R := padicSubfieldSheaf T ℓ E.1
  let RAb := (sheafCompose J (forget₂ RingCat.{u + 1} Ab.{u + 1})).obj R
  have hu : (Sheaf.sheafifyRingPresheafIso J R).inv.hom = toSheafify J RAb.obj := by
    change (sheafToPresheaf J Ab.{u + 1}).map
      (inv ((sheafificationAdjunction J Ab.{u + 1}).counit.app RAb)) = _
    rw [Functor.map_inv]
    exact (sheafificationAdjunction J Ab.{u + 1}).inv_counit_map
  have hf : toSheafify J (padicAlgClRingPresheaf T ℓ ⋙ forget₂ RingCat Ab) ≫
      (padicAlgClSheafToAdicConstantSheaf T ℓ).hom =
        padicAlgClPresheafToAdicConstantSheaf T ℓ := by
    exact ((sheafificationAdjunction J Ab.{u + 1}).homEquiv _ _).apply_symm_apply _
  change (((((padicSubfieldSheafToPadicAlgClSheaf T ℓ E.1) ≫
    padicAlgClSheafToAdicConstantSheaf T ℓ).hom.app V) s).down.1 x) = _
  unfold padicSubfieldSheafToPadicAlgClSheaf continuousMapRingSheafToPadicAlgClSheaf
    Sheaf.sheafComposeToSheafify
  change ((((((Sheaf.sheafifyRingPresheafIso J R).inv.hom ≫ _) ≫
    (padicAlgClSheafToAdicConstantSheaf T ℓ).hom).app V) s).down.1 x) = _
  rw [hu, Category.assoc, ← toSheafify_naturality_assoc, hf]
  rfl

private theorem coefficientIso_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    nativeModuleCoefficientIso l T = NativeEncoding.coefficientIso l T := by
  apply Iso.ext
  have : PreservesColimitsOfSize.{0, 0} (upperStarFromPoint T) :=
    (pointUpperStarLowerStarAdjunction.comp
      (upperStarLowerStarAdjunction Ab.{u + 1} (toSpecZ T))).leftAdjoint_preservesColimits
  apply (isColimitOfPreserves (upperStarFromPoint T)
    (Profinite.isColimitPadicAlgClRingObjCocone l)).hom_ext
  intro E
  change (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
    (nativeModuleCoefficientIso l T).hom =
      (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
        (NativeEncoding.coefficientIso l T).hom
  have hfac :
      (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
        (NativeEncoding.coefficientIso l T).hom = chartComparison T E ≫
          (padicAlgClSheafCocone T l).ι.app E ≫
            padicAlgClSheafToAdicConstantSheaf T l := by
    change (upperStarFromPoint T).map (Profinite.padicSubfieldRingObjToPadicAlgCl l E) ≫
      ((CondensedQbarCoefficientRealization.globalCoefficientIso l T).hom.hom ≫
        padicAlgClSheafToAdicConstantSheaf T l) = _
    rw [← Category.assoc,
      CondensedQbarCoefficientRealization.globalCoefficientIso_fac,
      finiteComparison_eq_chart, Category.assoc]
  rw [hfac]
  ext V s
  apply ULift.ext
  apply Subtype.ext
  apply ContinuousMap.ext
  intro x
  rw [(locallyFiniteCoefficientRing_realization l).choose_spec.2.1 T E V s x]
  exact (finiteLeg_native l T E V ((chartComparison T E).hom.app V s) x).symm

/-- The chosen native coefficient isomorphism is the normalized coefficient isomorphism of the
native encoding. -/
theorem nativeModuleCoefficientIso_eq_nativeEncodingCoefficientIso (l : ℕ) [Fact l.Prime]
    (T : Scheme.{u}) :
    nativeModuleCoefficientIso l T = NativeEncoding.coefficientIso l T :=
  coefficientIso_eq l T

private theorem encoding_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    nativeExchangeEncoding l T = NativeEncoding.encoding l T := by
  unfold nativeExchangeEncoding NativeEncoding.encoding
  simp only [coefficientIso_eq]

attribute [local irreducible] upperStarFromPoint Mod.monoidalClosed
  Mod.monoidalCategoryStruct DerivedCategory HasDerivedCategory.standard
  Functor.rightDerivedFunctor Functor.mapDerivedCategory
  Functor.leftDerivedFunctor Mod.monoidalCategory
  Functor.mapDerivedCategoryNatIso

private theorem ordinary_mate (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv (adicUpperStarLowerStarAdjunction l f)
      (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
      (TwoSquare.mk _ _ _ _ (NativeEncoding.pullComparison l f).inv)) =
        (NativeEncoding.pushComparison l f).hom := by
  exact (Classical.choose_spec
    (Classical.choose_spec (NativeEncoding.encoding_ordinary_operations l f)).2).1

attribute [local irreducible] NativeEncoding.encoding NativeEncoding.pullComparison
  NativeEncoding.pushComparison adicUpperStar adicLowerStar
  CondensedRing.upperStar CondensedRing.lowerStar

private theorem derived_mate (l : ℕ) [Fact l.Prime]
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    (mateEquiv
      (adicUpperStarLowerStarAdjunction l f).mapDerivedCategoryRightDerivedAdjunction
      (CondensedRing.upperStarLowerStarAdjunction
        (Profinite.padicAlgClRingObj l) f).mapDerivedCategoryRightDerivedAdjunction
      (TwoSquare.mk _ _ _ _
        (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l f)).inv)) =
        (NativeEncoding.derivedPushComparison l f).hom := by
  exact Adjunction.derived_exact_forget_mate
    (adicUpperStarLowerStarAdjunction l f)
    (CondensedRing.upperStarLowerStarAdjunction (Profinite.padicAlgClRingObj l) f)
    (NativeEncoding.encoding l Y) (NativeEncoding.encoding l X)
    (NativeEncoding.pullComparison l f) (NativeEncoding.pushComparison l f)
    (ordinary_mate l f)

section LocalizeInverseCube
variable {C : Type*} {D : Type*} {E : Type*} {F : Type*}
variable {G : Type*} {H : Type*} {I : Type*} {J : Type*}
  [Category C] [Abelian C] [HasDerivedCategory C]
  [Category D] [Abelian D] [HasDerivedCategory D]
  [Category E] [Abelian E] [HasDerivedCategory E]
  [Category F] [Abelian F] [HasDerivedCategory F]
  [Category G] [Abelian G] [HasDerivedCategory G]
  [Category H] [Abelian H] [HasDerivedCategory H]
  [Category I] [Abelian I] [HasDerivedCategory I]
  [Category J] [Abelian J] [HasDerivedCategory J]
  (a : C ⥤ D)
  (b : D ⥤ E)
  (c : E ⥤ F)
  (d : C ⥤ G)
  (e : G ⥤ E)
  (f : G ⥤ H)
  (g : H ⥤ F)
  (h : C ⥤ I)
  (i : I ⥤ H)
  (j : D ⥤ J)
  (k : J ⥤ F)
  (m : I ⥤ J)
  [a.Additive] [PreservesFiniteLimits a] [PreservesFiniteColimits a]
  [b.Additive] [PreservesFiniteLimits b] [PreservesFiniteColimits b]
  [c.Additive] [PreservesFiniteLimits c] [PreservesFiniteColimits c]
  [d.Additive] [PreservesFiniteLimits d] [PreservesFiniteColimits d]
  [e.Additive] [PreservesFiniteLimits e] [PreservesFiniteColimits e]
  [f.Additive] [PreservesFiniteLimits f] [PreservesFiniteColimits f]
  [g.Additive] [PreservesFiniteLimits g] [PreservesFiniteColimits g]
  [h.Additive] [PreservesFiniteLimits h] [PreservesFiniteColimits h]
  [i.Additive] [PreservesFiniteLimits i] [PreservesFiniteColimits i]
  [j.Additive] [PreservesFiniteLimits j] [PreservesFiniteColimits j]
  [k.Additive] [PreservesFiniteLimits k] [PreservesFiniteColimits k]
  [m.Additive] [PreservesFiniteLimits m] [PreservesFiniteColimits m]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

private theorem localize_inverse_cube
    (q1 : d ⋙ e ≅ a ⋙ b)
    (q2 : f ⋙ g ≅ e ⋙ c)
    (q3 : d ⋙ f ≅ h ⋙ i)
    (q4 : b ⋙ c ≅ j ⋙ k)
    (q5 : h ⋙ m ≅ a ⋙ j)
    (q6 : i ⋙ g ≅ m ⋙ k)
    (comm : ∀ X : C,
      c.map (q1.inv.app X) ≫ q2.inv.app (d.obj X) ≫ g.map (q3.hom.app X) =
        q4.hom.app (a.obj X) ≫ k.map (q5.inv.app X) ≫ q6.inv.app (h.obj X))
    (M : DerivedCategory C) :
    c.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q1).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso q2).inv.app (d.mapDerivedCategory.obj M) ≫
      g.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q3).hom.app M) =
    (Functor.mapDerivedCategorySquareIso q4).hom.app (a.mapDerivedCategory.obj M) ≫
      k.mapDerivedCategory.map ((Functor.mapDerivedCategorySquareIso q5).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso q6).inv.app (h.mapDerivedCategory.obj M) := by
  have hc := Functor.mapDerivedCategory_exactCube a b c d e f g h i j k m
    q1.symm q2.symm q3 q4 q5.symm q6.symm comm
  simpa only [Functor.mapDerivedCategorySquareIso, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Functor.mapDerivedCategoryNatIso_symm, Category.assoc]
      using congr_app hc M
end LocalizeInverseCube

private theorem nativeDerivedSquare_hom (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (AdicSheaf l Y)) :
    (adicDerivedPullSquare l sq).hom.app M =
      (Functor.mapDerivedCategorySquareIso (adicUpperStarCompIso l sq.w.symm)).hom.app M := by
  rfl

attribute [local irreducible] adicDerivedPullSquare adicDerivedBaseChange

private theorem localized_cube (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (AdicSheaf l Y)) :
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p').mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l g)).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l p')).inv.app
        ((adicUpperStar l g).mapDerivedCategory.obj M) ≫
      (NativeEncoding.derivedEncoding l X').map ((adicDerivedPullSquare l sq).hom.app M) =
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.condensedPullbackSquare l sq)).hom.app
        ((NativeEncoding.derivedEncoding l Y).obj M) ≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v).mapDerivedCategory.map
        ((Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l p)).inv.app M) ≫
      (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l v)).inv.app
        ((adicUpperStar l p).mapDerivedCategory.obj M) := by
  have hs := congrArg
    (fun z ↦
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p').mapDerivedCategory.map
          ((Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l g)).inv.app M) ≫
        (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l p')).inv.app
          ((adicUpperStar l g).mapDerivedCategory.obj M) ≫
        (NativeEncoding.derivedEncoding l X').map z)
    (nativeDerivedSquare_hom l sq M)
  apply hs.trans
  exact localize_inverse_cube
    (NativeEncoding.encoding l Y)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p')
    (adicUpperStar l g) (NativeEncoding.encoding l Y') (adicUpperStar l p')
    (NativeEncoding.encoding l X') (adicUpperStar l p) (adicUpperStar l v)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) p)
    (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) v)
    (NativeEncoding.encoding l X)
    (NativeEncoding.pullComparison l g) (NativeEncoding.pullComparison l p')
    (adicUpperStarCompIso l sq.w.symm) (NativeEncoding.condensedPullbackSquare l sq)
    (NativeEncoding.pullComparison l p) (NativeEncoding.pullComparison l v)
    (by
      intro N
      exact NativeEncoding.encoding_pullback_cube l sq N) M

private theorem native_exact_arrow (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (AdicSheaf l X)) :
    Nonempty (Arrow.mk ((NativeEncoding.derivedEncoding l Y').map
      ((adicDerivedBaseChange l sq).app M)) ≅
        Arrow.mk ((exactCondensedExchange l sq).app
          ((NativeEncoding.derivedEncoding l X).obj M))) := by
  have h := exchangeMate_cube
    (adicUpperStarLowerStarAdjunction l p).mapDerivedCategoryRightDerivedAdjunction
    (adicUpperStarLowerStarAdjunction l p').mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) p).mapDerivedCategoryRightDerivedAdjunction
    (CondensedRing.upperStarLowerStarAdjunction
      (Profinite.padicAlgClRingObj l) p').mapDerivedCategoryRightDerivedAdjunction
    (NativeEncoding.derivedEncoding l Y) (NativeEncoding.derivedEncoding l X)
    (NativeEncoding.derivedEncoding l Y') (NativeEncoding.derivedEncoding l X')
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l p))
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l g))
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l v))
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l p'))
    (adicDerivedPullSquare l sq).hom
    (Functor.mapDerivedCategorySquareIso (NativeEncoding.condensedPullbackSquare l sq)).hom
    (localized_cube l sq) M
  have hp := congr_app (derived_mate l p) M
  have hp' := congr_app (derived_mate l p')
    ((adicUpperStar l v).mapDerivedCategory.obj M)
  simp only [hp, hp'] at h
  refine ⟨Arrow.isoMk
    ((Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l g)).app
        ((adicLowerStar l p).rightDerivedFunctor.obj M) ≪≫
      (CondensedRing.upperStar (Profinite.padicAlgClRingObj l) g).mapDerivedCategory.mapIso
        ((NativeEncoding.derivedPushComparison l p).app M))
    ((NativeEncoding.derivedPushComparison l p').app
        ((adicUpperStar l v).mapDerivedCategory.obj M) ≪≫
      (CondensedRing.moduleObjectDerivedPushforward (Profinite.padicAlgClRingObj l) p').mapIso
        ((Functor.mapDerivedCategorySquareIso (NativeEncoding.pullComparison l v)).app M))
    ?_⟩
  simpa only [adicDerivedBaseChange, exactCondensedExchange, Iso.trans_hom,
    Functor.mapIso_hom, Iso.app_hom, Arrow.mk_hom, Arrow.mk_left, Arrow.mk_right,
    CondensedRing.moduleObjectDerivedPushforward, Category.assoc] using h.symm

attribute [local irreducible] CondensedRing.boundedConstructibleUpperStarComp

section Restriction
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ] (l : ℕ) [Fact l.Prime]
  {k : Type u} [Field k] [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
  {X' X Y' Y : Over (Spec (CommRingCat.of k))}
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom]
  {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}

omit [IsCommMonObj Λ] [Fact (Nat.Prime (ringChar k))] in
private theorem restricted_push_obj
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards Λ k)
    {A B : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    (f : A ⟶ B) (J : BoundedConstructible (condensedRingObj Λ A.left)) :
    ((CondensedRing.boundedConstructibleLowerStarOfPreserves Λ H f).obj J).obj =
      (CondensedRing.moduleObjectDerivedPushforward Λ f.left).obj J.obj := rfl

private theorem restricted_comp_hom
    {A B C : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (f : A ⟶ B) (g : B ⟶ C)
    (K : BoundedConstructible (condensedRingObj Λ C.left)) :
    ((CondensedRing.boundedConstructibleUpperStarComp Λ l f g).hom.app K).hom =
      (CondensedRing.leftDerivedUpperStarComp Λ f.left g.left).hom.app K.obj := by
  exact CondensedRing.boundedConstructibleUpperStarComp_hom_app_hom Λ l f g K

private theorem restricted_comp_inv
    {A B C : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    [LocallyOfFiniteType C.hom] [QuasiCompact C.hom] [IsSeparated C.hom]
    (f : A ⟶ B) (g : B ⟶ C)
    (K : BoundedConstructible (condensedRingObj Λ C.left)) :
    ((CondensedRing.boundedConstructibleUpperStarComp Λ l f g).inv.app K).hom =
      (CondensedRing.leftDerivedUpperStarComp Λ f.left g.left).inv.app K.obj := by
  have h : (boundedConstructible (condensedRingObj Λ A.left)).ι.mapIso
      ((CondensedRing.boundedConstructibleUpperStarComp Λ l f g).app K) =
      (CondensedRing.leftDerivedUpperStarComp Λ f.left g.left).app K.obj :=
    Iso.ext (restricted_comp_hom Λ l f g K)
  exact congrArg Iso.inv h

private theorem restricted_eq
    {A B : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom]
    [LocallyOfFiniteType B.hom] [QuasiCompact B.hom] [IsSeparated B.hom]
    {f g : A ⟶ B} (h : f = g)
    (K : BoundedConstructible (condensedRingObj Λ B.left)) :
    ((eqToIso (congrArg (CondensedRing.boundedConstructibleUpperStar Λ l) h)).hom.app K).hom =
    (eqToIso (congrArg
      (fun t : A ⟶ B ↦ CondensedRing.moduleObjectDerivedPullback Λ t.left) h)).hom.app K.obj := by
  subst g
  simp only [eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    ObjectProperty.FullSubcategory.id_hom,
    CondensedRing.boundedConstructibleUpperStar_obj_obj,
    CondensedRing.moduleObjectDerivedPullback]

private theorem bounded_square_hom (sq : CommSq v p' p g) :
    (CondensedRing.boundedConstructiblePullbackSquareComparison Λ l sq).hom =
      (CondensedRing.boundedConstructibleUpperStarComp Λ l p' g).inv ≫
        (eqToIso (congrArg (CondensedRing.boundedConstructibleUpperStar Λ l) sq.w.symm)).hom ≫
          (CondensedRing.boundedConstructibleUpperStarComp Λ l v p).hom := by
  rfl

omit [Fact (Nat.Prime (ringChar k))]
  [LocallyOfFiniteType X'.hom] [QuasiCompact X'.hom] [IsSeparated X'.hom]
  [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
  [LocallyOfFiniteType Y'.hom] [QuasiCompact Y'.hom] [IsSeparated Y'.hom]
  [LocallyOfFiniteType Y.hom] [QuasiCompact Y.hom] [IsSeparated Y.hom] in
private theorem ambient_square_hom (sq : CommSq v p' p g) :
    (CondensedRing.moduleObjectDerivedPullbackSquareComparison Λ
      (show CommSq v.left p'.left p.left g.left from (Over.forget _).map_commSq sq)).hom =
      (CondensedRing.leftDerivedUpperStarComp Λ p'.left g.left).inv ≫
        (eqToIso (congrArg
          (fun t : X' ⟶ Y ↦ CondensedRing.moduleObjectDerivedPullback Λ t.left)
          sq.w.symm)).hom ≫
        (CondensedRing.leftDerivedUpperStarComp Λ v.left p.left).hom := by
  rfl

attribute [local irreducible]
  CondensedRing.boundedConstructiblePullbackSquareComparison
  CondensedRing.moduleObjectDerivedPullbackSquareComparison

private theorem restricted_square (sq : CommSq v p' p g)
    (K : BoundedConstructible (condensedRingObj Λ Y.left)) :
    ((CondensedRing.boundedConstructiblePullbackSquareComparison Λ l sq).hom.app K).hom =
      (CondensedRing.moduleObjectDerivedPullbackSquareComparison Λ
        (show CommSq v.left p'.left p.left g.left from
          (Over.forget _).map_commSq sq)).hom.app K.obj := by
  have h₁ := congrArg (fun f ↦ f.hom) (congr_app (bounded_square_hom Λ l sq) K)
  have h₂ := congr_app (ambient_square_hom Λ sq) K.obj
  simp only [NatTrans.comp_app, ObjectProperty.FullSubcategory.comp_hom] at h₁ h₂
  exact h₁.trans ((congrArg₂ (fun a b ↦ a ≫ b) (restricted_comp_inv Λ l p' g K)
    (congrArg₂ (fun a b ↦ a ≫ b) (restricted_eq Λ l sq.w.symm K)
      (restricted_comp_hom Λ l v p K))).trans h₂.symm)

end Restriction

private def arrow_component_iso
    {C D : Type*} [Category C] [Category D] {F G : C ⥤ D}
    (t : F ⟶ G) {A B : C} (e : A ≅ B) :
    Arrow.mk (t.app A) ≅ Arrow.mk (t.app B) := by
  refine Arrow.isoMk (F.mapIso e) (G.mapIso e) ?_
  simpa only [Arrow.mk_hom, Functor.mapIso_hom] using t.naturality e.hom

private theorem underlying_arrow_eq
    {C : Type*} [Category C] (P : ObjectProperty C)
    {A B : P.FullSubcategory} (f : A ⟶ B) :
    nativeUnderlyingExchangeArrow P f = Arrow.mk f.hom := by
  unfold nativeUnderlyingExchangeArrow
  rfl

private instance encodingAtAdditive (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (nativeExchangeEncodingAt l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T).Additive :=
  nativeExchangeEncodingAt_additive l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T

private instance encodingAtEquivalence (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (nativeExchangeEncodingAt l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T).IsEquivalence :=
  nativeExchangeEncodingAt_isEquivalence l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T

private theorem mapDerived_eq_of_eq
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    [HasDerivedCategory C] [HasDerivedCategory D]
    (F G : C ⥤ D) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [PreservesFiniteLimits G] [PreservesFiniteColimits G] (h : F = G) :
    F.mapDerivedCategory = G.mapDerivedCategory := by
  subst G
  rfl

private theorem encodingAt_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    nativeExchangeEncodingAt l (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T =
      NativeEncoding.encoding l T := by
  unfold nativeExchangeEncodingAt
  exact encoding_eq l T

private theorem encodingDerived_eq (l : ℕ) [Fact l.Prime] (T : Scheme.{u}) :
    (nativeExchangeEncodingAt l
      (Mon.mk (Profinite.padicAlgClRingObj l)) rfl T).mapDerivedCategory =
      NativeEncoding.derivedEncoding l T := by
  unfold NativeEncoding.derivedEncoding
  exact mapDerived_eq_of_eq _ _ (encodingAt_eq l T)

private theorem nonempty_iso_trans {C : Type*} [Category C] {A B D : C}
    (h : Nonempty (A ≅ B)) (h' : Nonempty (B ≅ D)) : Nonempty (A ≅ D) := by
  obtain ⟨e⟩ := h
  obtain ⟨e'⟩ := h'
  exact ⟨e ≪≫ e'⟩

private theorem nonempty_iso_symm {C : Type*} [Category C] {A B : C}
    (h : Nonempty (A ≅ B)) : Nonempty (B ≅ A) := by
  obtain ⟨e⟩ := h
  exact ⟨e.symm⟩

attribute [local irreducible]
  CondensedRing.boundedConstructibleBaseChangeOfPreserves
  CondensedRing.moduleObjectDerivedExchange

private theorem native_input_arrow (l : ℕ) [Fact l.Prime]
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (AdicSheaf l X))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj (Profinite.padicAlgClRingObj l) X)))
    (e : (nativeExchangeEncodingAt l
      (Mon.mk (Profinite.padicAlgClRingObj l)) rfl X).mapDerivedCategory.obj M ≅ K) :
    Nonempty (Arrow.mk ((nativeExchangeEncodingAt l
      (Mon.mk (Profinite.padicAlgClRingObj l)) rfl Y').mapDerivedCategory.map
        ((adicDerivedBaseChange l sq).app M)) ≅
      Arrow.mk ((exactCondensedExchange l sq).app K)) := by
  rw [encodingDerived_eq l X] at e
  rw [encodingDerived_eq l Y']
  exact nonempty_iso_trans (native_exact_arrow l sq M)
    ⟨arrow_component_iso (exactCondensedExchange l sq) e⟩

attribute [-instance] encodingAtAdditive encodingAtEquivalence

private theorem native_input_arrow_at (l : ℕ) [Fact l.Prime]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Scheme.{u}} {v : X' ⟶ X} {p' : X' ⟶ Y'}
    {p : X ⟶ Y} {g : Y' ⟶ Y} (sq : CommSq v p' p g)
    (M : DerivedCategory (AdicSheaf l X))
    (K : DerivedCategory (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1})
      (condensedRingObj Λ.X X)))
    (e : (nativeExchangeEncodingAt l Λ hΛ X).mapDerivedCategory.obj M ≅ K) :
    Nonempty (Arrow.mk ((nativeExchangeEncodingAt l Λ hΛ Y').mapDerivedCategory.map
      ((adicDerivedBaseChange l sq).app M)) ≅
      Arrow.mk ((exactCondensedExchangeFor Λ.X sq).app K)) := by
  subst Λ
  rw [exactCondensedExchangeFor_canonical]
  exact native_input_arrow l sq M K e

set_option allowUnsafeReducibility true in
attribute [local reducible] Over.forget Comma.fst
set_option allowUnsafeReducibility true in
attribute [local irreducible] CondensedRing.rationalCoefficientPushforwardPreservation

attribute [local irreducible] CondensedRing.boundedConstructibleUpperStar
  CondensedRing.derivedUpperStarLowerStarAdjunction ObjectProperty.lift
  CondensedRing.boundedConstructibleUpperStarCompatibility
  Functor.squareTransport Adjunction.restrictFullyFaithful

private theorem generic_exchange_comparison_at
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    (H : CondensedRing.PreservesBoundedConstructiblePushforwards Λ.X k)
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (K : BoundedConstructible (condensedRingObj Λ.X X.left))
    (e : (nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M ≅ K.obj) :
    Nonempty (Arrow.mk ((nativeExchangeEncodingAt l Λ hΛ Y'.left).mapDerivedCategory.map
        ((adicDerivedBaseChange l
          ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M)) ≅
      nativeUnderlyingExchangeArrow (boundedConstructible (condensedRingObj Λ.X Y'.left))
        ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
          H
          sq.toCommSq).app K)) := by
  have htri (A : Over (Spec (CommRingCat.of k)))
      [LocallyOfFiniteType A.hom] [QuasiCompact A.hom] [IsSeparated A.hom] :
      (boundedConstructible (condensedRingObj Λ.X A.left)).IsTriangulated := by
    have : IsLocallyNoetherian A.left := LocallyOfFiniteType.isLocallyNoetherian A.hom
    have : CompactSpace A.left := QuasiCompact.compactSpace_of_compactSpace A.hom
    have : IsNoetherian A.left := ⟨⟩
    subst hΛ
    exact CondensedRing.isTriangulated_boundedConstructible_ellAdic_padicAlgCl A.left l
  have := htri X
  have := htri Y
  have := htri X'
  have := htri Y'
  have hBC :=
    CondensedRing.boundedConstructibleBaseChangeOfPreserves_app_eq_moduleObjectDerivedExchange
      Λ.X l sq.toCommSq (@H) (restricted_square Λ.X l sq.toCommSq) K
  rw [underlying_arrow_eq, hBC]
  -- Normalize the endpoints explicitly before applying the ambient comparison.
  simp only [Functor.comp_obj, CondensedRing.boundedConstructibleUpperStar_obj_obj,
    restricted_push_obj]
  refine nonempty_iso_trans
    (B := Arrow.mk ((exactCondensedExchangeFor Λ.X
      (show CommSq v.left p'.left p.left g.left from
        (Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app K.obj)) ?_ ?_
  · apply native_input_arrow_at
    exact e
  · apply nonempty_iso_symm
    apply totalDerivedExchange_exact_comparisonFor

/-- The encoded native mate and the underlying restricted condensed mate are isomorphic
as arrows. No properness or native constructibility hypothesis enters this comparison. -/
theorem nativeDerivedExchange_condensed_comparison
    (l : ℕ) [Fact l.Prime] (k : Type u) [Field k]
    [Fact (ringChar k).Prime] [Fact (ringChar k ≠ l)]
    (Λ : Mon (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}))
    [IsCommMonObj Λ.X] (hΛ : Λ = Mon.mk (Profinite.padicAlgClRingObj l))
    {X' X Y' Y : Over (Spec (CommRingCat.of k))}
    [LocallyOfFiniteType X'.hom]
    [QuasiCompact X'.hom]
    [IsSeparated X'.hom]
    [LocallyOfFiniteType X.hom]
    [QuasiCompact X.hom]
    [IsSeparated X.hom]
    [LocallyOfFiniteType Y'.hom]
    [QuasiCompact Y'.hom]
    [IsSeparated Y'.hom]
    [LocallyOfFiniteType Y.hom]
    [QuasiCompact Y.hom]
    [IsSeparated Y.hom]
    {v : X' ⟶ X} {p' : X' ⟶ Y'} {p : X ⟶ Y} {g : Y' ⟶ Y}
    (sq : IsPullback v p' p g) (M : DerivedCategory (AdicSheaf l X.left))
    (K : BoundedConstructible (condensedRingObj Λ.X X.left))
    (e : (nativeExchangeEncodingAt l Λ hΛ X.left).mapDerivedCategory.obj M ≅ K.obj) :
    Nonempty (Arrow.mk ((nativeExchangeEncodingAt l Λ hΛ Y'.left).mapDerivedCategory.map
        ((adicDerivedBaseChange l
          ((Over.forget (Spec (CommRingCat.of k))).map_commSq sq.toCommSq)).app M)) ≅
      nativeUnderlyingExchangeArrow (boundedConstructible (condensedRingObj Λ.X Y'.left))
        ((CondensedRing.boundedConstructibleBaseChangeOfPreserves Λ.X l
          (CondensedRing.rationalCoefficientPushforwardPreservation l Λ (Or.inr hΛ))
          sq.toCommSq).app K)) := by
  refine generic_exchange_comparison_at l k Λ hΛ ?_ sq M K e

end AlgebraicGeometry.ProEtale

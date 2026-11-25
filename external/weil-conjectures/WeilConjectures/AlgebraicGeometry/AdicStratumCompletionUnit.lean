/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.FiniteLocallyClosedStratification
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleInverseImage
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
import WeilConjectures.AlgebraicGeometry.AdicStratumCoverConservativity
import all WeilConjectures.AlgebraicGeometry.CompletedPullbackAdjunction
import WeilConjectures.AlgebraicGeometry.ExactCompletedKoszulPullback
import WeilConjectures.AlgebraicGeometry.ProEtaleImmersionLimitPreservation
import WeilConjectures.AlgebraicGeometry.ProEtaleProductsExact
import WeilConjectures.AlgebraicGeometry.ProEtaleWeaklyEtaleLocalization
import WeilConjectures.CategoryTheory.RingedCechKoszulHomLimitComparison

/-!
# Restriction of the actual Koszul completion unit

Source: Bhatt--Scholze, Lemma 6.5.8, Remark 6.5.10 and Proposition 6.6.11;
Stacks Project, proetale.tex, Tags 099L and 099M, and algebraization.tex, Tag 0A0E
(auxiliary; not a blueprint node).

We use the recorded equivalent small model of each pro-etale site. Its object and
morphism universes are both `u+1`; the original site's morphism universe remains `u`.
Algebraic inverse-image data fixes operations on all generalized sections. In particular
its completed coefficient map is the recorded limit lift of the finite projections.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option linter.all false
set_option linter.unusedVariables false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u v

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local irreducible] ConstantCompletion.completed ConstantCompletion.derivedPull
  HasDerivedCategory.standard

namespace AlgebraicGeometry.Scheme.SfbAdicRestriction

/-- The equivalence from the small model to the original pro-etale sheaf category.
Source: Stacks Tags 00YY and 09A5
(auxiliary; not a blueprint node). -/
def modelEquivalence (X : Scheme.{u}) (D : Type v) [Category.{u + 1} D] :
    Sheaf (proEtaleModelTopology X) D ≌ Sheaf (ProEt.topology X) D :=
  CategoryTheory.Equivalence.mk
    ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
      D (ProEt.topology X) (proEtaleModelTopology X))
    ((AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
      D (proEtaleModelTopology X) (ProEt.topology X))
    (Iso.refl _) (Iso.refl _)

attribute [local irreducible] modelEquivalence

/-- The specified pro-etale inverse image, transported through the site equivalences.
Source: Stacks Tags 09A5 and 00YV
(auxiliary; not a blueprint node). -/
def inverse {X S : Scheme.{u}} (i : S ⟶ X) :
    Sheaf (proEtaleModelTopology X) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology S) (Type (u + 1)) :=
  (modelEquivalence X (Type (u + 1))).functor ⋙
    proEtaleSheafInverseImage i (Type (u + 1)) ⋙
      (modelEquivalence S (Type (u + 1))).inverse

/-- Its transported right adjoint, the actual pro-etale direct image.
Source: Stacks Tags 09A5 and 00YV
(auxiliary; not a blueprint node). -/
def direct {X S : Scheme.{u}} (i : S ⟶ X) :
    Sheaf (proEtaleModelTopology S) (Type (u + 1)) ⥤
      Sheaf (proEtaleModelTopology X) (Type (u + 1)) :=
  (modelEquivalence S (Type (u + 1))).functor ⋙
    proEtaleSheafDirectImage i (Type (u + 1)) ⋙
      (modelEquivalence X (Type (u + 1))).inverse

/-- Transport of the specified inverse-image adjunction, with no new functor choice.
Source: Stacks Tag 00YV (auxiliary; not a blueprint node). -/
def adjunction {X S : Scheme.{u}} (i : S ⟶ X) : inverse i ⊣ direct i :=
  ((modelEquivalence X (Type (u + 1))).toAdjunction.comp
    (proEtaleSheafAdjunction i (Type (u + 1)))).comp
      (modelEquivalence S (Type (u + 1))).symm.toAdjunction

/-- Finite-limit structure inherited from the original inverse image and equivalences.
Source: Stacks Tag 00YV (auxiliary; not a blueprint node). -/
instance inverse_finiteLimits {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i] :
    PreservesFiniteLimits (inverse i) :=
  haveI := (proEtale_immersion_inverseImage_preservesLimits i).1
  inferInstanceAs (PreservesFiniteLimits
    ((modelEquivalence X (Type (u + 1))).functor ⋙
      proEtaleSheafInverseImage i (Type (u + 1)) ⋙
        (modelEquivalence S (Type (u + 1))).inverse))

private theorem inverse_limits {X S : Scheme.{u}} (i : S ⟶ X) [IsImmersion i] :
    PreservesLimitsOfSize.{0, 0} (inverse i) := by
  have := (proEtale_immersion_inverseImage_preservesLimits i).1
  have : PreservesLimitsOfSize.{0, 0}
      (proEtaleSheafInverseImage i (Type (u + 1))) :=
    preservesLimitsOfSize_shrink _
  unfold inverse
  infer_instance

attribute [local irreducible] inverse direct adjunction

private theorem moduleSiteEquivalence
    {C : Type*} [Category C] {H : Type*} [Category H]
    (J : GrothendieckTopology C) (K : GrothendieckTopology H)
    (e : C ≌ H) [e.functor.IsContinuous J K] [e.inverse.IsContinuous K J]
    (R : Sheaf J RingCat.{v}) (S : Sheaf K RingCat.{v})
    (c : S ≅ (e.inverse.sheafPushforwardContinuous RingCat.{v} K J).obj R) :
    ∃ q : SheafOfModules.{v} R ≌ SheafOfModules.{v} S,
      q.functor ⋙ SheafOfModules.forget _ =
        SheafOfModules.forget _ ⋙ PresheafOfModules.pushforward (F := e.inverse) c.hom.hom := by
  let ψ : R ⟶ (e.functor.sheafPushforwardContinuous RingCat.{v} J K).obj S :=
    { hom := Functor.whiskerRight e.op.unitIso.hom R.obj ≫
        Functor.whiskerLeft e.functor.op c.inv.hom }
  have H₁ : Functor.whiskerRight (NatTrans.op e.symm.counit) R.obj =
      ψ.hom ≫ e.functor.op.whiskerLeft c.hom.hom := by
    apply NatTrans.ext
    funext U
    change R.obj.map _ =
      (R.obj.map _ ≫ c.inv.hom.app _) ≫ c.hom.hom.app _
    rw [Category.assoc]
    have hc := congrArg (fun f ↦ f.hom.app (e.functor.op.obj U)) c.inv_hom_id
    have hc' : c.inv.hom.app (e.functor.op.obj U) ≫
        c.hom.hom.app (e.functor.op.obj U) = 𝟙 _ := hc
    change R.obj.map (e.unitInv.app U.unop).op =
      R.obj.map (e.unitInv.app U.unop).op ≫
        (c.inv.hom.app (e.functor.op.obj U) ≫ c.hom.hom.app (e.functor.op.obj U))
    exact (Category.comp_id _).symm.trans
      (congrArg (fun f ↦ R.obj.map (e.unitInv.app U.unop).op ≫ f) hc'.symm)
  have H₂ : c.hom.hom ≫ e.inverse.op.whiskerLeft ψ.hom ≫
      Functor.whiskerRight (NatTrans.op e.symm.unit) S.obj = 𝟙 S.obj := by
    apply NatTrans.ext
    funext U
    change c.hom.hom.app U ≫
      (R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U))) ≫
        S.obj.map (e.counitInv.app U.unop).op = 𝟙 _
    rw [Category.assoc]
    have hn := c.inv.hom.naturality (e.counitInv.app U.unop).op
    change R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op ≫
      c.inv.hom.app U =
      c.inv.hom.app (e.functor.op.obj (e.inverse.op.obj U)) ≫
        S.obj.map (e.counitInv.app U.unop).op at hn
    rw [← hn]
    have hm : R.obj.map (e.unitInv.app (e.inverse.obj U.unop)).op ≫
        R.obj.map (e.inverse.map (e.counitInv.app U.unop)).op = 𝟙 _ := by
      rw [← Functor.map_comp, ← op_comp]
      simp
    rw [← Category.assoc (R.obj.map _) (R.obj.map _) _, hm]
    change c.hom.hom.app U ≫ 𝟙 _ ≫ c.inv.hom.app U = 𝟙 _
    have hc : c.hom.hom.app U ≫ c.inv.hom.app U = 𝟙 _ :=
      congrArg (fun f ↦ f.hom.app U) c.hom_inv_id
    exact (congrArg (fun f ↦ c.hom.hom.app U ≫ f)
      (Category.id_comp (c.inv.hom.app U))).trans hc
  have : e.symm.functor.IsContinuous K J := inferInstanceAs (e.inverse.IsContinuous K J)
  have : e.symm.inverse.IsContinuous J K := inferInstanceAs (e.functor.IsContinuous J K)
  refine ⟨SheafOfModules.pushforwardPushforwardEquivalence e.symm c.hom ψ H₁ H₂, rfl⟩

private theorem smallProducts_exact (X : Scheme.{u})
    (R : Sheaf (proEtaleModelTopology X) RingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1} R) := by
  let e := (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
  let A := ((AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).sheafPushforwardContinuous
    RingCat.{u + 1} (ProEt.topology X) (proEtaleModelTopology X)).obj R
  have : e.functor.IsContinuous (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs (AsSmall.down.IsContinuous (proEtaleModelTopology X)
      (ProEt.topology X))
  have : e.inverse.IsContinuous (ProEt.topology X) (proEtaleModelTopology X) :=
    proEtaleModelUp_isContinuous X
  obtain ⟨q, _⟩ := moduleSiteEquivalence (proEtaleModelTopology X)
    (ProEt.topology X) e R A (Iso.refl _)
  have := ProEt.products_exact.{u, u + 1, 0} X A ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) q.symm

private theorem sliceProducts_exact (X : Scheme.{u}) (U : proEtaleSiteModel X)
    (R : Sheaf ((proEtaleModelTopology X).over U) RingCat.{u + 1}) :
    HasExactLimitsOfShape (Discrete ℕ) (SheafOfModules.{u + 1} R) := by
  let e₀ := Over.postEquiv (X := U)
    (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).symm
  let W := (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).obj U
  let e := e₀.trans (ProEt.sliceEquiv X W)
  let J := (proEtaleModelTopology X).over U
  let K := ProEt.topology W.left
  have : (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsDenseSubsite
      (ProEt.topology X) (proEtaleModelTopology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsDenseSubsite
      (ProEt.topology X)
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)))
  have : (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsDenseSubsite
      (proEtaleModelTopology X) (ProEt.topology X) :=
    inferInstanceAs ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsDenseSubsite
      ((AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.inducedTopology
        (ProEt.topology X)) (ProEt.topology X))
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).functor.IsCocontinuous
      (ProEt.topology X) (proEtaleModelTopology X) := by
    change (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X).IsCocontinuous _ _
    infer_instance
  have : (AsSmall.equiv.{u, u + 1, u + 1} (C := X.ProEt)).inverse.IsCocontinuous
      (proEtaleModelTopology X) (ProEt.topology X) := by
    change (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).IsCocontinuous _ _
    infer_instance
  have : e₀.functor.IsCocontinuous J ((ProEt.topology X).over W) := by
    change (Over.post (X := U)
      (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt)).IsCocontinuous _ _
    infer_instance
  have : e₀.inverse.IsCocontinuous ((ProEt.topology X).over W) J := by
    change (Over.post (X := W) (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X) ⋙
      Over.map (𝟙 U)).IsCocontinuous _ _
    have hp : (Over.post (X := W)
        (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X)).IsCocontinuous
        ((ProEt.topology X).over W)
        ((proEtaleModelTopology X).over (AsSmall.up.obj W)) := inferInstance
    change (Over.post (X := W)
      (AsSmall.up : X.ProEt ⥤ proEtaleSiteModel X)).IsCocontinuous
      ((ProEt.topology X).over W) ((proEtaleModelTopology X).over U) at hp
    have : (Over.map (𝟙 U)).IsCocontinuous ((proEtaleModelTopology X).over U) J :=
      inferInstanceAs ((Over.map (𝟙 U)).IsCocontinuous
        ((proEtaleModelTopology X).over U) ((proEtaleModelTopology X).over U))
    exact CategoryTheory.isCocontinuous_comp _ _ ((ProEt.topology X).over W)
      ((proEtaleModelTopology X).over U)
  have : e₀.inverse.IsDenseSubsite ((ProEt.topology X).over W) J :=
    e₀.isDenseSubsite_inverse_of_isCocontinuous J ((ProEt.topology X).over W)
  have : e₀.functor.IsContinuous J ((ProEt.topology X).over W) := by infer_instance
  have : e₀.inverse.IsContinuous ((ProEt.topology X).over W) J := by infer_instance
  have := ProEt.sliceDense X W
  have : (ProEt.sliceEquiv X W).functor.IsContinuous
      ((ProEt.topology X).over W) (ProEt.topology W.left) := by infer_instance
  have : (ProEt.sliceEquiv X W).inverse.IsContinuous
      (ProEt.topology W.left) ((ProEt.topology X).over W) := by infer_instance
  have : e.functor.IsContinuous J K := by
    exact Functor.isContinuous_comp _ _ J ((ProEt.topology X).over W) K
  have : e.inverse.IsContinuous K J := by
    exact Functor.isContinuous_comp _ _ K ((ProEt.topology X).over W) J
  let A := (e.inverse.sheafPushforwardContinuous RingCat.{u + 1} K J).obj R
  obtain ⟨q, _⟩ := moduleSiteEquivalence J K e R A (Iso.refl _)
  have := ProEt.products_exact.{u, u + 1, 0} W.left A ℕ
  exact HasExactLimitsOfShape.of_codomain_equivalence (Discrete ℕ) q.symm

section Slice

variable {C : Type v} [SmallCategory C] (J : GrothendieckTopology C) (U : C)

/-- Slice restriction with all algebraic operations evaluated on the underlying object.
Source: Stacks Tags 00XZ and 03D2
(auxiliary; not a blueprint node). -/
def sliceAlgebra : ConstantCompletion.InverseImageData (J.overPullback (Type v) U) where
  rings := J.overPullback CommRingCat.{v} U
  algebra O :=
    { ringUnderlying := Iso.refl _
      ringAdd := fun _ _ _ _ h V x ↦ h (op V.unop.left) x
      ringMul := fun _ _ _ _ h V x ↦ h (op V.unop.left) x
      ringZero := fun _ _ h V x ↦ h (op V.unop.left) x
      ringOne := fun _ _ h V x ↦ h (op V.unop.left) x
      modules := SheafOfModules.overFunctor (siteModuleRings O) U
      moduleUnderlying := Iso.refl _
      moduleAdd := fun _ _ _ _ _ h V x ↦ h (op V.unop.left) x
      moduleZero := fun _ _ _ h V x ↦ h (op V.unop.left) x
      moduleSMul := fun _ _ _ _ _ h V x ↦ h (op V.unop.left) x }
  ring_naturality := fun _ ↦ (Category.comp_id _).trans (Category.id_comp _).symm
  constants := NatIso.ofComponents
    (fun A ↦ ((Over.forget U).pushforwardContinuousSheafificationCompatibility
      CommRingCat.{v} (J.over U) J).app ((Functor.const Cᵒᵖ).obj A) |>.symm)
    (fun f ↦ by
      exact ((Over.forget U).pushforwardContinuousSheafificationCompatibility
        CommRingCat.{v} (J.over U) J).inv.naturality
          ((Functor.const Cᵒᵖ).map f))

/-- The right adjoint of slice restriction, from the canonical site localization.
Source: Stacks Tag 00XZ (auxiliary; not a blueprint node). -/
abbrev sliceDirect :=
  (Over.forget U).sheafPushforwardCocontinuous (Type v) (J.over U) J

/-- The canonical localization adjunction, rather than a chosen module map.
Source: Stacks Tag 00XZ (auxiliary; not a blueprint node). -/
def sliceAdjunction : J.overPullback (Type v) U ⊣ sliceDirect J U :=
  (Over.forget U).sheafAdjunctionCocontinuous (Type v) (J.over U) J

attribute [local irreducible] sliceAlgebra sliceAdjunction

end Slice

section Comparisons

variable {C D : Type v} [SmallCategory C] [SmallCategory D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D}
  {L : Sheaf J (Type v) ⥤ Sheaf K (Type v)}
  (F : ConstantCompletion.InverseImageData L)
  (V : Sheaf K (Type v) ⥤ Sheaf J (Type v)) (adj : L ⊣ V)
  [PreservesFiniteLimits L] (A : Type v) [CommRing A] (I : Ideal A)

/-- Derived module inverse image with the finite-projection completed coefficient map.
Source: Stacks Tags 099L and 06YY
(auxiliary; not a blueprint node). -/
def completedPull :
    ConstantCompletion.D (ConstantCompletion.completed J A I) ⥤
      ConstantCompletion.D (ConstantCompletion.completed K A I) :=
  (ConstantCompletion.derivedPull F V adj (ConstantCompletion.completedMap F A I)).functor

/-- The finite derived comparison in the actual quotient coefficient category. Its three
factors are the recorded K-flat-normalized finite scalar comparisons and the uniquely
normalized completed finite pullback comparison. Thus its source uses the actual
projection of the completed ring, not a replacement finite coefficient object.
Source: Stacks Tags 099L and 06YY
(auxiliary; not a blueprint node). -/
def finiteComparison [IsNoetherianRing A] (n : ℕ) :
    completedPull F V adj A I ⋙
        ConstantCompletion.extend (ConstantCompletion.projection K A I n) ≅
      ConstantCompletion.extend (ConstantCompletion.projection J A I n) ⋙
        (ConstantCompletion.derivedPull F V adj
          (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor :=
  Functor.isoWhiskerLeft (completedPull F V adj A I)
    (ConstantCompletion.finiteDerivedComparison K A I n).choose.symm ≪≫
  (ConstantCompletion.completedFinitePull_existsUnique F V adj A I n).exists.choose ≪≫
  Functor.isoWhiskerRight (ConstantCompletion.finiteDerivedComparison J A I n).choose
    (ConstantCompletion.derivedPull F V adj
      (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor

/-- The three restriction clauses: the specified coefficient map is invertible; the
universal derived pullback computes on every complex; and the actual strict Koszul units
agree under a natural completion comparison. The finite comparison satisfies the
canonical scalar-insertion normalization in each quotient coefficient category. Finally local
internal-Hom completeness
restricts. This is just a package of the conclusions, not a replacement definition of
completeness or of completion.
Source: Bhatt--Scholze, Lemma 6.5.8 and Remark 6.5.10; Stacks Tags 099M and 0A0E
(auxiliary; not a blueprint node). -/
def UnitRestriction [IsNoetherianRing A] (r : ℕ) (a : Fin r → A) : Prop :=
  IsIso (ConstantCompletion.completedMap F A I) ∧
  (∀ P : ConstantCompletion.Cx (ConstantCompletion.completed J A I),
    IsIso ((ConstantCompletion.derivedPull F V adj
      (ConstantCompletion.completedMap F A I)).comparison.app P)) ∧
  (∀ (PX : ConstantCompletion.KoszulPresentation J A I true r a)
      (PS : ConstantCompletion.KoszulPresentation K A I true r a),
    ∃ e : ConstantCompletion.koszulCompletion J A I PX ⋙ completedPull F V adj A I ≅
        completedPull F V adj A I ⋙ ConstantCompletion.koszulCompletion K A I PS,
      ∀ M : ConstantCompletion.D (ConstantCompletion.completed J A I),
        (completedPull F V adj A I).map (ConstantCompletion.koszulUnit J A I PX M) ≫
            e.hom.app M =
          ConstantCompletion.koszulUnit K A I PS ((completedPull F V adj A I).obj M)) ∧
  (∀ (n : ℕ) (M : ConstantCompletion.D (ConstantCompletion.completed J A I)),
    (ConstantCompletion.extend (ConstantCompletion.quotient K A I n)).map
          ((ConstantCompletion.derivedPullComparison F V adj A I).app M) ≫
        (ConstantCompletion.finiteDerivedComparison K A I n).choose.hom.app
          ((completedPull F V adj A I).obj M) =
      (ConstantCompletion.finitePull F V adj A I n).hom.app
          ((ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)).obj M) ≫
        (ConstantCompletion.derivedPull F V adj
          (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor.map
            ((ConstantCompletion.finiteDerivedComparison J A I n).choose.hom.app M) ≫
        (finiteComparison F V adj A I n).inv.app M) ∧
  (∀ M : ConstantCompletion.D (ConstantCompletion.completed J A I),
    ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) M →
      ConstantCompletion.IsComplete (ConstantCompletion.projection K A I 0)
        ((completedPull F V adj A I).obj M))

private theorem rings_preserveTowers [PreservesLimitsOfShape ℕᵒᵖ L] :
    PreservesLimitsOfShape ℕᵒᵖ F.rings := by
  let UJ := sheafCompose J (CategoryTheory.forget CommRingCat.{v})
  let UK := sheafCompose K (CategoryTheory.forget CommRingCat.{v})
  let e : UJ ⋙ L ≅ F.rings ⋙ UK :=
    NatIso.ofComponents (fun O ↦ (F.algebra O).ringUnderlying)
      (fun f ↦ F.ring_naturality f)
  have hU (T : GrothendieckTopology C) :
      PreservesLimitsOfShape ℕᵒᵖ (sheafCompose T (CategoryTheory.forget CommRingCat.{v})) := by
    let U := sheafCompose T (CategoryTheory.forget CommRingCat.{v})
    have : PreservesLimitsOfShape ℕᵒᵖ (U ⋙ sheafToPresheaf T (Type v)) := by
      change PreservesLimitsOfShape ℕᵒᵖ
        (sheafToPresheaf T CommRingCat.{v} ⋙
          (Functor.whiskeringRight Cᵒᵖ CommRingCat.{v} (Type v)).obj
            (CategoryTheory.forget CommRingCat.{v}))
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves U (sheafToPresheaf T (Type v))
  have : PreservesLimitsOfShape ℕᵒᵖ UJ := hU J
  have : PreservesLimitsOfShape ℕᵒᵖ UK := by
    let U := sheafCompose K (CategoryTheory.forget CommRingCat.{v})
    have : PreservesLimitsOfShape ℕᵒᵖ (U ⋙ sheafToPresheaf K (Type v)) := by
      change PreservesLimitsOfShape ℕᵒᵖ
        (sheafToPresheaf K CommRingCat.{v} ⋙
          (Functor.whiskeringRight Dᵒᵖ CommRingCat.{v} (Type v)).obj
            (CategoryTheory.forget CommRingCat.{v}))
      infer_instance
    exact preservesLimitsOfShape_of_reflects_of_preserves U (sheafToPresheaf K (Type v))
  have : PreservesLimitsOfShape ℕᵒᵖ (F.rings ⋙ UK) :=
    preservesLimitsOfShape_of_natIso e
  have : ReflectsLimitsOfShape ℕᵒᵖ UK := reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact preservesLimitsOfShape_of_reflects_of_preserves F.rings UK

attribute [local semireducible] ConstantCompletion.completed

private theorem completedMap_isIso [PreservesLimitsOfShape ℕᵒᵖ L] :
    IsIso (ConstantCompletion.completedMap F A I) := by
  have := rings_preserveTowers F
  let T := ConstantCompletion.finiteSystem J A I
  let T' := ConstantCompletion.finiteSystem K A I
  let t : T ⋙ F.rings ⟶ T' := NatTrans.ofOpSequence
    (fun n ↦ (F.constants.app (CommRingCat.of (A ⧸ I ^ (n + 1)))).hom) (by
      intro n
      simpa only [T, T', ConstantCompletion.finiteSystem, Functor.comp_map,
        Functor.ofOpSequence_map_homOfLE_succ, ConstantCompletion.transition,
        Iso.app_hom] using
          F.constants.hom.naturality
            (CommRingCat.ofHom (Ideal.Quotient.factorPow I (Nat.le_succ (n + 1)))))
  have : ∀ n, IsIso (t.app n) := fun n ↦ by
    change IsIso ((F.constants.app (CommRingCat.of (A ⧸ I ^ (n.unop + 1)))).hom)
    infer_instance
  have : IsIso t := NatIso.isIso_of_isIso_app t
  let e : T ⋙ F.rings ≅ T' := asIso t
  let c := (Cone.postcompose e.hom).obj (F.rings.mapCone (limit.cone T))
  have hc : IsLimit c := (IsLimit.postcomposeHomEquiv e _).symm
    (isLimitOfPreserves F.rings (limit.isLimit T))
  let e' := hc.conePointUniqueUpToIso (limit.isLimit T')
  have h : e'.hom = ConstantCompletion.completedMap F A I := by
    apply (limit.isLimit T').hom_ext
    intro n
    exact (hc.conePointUniqueUpToIso_hom_comp (limit.isLimit T') n).trans
      (limit.lift_π (F := T') _ n).symm
  rw [← h]
  infer_instance

attribute [local semireducible] HasDerivedCategory.standard

private theorem finiteComparison_normalized [IsNoetherianRing A] (n : ℕ)
    (M : ConstantCompletion.D (ConstantCompletion.completed J A I)) :
    (ConstantCompletion.extend (ConstantCompletion.quotient K A I n)).map
          ((ConstantCompletion.derivedPullComparison F V adj A I).app M) ≫
        (ConstantCompletion.finiteDerivedComparison K A I n).choose.hom.app
          ((completedPull F V adj A I).obj M) =
      (ConstantCompletion.finitePull F V adj A I n).hom.app
          ((ConstantCompletion.dres (ConstantCompletion.coefficientMap J A I)).obj M) ≫
        (ConstantCompletion.derivedPull F V adj
          (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor.map
            ((ConstantCompletion.finiteDerivedComparison J A I n).choose.hom.app M) ≫
        (finiteComparison F V adj A I n).inv.app M := by
  let eJ := (ConstantCompletion.finiteDerivedComparison J A I n).choose
  let eK := (ConstantCompletion.finiteDerivedComparison K A I n).choose
  let e := (ConstantCompletion.completedFinitePull_existsUnique F V adj A I n).exists.choose
  have he := (ConstantCompletion.completedFinitePull_existsUnique F V adj A I n
    ).exists.choose_spec M
  dsimp only [finiteComparison, Iso.trans_inv, Iso.symm_inv,
    Functor.isoWhiskerRight_inv, Functor.isoWhiskerLeft_inv, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Category.assoc]
  change _ ≫ eK.hom.app _ =
    (ConstantCompletion.finitePull F V adj A I n).hom.app _ ≫
      (ConstantCompletion.derivedPull F V adj
        (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor.map
          (eJ.hom.app M) ≫
      (ConstantCompletion.derivedPull F V adj
        (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor.map
          (eJ.inv.app M) ≫ e.inv.app M ≫ eK.hom.app _
  let G := (ConstantCompletion.derivedPull F V adj
    (ConstantCompletion.constantMap F (A ⧸ I ^ (n + 1)))).functor
  have hcancel : G.map (eJ.hom.app M) ≫ G.map (eJ.inv.app M) = 𝟙 _ := by
    rw [← G.map_comp, eJ.hom_inv_id_app]
    exact G.map_id _
  rw [he]
  change _ = _ ≫ G.map (eJ.hom.app M) ≫ G.map (eJ.inv.app M) ≫ _
  rw [← Category.assoc (G.map (eJ.hom.app M)), hcancel, Category.id_comp]
  exact Category.assoc _ _ _

private theorem derivedPull_computes {R : Sheaf J CommRingCat.{v}}
    {S : Sheaf K CommRingCat.{v}} (c : F.rings.obj R ⟶ S) [IsIso c]
    (P : ConstantCompletion.Cx R) :
    IsIso ((ConstantCompletion.derivedPull F V adj c).comparison.app P) := by
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod R)
  letI := HasDerivedCategory.standard (ConstantCompletion.Mod S)
  have : PreservesFiniteLimits (ConstantCompletion.pull F c) :=
    ConstantCompletion.pull_finiteLimits_of_isIso F c
  obtain ⟨G, eG, aM, haM⟩ := ConstantCompletion.module_adjunction_exists V adj F c
  have : PreservesFiniteColimits (ConstantCompletion.pull F c) := by
    have := aM.leftAdjoint_preservesColimits
    infer_instance
  let W := HomologicalComplex.quasiIso (ConstantCompletion.Mod R) (.up ℤ)
  let d := ConstantCompletion.derivedPull F V adj c
  have : d.functor.IsLeftDerivedFunctor d.comparison W := d.universal
  have hi : W.IsInvertedBy ((ConstantCompletion.pull F c).mapHomologicalComplex
      (.up ℤ) ⋙ ConstantCompletion.Q S) := by
    intro P P' f hf
    have : QuasiIso f := hf
    exact inferInstanceAs (IsIso (DerivedCategory.Q.map
      (((ConstantCompletion.pull F c).mapHomologicalComplex (.up ℤ)).map f)))
  have : IsIso d.comparison :=
    Functor.isIso_of_isLeftDerivedFunctor_of_inverts d.functor d.comparison hi
  exact NatIso.isIso_app_of_isIso d.comparison P

private theorem koszul_unit_criterion [IsNoetherianRing A] (r : ℕ) (a : Fin r → A)
    (ha : Ideal.span (Set.range a) = I)
    (P : ConstantCompletion.KoszulPresentation J A I true r a)
    (M : ConstantCompletion.D (ConstantCompletion.completed J A I)) :
    IsIso (ConstantCompletion.koszulUnit J A I P M) ↔
      ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) M := by
  obtain ⟨P₀, ⟨e₀, he₀⟩, _, _, hcrit⟩ :=
    ConstantCompletion.koszul_quotient_reflector J A I true r a ha
  letI := HasDerivedCategory.standard
    (ConstantCompletion.Mod (ConstantCompletion.completed J A I))
  letI := HasDerivedCategory.standard
    (ℕᵒᵖ ⥤ ConstantCompletion.Mod (ConstantCompletion.completed J A I))
  let O := ConstantCompletion.completed J A I
  let : Category.{v + 1} (ringedSiteDerived O) :=
    inferInstanceAs (Category.{v + 1} (ConstantCompletion.D O))
  let b := fun j ↦ ConstantCompletion.algebraSection
    (ConstantCompletion.baseMap J A I true) (a j)
  obtain ⟨e, he⟩ := exists_ringed_cech_koszul_hom_limit_comparison O r b P
  obtain ⟨e', he'⟩ := exists_ringed_cech_koszul_hom_limit_comparison O r b P₀
  have hunit : ConstantCompletion.koszulUnit J A I P M ≫
      (e.inv.app M ≫ e'.hom.app M ≫ e₀.hom.app M) =
        (ConstantCompletion.completionUnit J A I true).app M := by
    dsimp only [ConstantCompletion.koszulUnit]
    rw [← Category.assoc, ← he M]
    simp only [Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
    rw [← Category.assoc, he' M]
    exact he₀ M
  change IsIso (ConstantCompletion.koszulUnit J A I P M) ↔
    ConstantCompletion.IsComplete (ConstantCompletion.finiteMap J A I true 0) M
  rw [← hcrit M, ← hunit]
  exact (isIso_comp_right_iff _ _).symm

private theorem complete_of_unit_comparison [IsNoetherianRing A]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (PX : ConstantCompletion.KoszulPresentation J A I true r a)
    (PS : ConstantCompletion.KoszulPresentation K A I true r a)
    (e : ConstantCompletion.koszulCompletion J A I PX ⋙ completedPull F V adj A I ≅
      completedPull F V adj A I ⋙ ConstantCompletion.koszulCompletion K A I PS)
    (he : ∀ M, (completedPull F V adj A I).map
        (ConstantCompletion.koszulUnit J A I PX M) ≫ e.hom.app M =
      ConstantCompletion.koszulUnit K A I PS ((completedPull F V adj A I).obj M))
    (M : ConstantCompletion.D (ConstantCompletion.completed J A I))
    (hM : ConstantCompletion.IsComplete (ConstantCompletion.projection J A I 0) M) :
    ConstantCompletion.IsComplete (ConstantCompletion.projection K A I 0)
      ((completedPull F V adj A I).obj M) := by
  haveI := (koszul_unit_criterion A I r a ha PX M).mpr hM
  apply (koszul_unit_criterion A I r a ha PS _).mp
  rw [← he M]
  infer_instance

private theorem unitRestriction_of_exact [IsNoetherianRing A]
    [PreservesLimitsOfShape ℕᵒᵖ L] [PreservesLimitsOfShape (Discrete ℕ) L]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ConstantCompletion.Mod (ConstantCompletion.completed J A I))]
    [HasExactLimitsOfShape (Discrete ℕ)
      (ConstantCompletion.Mod (ConstantCompletion.completed K A I))]
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I) :
    UnitRestriction F V adj A I r a := by
  haveI := completedMap_isIso F A I
  have hK := ConstantCompletion.exactCompletedKoszulPullback F V adj A I r a
  refine ⟨inferInstance, derivedPull_computes F V adj _, hK,
    finiteComparison_normalized F V adj A I, ?_⟩
  obtain ⟨PX, _⟩ := ConstantCompletion.koszul_quotient_reflector J A I true r a ha
  obtain ⟨PS, _⟩ := ConstantCompletion.koszul_quotient_reflector K A I true r a ha
  obtain ⟨e, he⟩ := hK PX PS
  exact complete_of_unit_comparison F V adj A I r a ha PX PS e he

end Comparisons

section Strata

variable {X : Scheme.{u}} (s : FiniteLocallyClosedStratification X)
  (F : ∀ α : Fin s.n, ConstantCompletion.InverseImageData (inverse (s.immersion α)))
  (A : Type (u + 1)) [CommRing A] (I : Ideal A)

/-- Restriction along the actual immersion realizing one stratum. The finite-limit
structure comes from that immersion, so it is not an extra hypothesis on a stratum.
Source: Bhatt--Scholze, Lemma 6.5.8
(auxiliary; not a blueprint node). -/
def stratumPull (α : Fin s.n) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I) ⥤
      ConstantCompletion.D
        (ConstantCompletion.completed (proEtaleModelTopology (s.domain α)) A I) :=
  haveI := s.isImmersion α
  completedPull (F α) (direct (s.immersion α)) (adjunction (s.immersion α)) A I

/-- The composite of stratum inverse image and the actual localization at a site object,
with coefficient change given by the canonical finite-projection comparison.
Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication; Stacks Tag 00XZ
(auxiliary; not a blueprint node). -/
def stratumSlicePull (α : Fin s.n) (U : proEtaleSiteModel (s.domain α)) :
    ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I) ⥤
      ConstantCompletion.D
        (ConstantCompletion.completed ((proEtaleModelTopology (s.domain α)).over U) A I) :=
  stratumPull s F A I α ⋙
    completedPull (sliceAlgebra (proEtaleModelTopology (s.domain α)) U)
      (sliceDirect (proEtaleModelTopology (s.domain α)) U)
      (sliceAdjunction (proEtaleModelTopology (s.domain α)) U) A I

attribute [local irreducible] stratumPull stratumSlicePull

end Strata

/-- Immersion and slice restriction preserve the finite-projection completed coefficients,
the actual Koszul completion units, and local derived ideal completeness, without a
boundedness assumption. The auxiliary `finiteComparison` gives the normalized comparison
for every finite derived reduction.

Source: Bhatt--Scholze, Lemma 6.5.8(1),(2), Remark 6.5.10 and Proposition 6.6.11;
Stacks Project, proetale.tex, Tags 099L and 099M, algebraization.tex, Tag 0A0E
(auxiliary; not a blueprint node).

Proof, following steps 1--4 and the forward part of step 5 of the node:
1. Constant inverse-image comparisons identify every finite quotient and its transitions.
   Immersion inverse image preserves limits, by
   lem-weil-pbc-proetale-immersion-limit-preservation, so the limit lift formed from these
   projections is invertible. Its module inverse image is exact and preserves products.
2. Slice restriction is the recorded exact module overFunctor, with extension by zero
   as a left adjoint, by lem-pur-site-restriction-module-adjunction-exact. It preserves
   products and the quotient projections. Weakly-etale localization identifies its site
   with the covering scheme's site; lem-sfb-proetale-object-inverse-image-restriction
   identifies this restriction with the specified inverse image, also for ring sheaves.
3. The canonical ringed-topos tensor pullback comparison gives finiteComparison.
   Pull back a flat-term K-flat model and its finite-free Koszul tensor tower. The powers
   a_j^(m+1), the transitions (a_j,1), and the degree-zero augmentation all restrict to
   the corresponding strict maps. No perfectness of A/I^(m+1) over A is needed.
4. Exact countable products on each pro-etale site and slice allow the normalized strict
   Roos comparison (lem-weil-strict-roos-comparison). The additive comparison
   lem-pur-roos-additive-comparison identifies 1-shift on both product coordinates and
   takes the actual augmentation (gamma_m,0) to its restricted augmentation. This gives
   the displayed equality of the actual units, not just an isomorphism of their targets.
5. lem-weil-pbc-constant-completion-equivalence identifies local completeness with
   invertibility of these units. Their comparison therefore proves preservation.
-/
theorem adicStratumCompletionUnit (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I) :
    (∀ (S : Scheme.{u}) (i : S ⟶ X) [IsImmersion i]
        (F : ConstantCompletion.InverseImageData (inverse i)),
      UnitRestriction F (direct i) (adjunction i) A I r a) ∧
    (∀ (S : Scheme.{u}) (i : S ⟶ X) [IsImmersion i]
        (U : proEtaleSiteModel S),
      UnitRestriction (sliceAlgebra (proEtaleModelTopology S) U)
        (sliceDirect (proEtaleModelTopology S) U)
        (sliceAdjunction (proEtaleModelTopology S) U) A I r a) := by
  constructor
  · intro S i hi F
    have := inverse_limits i
    have := smallProducts_exact X
      (siteModuleRings (ConstantCompletion.completed (proEtaleModelTopology X) A I))
    have := smallProducts_exact S
      (siteModuleRings (ConstantCompletion.completed (proEtaleModelTopology S) A I))
    exact unitRestriction_of_exact F (direct i) (adjunction i) A I r a ha
  · intro S i hi U
    have : PreservesLimitsOfSize.{0, 0}
        ((proEtaleModelTopology S).overPullback (Type (u + 1)) U) := by infer_instance
    have := smallProducts_exact S
      (siteModuleRings (ConstantCompletion.completed (proEtaleModelTopology S) A I))
    have := sliceProducts_exact S U
      (siteModuleRings (ConstantCompletion.completed ((proEtaleModelTopology S).over U) A I))
    exact unitRestriction_of_exact (sliceAlgebra (proEtaleModelTopology S) U)
      (sliceDirect (proEtaleModelTopology S) U)
      (sliceAdjunction (proEtaleModelTopology S) U) A I r a ha

/-- Finite strata with chosen pro-etale covering sieves detect local derived completeness.
A covering family is represented by its generated covering sieve; testing its arrows
also tests every further pullback, so includes arbitrary chosen covering families.

Source: Bhatt--Scholze, Proposition 6.6.11, reverse implication, and Remark 6.5.10;
Stacks Project, proetale.tex, Tags 099L and 099M
(auxiliary; not a blueprint node).

Proof, step 5 of the node: apply adicStratumCompletionUnit to every stratum and then
its covering slices. By lem-weil-pbc-constant-completion-equivalence every restricted
unit is invertible exactly when the restricted object is locally complete. The module
underlying-sheaf comparisons identify these exact functors with the inverse images in
lem-weil-pbc-noetherian-stratum-detection; the object inverse-image/restriction theorem
identifies the covering localizations. Apply their joint conservativity to the unbounded
derived completion unit. Invertibility of that unit is local completeness on X. For the
forward implication use the already proved preservation clauses. Empty schemes and empty
strata use the empty-cover sheaf axiom; no nonemptiness hypothesis is introduced.
-/
theorem adicStratumCompletionUnit_detection (X : Scheme.{u}) [IsNoetherian X]
    (A : Type (u + 1)) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (r : ℕ) (a : Fin r → A) (ha : Ideal.span (Set.range a) = I)
    (s : FiniteLocallyClosedStratification X)
    (V : ∀ α : Fin s.n,
      Sieve ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (hV : ∀ α : Fin s.n, V α ∈ proEtaleModelTopology (s.domain α)
      ((AsSmall.up : (s.domain α).ProEt ⥤ proEtaleSiteModel (s.domain α)).obj
        (⊤_ (s.domain α).ProEt)))
    (F : ∀ α : Fin s.n, ConstantCompletion.InverseImageData (inverse (s.immersion α)))
    (M : ConstantCompletion.D (ConstantCompletion.completed (proEtaleModelTopology X) A I)) :
    ConstantCompletion.IsComplete
        (ConstantCompletion.projection (proEtaleModelTopology X) A I 0) M ↔
      ∀ (α : Fin s.n) (U : proEtaleSiteModel (s.domain α))
        (f : U ⟶ (AsSmall.up : (s.domain α).ProEt ⥤
          proEtaleSiteModel (s.domain α)).obj (⊤_ (s.domain α).ProEt)), V α f →
        ConstantCompletion.IsComplete
          (ConstantCompletion.projection ((proEtaleModelTopology (s.domain α)).over U) A I 0)
          ((stratumSlicePull s F A I α U).obj M) := by
  letI : ∀ α, IsImmersion (s.immersion α) := s.isImmersion
  have h := adicStratumCompletionUnit X A I r a ha
  have hS (α : Fin s.n) := h.1 (s.domain α) (s.immersion α) (F α)
  have hU (α : Fin s.n) (U : proEtaleSiteModel (s.domain α)) :=
    h.2 (s.domain α) (s.immersion α) U
  constructor
  · intro hM α U f hf
    change ConstantCompletion.IsComplete _
      ((completedPull (sliceAlgebra (proEtaleModelTopology (s.domain α)) U)
        (sliceDirect (proEtaleModelTopology (s.domain α)) U)
        (sliceAdjunction (proEtaleModelTopology (s.domain α)) U) A I).obj
          ((completedPull (F α) (direct (s.immersion α))
            (adjunction (s.immersion α)) A I).obj M))
    exact (hU α U).2.2.2.2 _ ((hS α).2.2.2.2 M hM)
  · intro hM
    obtain ⟨PX, _⟩ := ConstantCompletion.koszul_quotient_reflector
      (proEtaleModelTopology X) A I true r a ha
    apply (koszul_unit_criterion A I r a ha PX M).mp
    haveI : ∀ α, IsIso (ConstantCompletion.completedMap (F α) A I) :=
      fun α ↦ (hS α).1
    haveI : ∀ α U, IsIso (ConstantCompletion.completedMap
        (sliceAlgebra (proEtaleModelTopology (s.domain α)) U) A I) :=
      fun α U ↦ (hU α U).1
    apply adicStratumCoverConservativity X A I s V hV
      (fun α ↦ inverse (s.immersion α)) (fun α ↦ direct (s.immersion α))
      (fun α ↦ adjunction (s.immersion α)) (fun α ↦ by
        unfold inverse modelEquivalence
        exact ⟨Iso.refl _⟩) F
      (fun α U ↦ sliceAlgebra (proEtaleModelTopology (s.domain α)) U)
      (fun α U ↦ sliceDirect (proEtaleModelTopology (s.domain α)) U)
      (fun α U ↦ sliceAdjunction (proEtaleModelTopology (s.domain α)) U)
      M _ (ConstantCompletion.koszulUnit (proEtaleModelTopology X) A I PX M)
    intro α U f hf
    obtain ⟨PS, _⟩ := ConstantCompletion.koszul_quotient_reflector
      (proEtaleModelTopology (s.domain α)) A I true r a ha
    obtain ⟨PU, _⟩ := ConstantCompletion.koszul_quotient_reflector
      ((proEtaleModelTopology (s.domain α)).over U) A I true r a ha
    obtain ⟨eS, heS⟩ := (hS α).2.2.1 PX PS
    obtain ⟨eU, heU⟩ := (hU α U).2.2.1 PS PU
    let T := completedPull (F α) (direct (s.immersion α))
      (adjunction (s.immersion α)) A I
    let W := completedPull (sliceAlgebra (proEtaleModelTopology (s.domain α)) U)
      (sliceDirect (proEtaleModelTopology (s.domain α)) U)
      (sliceAdjunction (proEtaleModelTopology (s.domain α)) U) A I
    have ht : IsIso (ConstantCompletion.koszulUnit
        ((proEtaleModelTopology (s.domain α)).over U) A I PU (W.obj (T.obj M))) :=
      (koszul_unit_criterion A I r a ha PU _).mpr (hM α U f hf)
    have hu : IsIso (W.map (ConstantCompletion.koszulUnit
        (proEtaleModelTopology (s.domain α)) A I PS (T.obj M))) := by
      apply (isIso_comp_right_iff _ (eU.hom.app (T.obj M))).mp
      rw [heU]
      exact ht
    change IsIso (W.map (T.map
      (ConstantCompletion.koszulUnit (proEtaleModelTopology X) A I PX M)))
    apply (isIso_comp_right_iff _ (W.map (eS.hom.app M))).mp
    rw [← W.map_comp, heS M]
    exact hu

end AlgebraicGeometry.Scheme.SfbAdicRestriction

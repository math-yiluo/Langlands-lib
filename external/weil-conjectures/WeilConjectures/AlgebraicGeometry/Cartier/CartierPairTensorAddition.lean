/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Tensor.TensorPullbackFrames
public import WeilConjectures.AlgebraicGeometry.EffectiveCartier
public import WeilConjectures.AlgebraicGeometry.Sites.GmPicard
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeCocycleCoordinates
public import WeilConjectures.AlgebraicGeometry.CartierPoleBoundary
public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
public import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorCohomology
public import WeilConjectures.CategoryTheory.Sites.RelativeTorsorExtension
public import WeilConjectures.CategoryTheory.Sites.TorsorExtensionPresentation
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasSheafify
public import WeilConjectures.CategoryTheory.Sites.Torsor
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.CategoryTheory.Abelian.Exact
public import WeilConjectures.CategoryTheory.Sites.EtaleTorsorExtensionPresentationExists
public import WeilConjectures.CategoryTheory.Sites.ExtensionPresentationShortExact
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass
public import WeilConjectures.CategoryTheory.YonedaExtension.YonedaExtensionData
public import Mathlib.CategoryTheory.Abelian.Basic
public import Mathlib.Algebra.Homology.ExactSequence
public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorBilinearUniversal
import WeilConjectures.AlgebraicGeometry.Modules.IdealSheafFiniteType
import WeilConjectures.AlgebraicGeometry.Modules.TensorSection
import WeilConjectures.AlgebraicGeometry.EffectiveCartierSum
import WeilConjectures.Mathlib.CategoryTheory.Monoidal.Closed.Braided
import WeilConjectures.AlgebraicGeometry.Relative.RelativeExtensionCohomologyNormalization
import WeilConjectures.AlgebraicGeometry.Relative.RelativeTorsorAddition
import WeilConjectures.CategoryTheory.Sites.SmoothPurity.BinaryTorsorQuotient
import all WeilConjectures.AlgebraicGeometry.CartierComplementFrame
import all WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerBoundarySupplement
import all WeilConjectures.AlgebraicGeometry.Modules.SectionAvoidance
import all WeilConjectures.AlgebraicGeometry.InternalHomRestrictScheme
import Mathlib.Algebra.Homology.HomologySequenceLemmas

/-! # Tensor addition of framed Cartier pairs

Source: Stacks Project, Tags 01WT, 01WU, 03AJ, 010L, 0117 and 0G78;
blueprint main-20261015, lemma-cycle-class-cartier-divisor, clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition)

The geometric, framed-torsor, relative-class, extension-class and naturality clauses
are recorded separately. Restriction uses the actual shifted cone, and the relative
class is minus the raw lifting class, as required by the Ext normalization.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian MonoidalCategory Opposite
open scoped AlgebraicGeometry.Scheme.Modules

namespace AlgebraicGeometry.Etale

local instance : MorphismProperty.ContainsIdentities
    (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}) :=
  AlgebraicGeometry.Etale.instIsMultiplicativeScheme.toContainsIdentities

/-- The existing frame torsor of the dual Cartier ideal, with its canonical invertibility
instances supplied by the recorded divisor-line-bundle theorem.
Source: Stacks 03AJ and blueprint divisor-class clause (b).
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairFrameTorsor {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible) :
    Sheaf.Torsor T.gmSheaf :=
  letI := hI.isInvertible_dual_toModules
  letI := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
    (Scheme.Modules.dual i.ker.toModules)
  Scheme.Modules.etaleIsoTorsor (Scheme.Modules.dual i.ker.toModules)

/-- The underlying ordinary-pullback frame, using the recorded frame-torsor API.
Source: Stacks 03AJ, frames of O(D).
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairFrameVal {D T : Scheme.{u}} (i : D ⟶ T) (hI : i.ker.IsInvertible)
    {U : T.Etaleᵒᵖ} (x : (cartierPairFrameTorsor i hI).sheaf.obj.obj U) :
    (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.unit T) ⟶
      (Scheme.Modules.pullback U.unop.hom).obj (Scheme.Modules.dual i.ker.toModules) :=
  x.down.1

/-- Inclusion of one open in another as an object of the small etale site.
Source: Stacks 0G78, restriction of the open term.
(blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairOpenInclusion {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V) :
    Scheme.Etale.mk W.ι ⟶ Scheme.Etale.mk V.ι :=
  MorphismProperty.Over.homMk (T.homOfLE h) (T.homOfLE_ι h)

/-- The identity on global sections and restriction on open sections form a commuting
square. Source: Stacks 0G78, signed-cone refinement.
(blueprint: lem-pur-cartier-pair-tensor-addition).
Proof: restriction from the terminal object factors through V; functoriality of
sections gives the equality degreewise, and extension by zero preserves it. -/
theorem cartierPairRestriction_square {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    (𝟙 (relativeSections (Scheme.Etale.mk (𝟙 T)) I)) ≫
        relativeSectionRestriction T (Scheme.Etale.mk W.ι) I =
      relativeSectionRestriction T (Scheme.Etale.mk V.ι) I ≫
        HomologicalComplex.extendMap (etaleSectionMap (cartierPairOpenInclusion h) I)
          ComplexShape.embeddingUpNat := by
  rw [Category.id_comp]
  dsimp only [relativeSectionRestriction]
  rw [← HomologicalComplex.extendMap_comp]
  congr 1
  apply HomologicalComplex.hom_ext
  intro n
  change (I.X n).obj.map _ = (I.X n).obj.map _ ≫ (I.X n).obj.map _
  rw [← Functor.map_comp]
  congr 1
  apply Quiver.Hom.unop_inj
  exact (MorphismProperty.Over.mkIdTerminal @Etale T).hom_ext _ _

/-- Enlargement of support in the actual signed shifted-cone model. Its coordinates
are (x,y) to (x,y restricted to W), so there is no independently chosen sign.
Source: Stacks 0G78 (blueprint: lem-pur-cartier-pair-tensor-addition). -/
def cartierPairRestriction {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : CochainComplex (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) ℕ) :
    relativeSectionComplex T (Scheme.Etale.mk V.ι) I ⟶
      relativeSectionComplex T (Scheme.Etale.mk W.ι) I :=
  relativeFiberMap (relativeSectionRestriction T (Scheme.Etale.mk V.ι) I)
    (relativeSectionRestriction T (Scheme.Etale.mk W.ι) I) (𝟙 _)
    (HomologicalComplex.extendMap (etaleSectionMap (cartierPairOpenInclusion h) I)
      ComplexShape.embeddingUpNat) (cartierPairRestriction_square h I)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma dual_evaluation_tmul {X : Scheme.{u}} (A : X.Modules) (U : X.Opens)
    (s : Γ(A, U)) (f : Γ(Aᵛ, U)) :
    (Scheme.Modules.dualEvaluation A).app U (Scheme.Modules.tmulSection s f) =
      f.app (op (Over.mk (𝟙 U))) s := by
  let adj := PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)
  let q := (adj.homEquiv _ (Scheme.Modules.unit X)).symm
    (Scheme.Modules.presheafDualEvaluation A)
  have hh := (adj.homEquiv _ (Scheme.Modules.unit X)).apply_symm_apply
    (Scheme.Modules.presheafDualEvaluation A)
  rw [Adjunction.homEquiv_unit] at hh
  have he := congrArg (fun t ↦ t.app (op U) (s ⊗ₜ[Γ(X, U)] f)) hh
  change Scheme.Modules.Hom.app q U ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U)
    (s ⊗ₜ[Γ(X, U)] f)) = _ at he
  change Scheme.Modules.Hom.app q U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).hom U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv U
      ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U)
        (s ⊗ₜ[Γ(X, U)] f)))) = _
  have hi := congrArg (fun t ↦ Scheme.Modules.Hom.app t U
    ((Scheme.Modules.toSheafifyTensor A Aᵛ).app (op U) (s ⊗ₜ[Γ(X, U)] f)))
    (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv_hom_id
  change Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).hom U
    (Scheme.Modules.Hom.app (SheafOfModules.tensorObjIsoSheafification A Aᵛ).inv U _) = _ at hi
  rw [hi]
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private lemma divisor_section_evaluation {D X : Scheme.{u}} (i : D ⟶ X) :
    i.ker.toModules ◁ supportedDivisorSection i ≫
      Scheme.Modules.dualEvaluation i.ker.toModules =
        (ρ_ i.ker.toModules).hom ≫ i.ker.toModulesι := by
  apply (cancel_epi (ρ_ i.ker.toModules).inv).1
  rw [Iso.inv_hom_id_assoc]
  apply Scheme.Modules.hom_ext
  intro U
  ext x
  change (Scheme.Modules.dualEvaluation i.ker.toModules).app U
    ((i.ker.toModules ◁ supportedDivisorSection i).app U
      ((ρ_ i.ker.toModules).inv.app U x)) = _
  rw [Scheme.Modules.rightUnitor_inv_app, Scheme.Modules.whiskerLeft_app_tmulSection,
    dual_evaluation_tmul]
  have hs := (SheafOfModules.unitHomEquiv _).apply_symm_apply
    ((SheafOfModules.homObjSectionsEquiv i.ker.toModules (Scheme.Modules.unit X)).symm
      i.ker.toModulesι)
  have he := congrArg (fun z ↦ (z.val (op U)).app (op (Over.mk (𝟙 U))) x) hs
  exact he

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
section
attribute [local irreducible] supportedDivisorSection Scheme.Modules.dualEvaluation
  Scheme.IdealSheafData.toModules

end

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency false in

set_option backward.isDefEq.respectTransparency false in
-- The cone-coordinate conversion traverses the injective-resolution representation.
private theorem pair_restrict {T : Scheme.{u}} {W V : T.Opens} (h : W ≤ V)
    (I : InjectiveResolution T.gmSheaf) (P : Sheaf.Torsor T.gmSheaf)
    (τ : P.sheaf.obj.obj (op (Scheme.Etale.mk V.ι))) :
    HomologicalComplex.homologyMap (cartierPairRestriction h I.cocomplex) 1
      (relativeTorsorEquiv T (Scheme.Etale.mk V.ι) I (Quotient.mk _ ⟨P, τ⟩)) =
    relativeTorsorEquiv T (Scheme.Etale.mk W.ι) I
      (Quotient.mk _ ⟨P, P.sheaf.obj.map (cartierPairOpenInclusion h).op τ⟩) := by
  let hT := MorphismProperty.Over.mkIdTerminal @Etale T
  let : Injective (I.cocomplex.X 0) := I.injective 0
  obtain ⟨s, ⟨e⟩⟩ := Sheaf.Torsor.exists_equiv_lifts hT
    (resolutionLiftSequence_shortExact T I) P
  rw [relativeTorsorEquiv_presentation T (Scheme.Etale.mk V.ι) I ⟨P, τ⟩ s e,
    relativeTorsorEquiv_presentation T (Scheme.Etale.mk W.ι) I
      ⟨P, P.sheaf.obj.map (cartierPairOpenInclusion h).op τ⟩ s e]
  let z : ResolutionFramedLift T (Scheme.Etale.mk V.ι) I :=
    ⟨s, e.iso.hom.hom.app _ τ⟩
  let z' : ResolutionFramedLift T (Scheme.Etale.mk W.ι) I :=
    ⟨s, e.iso.hom.hom.app _ (P.sheaf.obj.map (cartierPairOpenInclusion h).op τ)⟩
  have hsq : HomologicalComplex.extendMap
      (𝟙 (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
        (.up ℕ)).obj I.cocomplex)) ComplexShape.embeddingUpNat ≫
        relativeSectionRestriction T (Scheme.Etale.mk W.ι) I.cocomplex =
      relativeSectionRestriction T (Scheme.Etale.mk V.ι) I.cocomplex ≫
        HomologicalComplex.extendMap
          (etaleSectionMap (cartierPairOpenInclusion h) I.cocomplex)
          ComplexShape.embeddingUpNat := by
    rw [HomologicalComplex.extendMap_id]
    exact cartierPairRestriction_square h I.cocomplex
  let α : (((etaleSectionFunctor (Scheme.Etale.mk (𝟙 T))).mapHomologicalComplex
      (.up ℕ)).obj I.cocomplex) ⟶ _ := 𝟙 _
  have hd : (I.cocomplex.d 0 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) 0 =
      (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z'.1 -
        (show (I.cocomplex.X 1).obj.obj (op (Scheme.Etale.mk (𝟙 T))) from
          α.f 1 ((I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) z.1)) := by
    change _ = _ - (I.cocomplex.iCycles 1).hom.app (op (Scheme.Etale.mk (𝟙 T))) s
    rw [map_zero, sub_self]
  have hr : (I.cocomplex.X 0).obj.map
      ((MorphismProperty.Over.mkIdTerminal @Etale T).from (Scheme.Etale.mk W.ι)).op 0 =
      (show (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)) from z'.2.1) -
        (show (I.cocomplex.X 0).obj.obj (op (Scheme.Etale.mk W.ι)) from
          (etaleSectionMap (cartierPairOpenInclusion h) I.cocomplex).f 0 z.2.1) := by
    rw [map_zero, eq_comm, sub_eq_zero]
    exact congrArg Subtype.val (ConcreteCategory.congr_hom
      (e.iso.hom.hom.naturality (cartierPairOpenInclusion h).op) τ)
  have hh := relativeFrameClass_map_eq T (Scheme.Etale.mk V.ι) I
    (Scheme.Etale.mk W.ι) I _ _ hsq z z' 0 hd hr
  simp only [HomologicalComplex.extendMap_id] at hh
  unfold cartierPairRestriction relativeSections
  exact hh

section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal

-- Explicit frame and pseudofunctor comparisons require additional elaboration.
end

private lemma supported_one_restrict {D T : Scheme.{u}} (i : D ⟶ T)
    (U : T.Etaleᵒᵖ) :
    ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)).obj.map
        ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
        ((supportedIntegralUnit i).hom.app (op (Scheme.Etale.mk (𝟙 T)))
          (supportedIntegralOne T)) =
      (supportedIntegralUnit i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩) := by
  let v := ((MorphismProperty.Over.mkIdTerminal @Etale T).from U.unop).op
  have hq := ConcreteCategory.congr_hom ((supportedIntegralUnit i).hom.naturality v)
    (supportedIntegralOne T)
  have h1 := ConcreteCategory.congr_hom
    ((toSheafify T.smallEtaleTopology
      ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).naturality v)
    (ULift.up 1)
  simp only [ConcreteCategory.comp_apply, Functor.const_obj_map] at hq h1
  exact hq.symm.trans (congrArg ((supportedIntegralUnit i).hom.app U) h1.symm)

set_option backward.isDefEq.respectTransparency false in
private lemma relativeExtension_eq_of_represents {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (β : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D)) G 1)
    (hβ : RelativeExtensionRepresents i P β) : β = relativeExtension i P :=
  (Classical.choose_spec (relativeExtension_existsUnique i P)).2 β hβ

section

private local instance cartierPairForgottenSectionsHAdd {T : Scheme.{u}}
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (U : T.Etaleᵒᵖ) :
    HAdd ((E.obj ⋙ forget AddCommGrpCat.{u + 1}).obj U) (E.obj.obj U) (E.obj.obj U) :=
  inferInstanceAs (HAdd (E.obj.obj U) (E.obj.obj U) (E.obj.obj U))

private theorem relativeExtensionRepresents_mk {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] {G : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (P : Sheaf.Torsor.WithSection G (Scheme.Etale.mk i.openComplement.ι))
    (E : Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) (a : G ⟶ E)
    (b : E ⟶ (lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
    (hab : a ≫ b = 0) (hE : (ShortComplex.mk a b hab).ShortExact)
    (f : P.1.sheaf.obj ⟶ E.obj ⋙ forget AddCommGrpCat.{u + 1})
    (ha : ∀ (U : T.Etaleᵒᵖ) g t,
      @id (E.obj.obj U) (f.app U (P.1.vadd U g t)) = f.app U t + a.hom.app U g)
    (hb : ∀ (U : T.Etaleᵒᵖ) t,
      b.hom.app U (f.app U t) = (supportedIntegralUnit i).hom.app U
        ((toSheafify T.smallEtaleTopology
          ((Functor.const T.Etaleᵒᵖ).obj (AddCommGrpCat.of (ULift.{u + 1} ℤ)))).app U ⟨1⟩))
    (hτ : @id (E.obj.obj (op (Scheme.Etale.mk i.openComplement.ι)))
      (f.app _ P.2) = 0) :
    RelativeExtensionRepresents i P hE.extClass := by
  exact ⟨E, a, b, hab, hE, f, ha, hb, hτ, rfl⟩

end

set_option backward.isDefEq.respectTransparency false in
private lemma pole_boundary_eq_relative {D T : Scheme.{u}} (i : D ⟶ T)
    [IsClosedImmersion i] (hI : i.ker.IsInvertible)
    (τ : (cartierPairFrameTorsor i hI).sheaf.obj.obj
      (op (Scheme.Etale.mk i.openComplement.ι)))
    (hτ : cartierPairFrameVal i hI τ = supportedDivisorSectionPullback i i.openComplement)
    (β : Ext ((lowerStar AddCommGrpCat.{u + 1} i).obj (supportedIntegralConstant D))
      T.gmSheaf 1) (hβ : CartierPoleBoundarySpec i hI β) :
    β = relativeExtension i ⟨cartierPairFrameTorsor i hI, τ⟩ := by
  obtain ⟨τ', E, a, b, hab, hE, f, hτ', hfa, hfb, hfτ, hext⟩ :=
    (by unfold CartierPoleBoundarySpec at hβ; exact hβ i.openComplement rfl)
  have hframe : τ' = τ := by
    have := hI.isInvertible_dual_toModules
    have := Scheme.Modules.IsInvertible.sheafOfModules_isInvertible
      (Scheme.Modules.dual i.ker.toModules)
    apply Scheme.Modules.etaleIsoTorsorVal_injective (Scheme.Modules.dual i.ker.toModules)
    exact hτ'.trans hτ.symm
  apply relativeExtension_eq_of_represents
  rw [hext]
  apply relativeExtensionRepresents_mk i ⟨cartierPairFrameTorsor i hI, τ⟩
    E a b hab hE f.hom
  · intro U g t
    exact (hfa U g t).trans (add_comm _ _)
  · intro U t
    exact (hfb U t).trans (supported_one_restrict i U)
  · rw [← hframe]
    exact hfτ

section
attribute [local irreducible] cartierPairFrameTorsor cartierPairFrameVal

end

end AlgebraicGeometry.Etale

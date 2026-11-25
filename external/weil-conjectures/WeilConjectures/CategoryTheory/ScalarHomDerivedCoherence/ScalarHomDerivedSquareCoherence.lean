/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Scalar.ScalarInternalHomDataSupplement
public import WeilConjectures.SmoothPurity.Supporting.CoefDerivedSystemEvaluationCalculus
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomTensorCoherence
import all WeilConjectures.CategoryTheory.Scalar.ScalarHomComparisonTower
import Mathlib.CategoryTheory.Limits.HasLimits

/-! # Flat scalar evaluation on an arbitrary first complex

Source: Stacks Project, sites-cohomology.tex, Tags 07A4, 08J9 and 06YP;
the one-K-flat-factor scalar evaluation refinement recorded in the DAG, rather
than a verbatim assertion of these tags
(blueprint: lem-sfb-scalar-hom-derived-square-coherence).

All tensors, Hom products, sections and localization functors below are the
recorded constructions. The data asserted to exist are fixed by generator
formulas and the K-flat normalization; no representative is chosen arbitrarily.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option maxErrors 4
-- Avoid re-synthesizing the site-universe instances in the section-variable linter.
set_option linter.unusedSectionVars false
set_option linter.unusedTactic false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward false
universe c v r w
open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules WeilConjectures

attribute [local irreducible] CategoryTheory.Preadditive.preadditiveHasZeroMorphisms

attribute [local irreducible] derivedInternalHomOfUniverses
  CoefficientClosedStructure.tensor coefficientBaseChangeHom
  Functor.mapHomologicalComplexUpToQuasiIso Functor.mapHomologicalComplexUpToQuasiIsoFactors


attribute [local irreducible] coefficientTotalTensor coefficientTensorGenerator
  scalarPairComplexComparison CoefficientTensorModels.iso
  SheafOfModules.monoidalCategory homComplexFunctor

namespace CategoryTheory
private theorem conjugate_square
    {A : Type*} [Category A] (H : Aᵒᵖ × A ⥤ A)
    {X0 X1 Y0 Y1 Z0 Z1 W0 W1 SX SY CX CY : A}
    (u0 : X0 ≅ Z0) (u1 : X1 ≅ Z1) (v0 : Y0 ≅ W0) (v1 : Y1 ≅ W1)
    (e0 : Z0 ≅ W0) (e1 : Z1 ≅ W1)
    (u : SX ≅ CX) (v : SY ≅ CY) (e : CX ≅ CY)
    (f : SX ⟶ H.obj (op X0, X1)) (g : SY ⟶ H.obj (op Y0, Y1))
    (c : CX ⟶ H.obj (op Z0, Z1)) (d : CY ⟶ H.obj (op W0, W1))
    (hf : f ≫ H.map (Prod.mkHom u0.inv.op u1.hom) = u.hom ≫ c)
    (hg : g ≫ H.map (Prod.mkHom v0.inv.op v1.hom) = v.hom ≫ d)
    (he : c ≫ H.map (Prod.mkHom e0.inv.op e1.hom) = e.hom ≫ d) :
    f ≫ H.map (Prod.mkHom (v0.hom ≫ e0.inv ≫ u0.inv).op
        (u1.hom ≫ e1.hom ≫ v1.inv)) = u.hom ≫ e.hom ≫ v.inv ≫ g := by
  have : IsIso (Prod.mkHom v0.inv.op v1.hom) :=
    inferInstanceAs (IsIso ((v0.symm.op.prod v1).hom))
  have : IsIso (H.map (Prod.mkHom v0.inv.op v1.hom)) :=
    Functor.map_isIso _ _
  apply (cancel_mono (H.map (Prod.mkHom v0.inv.op v1.hom))).mp
  simp only [Category.assoc, ← H.map_comp]
  have hp : Prod.mkHom (v0.hom ≫ e0.inv ≫ u0.inv).op
      (u1.hom ≫ e1.hom ≫ v1.inv) ≫ Prod.mkHom v0.inv.op v1.hom =
      Prod.mkHom u0.inv.op u1.hom ≫ Prod.mkHom e0.inv.op e1.hom := by
    apply Prod.ext <;> simp [Category.assoc, ← op_comp]
  rw [hp, H.map_comp, ← Category.assoc, hf]
  simp only [Category.assoc]
  rw [he, hg]
  simp only [Iso.inv_hom_id_assoc]


end CategoryTheory
namespace CategoryTheory.ScalarHomDerivedCoherence

variable {C : Type c} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{max c v r} RingCat.{max c v r})]
  [HasSheafify J AddCommGrpCat.{max c v r}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max c v r}]
  [∀ R : Sheaf J CommRingCat.{max c v r}, HasDerivedCategory.{w} (scalarModules J R)]
  (M : ScalarHomModels.{c, v, r, w} J)
  (μ : ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S),
    ScalarHomTensorComparison.{c, v, r, w} (J := J) M a)

def squareTransport {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ d = a ≫ φ') :
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) φ).derived ⋙ ((ScalarHomModels.scalar.{c, v,
      r, w} (J := J) M) d).derived ≅
      ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived ⋙ ((ScalarHomModels.scalar.{c,
        v, r, w} (J := J) M) φ').derived :=
  scalarHomExtensionComp.{c, v, r, w} (J := J) M φ d ≪≫
    eqToIso (congrArg (fun z ↦ ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) z).derived) h) ≪≫
    (scalarHomExtensionComp.{c, v, r, w} (J := J) M a φ').symm

/-- DerivedCoherence clause `naturality`, with its displayed formula unchanged. -/
def DerivedCoherenceNaturality : Prop :=
  ∀ {R S : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S)
    (K L K' L' : DerivedCategory (scalarModules J R)) (f : K' ⟶ K) (g : L ⟶ L'),
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).map (Prod.mkHom f.op g)) ≫
        coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) a).derived
          (μ a).iso K' L' =
      coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
        ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v, r, w}
        (J := J) M) a).derived
          (μ a).iso K L ≫
        (derivedInternalHomOfUniverses.{c, v, r, w} J S).map
          (Prod.mkHom (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map f).op
            (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.map g))

/-- DerivedCoherence clause `composition`, with its displayed formula unchanged. -/
def DerivedCoherenceComposition : Prop :=
  ∀ {R S T : Sheaf J CommRingCat.{max c v r}} (a : R ⟶ S) (b : S ⟶ T)
    (K L : DerivedCategory (scalarModules J R)),
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) b).derived.map
        (coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) a).derived
          (μ a).iso K L) ≫
      coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S)
        ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) T) ((ScalarHomModels.scalar.{c, v, r, w}
        (J := J) M) b).derived
        (μ b).iso (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj K)
          (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj L) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J T).map
        (Prod.mkHom ((scalarHomExtensionComp.{c, v, r, w} (J := J) M a b).inv.app K).op
          ((scalarHomExtensionComp.{c, v, r, w} (J := J) M a b).hom.app L)) =
      (scalarHomExtensionComp.{c, v, r, w} (J := J) M a b).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) T) ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) (a ≫ b)).derived
          (μ (a ≫ b)).iso K L

/-- DerivedCoherence clause `identity`, with its displayed formula unchanged. -/
def DerivedCoherenceIdentity : Prop :=
  ∀ (R : Sheaf J CommRingCat.{max c v r})
    (K L : DerivedCategory (scalarModules J R)),
    coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
      ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R) ((ScalarHomModels.scalar.{c, v, r, w}
      (J := J) M) (𝟙 R)).derived
        (μ (𝟙 R)).iso K L ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J R).map
        (Prod.mkHom ((scalarHomExtensionId.{c, v, r, w} (J := J) M R).inv.app K).op
          ((scalarHomExtensionId.{c, v, r, w} (J := J) M R).hom.app L)) =
      (scalarHomExtensionId.{c, v, r, w} (J := J) M R).hom.app
        ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L))

/-- DerivedCoherence clause `derived_square`, with its displayed formula unchanged. -/
def DerivedCoherenceDerivedSquare : Prop :=
  ∀ {R S R' S' : Sheaf J CommRingCat.{max c v r}}
    (φ : R ⟶ S) (a : R ⟶ R') (d : S ⟶ S') (φ' : R' ⟶ S')
    (h : φ ≫ d = a ≫ φ') (K L : DerivedCategory (scalarModules J R)),
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) d).derived.map
        (coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S) ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) φ).derived
          (μ φ).iso K L) ≫
      coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S)
        ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S') ((ScalarHomModels.scalar.{c, v, r,
        w} (J := J) M) d).derived
        (μ d).iso (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) φ).derived.obj K)
          (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) φ).derived.obj L) ≫
      (derivedInternalHomOfUniverses.{c, v, r, w} J S').map
        (Prod.mkHom ((squareTransport.{c, v, r, w} (J := J) M φ a d φ' h).inv.app K).op
          ((squareTransport.{c, v, r, w} (J := J) M φ a d φ' h).hom.app L)) =
      (squareTransport.{c, v, r, w} (J := J) M φ a d φ' h).hom.app
          ((derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)) ≫
        ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) φ').derived.map
          (coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
            ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R') ((ScalarHomModels.scalar.{c, v,
            r, w} (J := J) M) a).derived
            (μ a).iso K L) ≫
        coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R')
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S') ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) φ').derived
          (μ φ').iso (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj K)
            (((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) a).derived.obj L)


/-- Generic storage for the four coefficient coherence equations.
Source: this module (blueprint: lem-sfb-scalar-hom-derived-square-coherence). -/
structure CoherencePackage (Natural Composition Identity Square : Prop) : Prop where
  naturality : Natural
  composition : Composition
  identity : Identity
  derived_square : Square

/-- Exactly the displayed naturality, composition, identity and square equations.
Source: Stacks 07A4, 0D6D (blueprint: lem-sfb-scalar-hom-derived-square-coherence). -/
abbrev DerivedCoherence :=
  CoherencePackage (DerivedCoherenceNaturality.{c, v, r, w} (J := J) M μ)
    (DerivedCoherenceComposition.{c, v, r, w} (J := J) M μ)
    (DerivedCoherenceIdentity.{c, v, r, w} (J := J) M μ) (DerivedCoherenceDerivedSquare.{c, v, r,
      w} (J := J) M μ)


/-- Derived scalar-Hom comparison is natural and coherent for composition, identities
and coefficient squares on arbitrary derived inputs.
Source: Stacks 07A4, 08J9, 0D6D
(blueprint: lem-sfb-scalar-hom-derived-square-coherence).

Proof: the normalized scalar tensor coherence supplies the unit and composition
equations, and the scalar-Hom comparison tower transfers these through the
closed adjunction. For a commuting coefficient square, the direct composite
comparisons agree after transport along equality of the coefficient maps.
Conjugate both composition equations by their source and target composition
isomorphisms. Functoriality of Hom and cancellation of the inverse isomorphisms
identify the two square routes. These are equations for all derived morphisms,
so inverse quasi-isomorphisms are included. -/
theorem coherence : DerivedCoherence.{c, v, r, w} (J := J) M μ := by
  obtain ⟨ht, hid⟩ := scalarHomTensorCoherence (J := J) M μ
  obtain ⟨hn, hc, hi⟩ := scalarHomComparisonTower (J := J) M μ ht hid
  refine ⟨hn, hc, hi, ?_⟩
  intro R S R' S' φ a d φ' h K L
  let H := derivedInternalHomOfUniverses.{c, v, r, w} J S'
  let H0 := (derivedInternalHomOfUniverses.{c, v, r, w} J R).obj (op K, L)
  let u := scalarHomExtensionComp.{c, v, r, w} (J := J) M φ d
  let v := scalarHomExtensionComp.{c, v, r, w} (J := J) M a φ'
  let e : ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) (φ ≫ d)).derived ≅
    ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) (a ≫ φ')).derived :=
    eqToIso (congrArg (fun z ↦ ((ScalarHomModels.scalar.{c, v, r, w} (J := J) M) z).derived) h)
  have he :
      coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
        ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S') ((ScalarHomModels.scalar.{c, v, r,
        w} (J := J) M) (φ ≫ d)).derived
          (μ (φ ≫ d)).iso K L ≫
        H.map (Prod.mkHom (e.inv.app K).op (e.hom.app L)) =
      e.hom.app H0 ≫
        coefficientBaseChangeHom ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) R)
          ((ScalarHomModels.closed.{c, v, r, w} (J := J) M) S') ((ScalarHomModels.scalar.{c, v, r,
          w} (J := J) M) (a ≫ φ')).derived
          (μ (a ≫ φ')).iso K L := by
    dsimp only [e]
    generalize hz : φ ≫ d = z at h ⊢
    generalize hz' : a ≫ φ' = z' at h ⊢
    cases h
    simp [H]
  have h1 := hc φ d K L
  have h2 := hc a φ' K L
  rw [← Category.assoc] at h1 h2
  change _ ≫ H.map (Prod.mkHom (u.inv.app K).op (u.hom.app L)) =
    u.hom.app H0 ≫ _ at h1
  change _ ≫ H.map (Prod.mkHom (v.inv.app K).op (v.hom.app L)) =
    v.hom.app H0 ≫ _ at h2
  have hs := conjugate_square H (u.app K) (u.app L) (v.app K) (v.app L)
    (e.app K) (e.app L) (u.app H0) (v.app H0) (e.app H0) _ _ _ _ h1 h2 he
  simpa only [squareTransport, u, v, e, Iso.trans_hom, Iso.trans_inv,
    Iso.symm_hom, Iso.symm_inv, Iso.app_hom, Iso.app_inv, NatTrans.comp_app,
    Functor.comp_obj, H, H0, Category.assoc] using hs


end CategoryTheory.ScalarHomDerivedCoherence

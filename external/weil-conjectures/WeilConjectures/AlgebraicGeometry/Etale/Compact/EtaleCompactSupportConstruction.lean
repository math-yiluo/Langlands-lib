/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleSystemInterfaces
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleOpenExtension
import WeilConjectures.AlgebraicGeometry.Strict.Etale.StrictEtaleImageRestrictionConstruction
import WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemOrdinaryImages
import all WeilConjectures.Algebra.Homology.Coefficient.CoefficientSystemUnboundedComparison
import WeilConjectures.CategoryTheory.Derived.DerivedMateComparison
import Mathlib.CategoryTheory.Localization.Adjunction
import Mathlib.CategoryTheory.Sites.Pullback
import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Types

/-! # Coherent extension by zero on strict étale coefficient systems

Source: Stacks 03S2, 03DI and 03DJ; Zheng, Constructions 4.1 and 5.15.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genSizeOfSpec false
set_option genInjectivity false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u
open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor SheafOfModules
namespace AlgebraicGeometry

attribute [local irreducible] coefficientQuotientSheaf coefficientQuotientMap
  Functor.mapDerivedCategory Functor.mapDerivedCategoryFactors

section ExactAdjunction
universe a av b bv d
variable {A : Type a} [Category.{av} A] [Abelian A] [HasDerivedCategory.{d} A]
  {B : Type b} [Category.{bv} B] [Abelian B] [HasDerivedCategory.{d} B]

private theorem localizeOpenAdjunction
    (F : A ⥤ B) (G : B ⥤ A) [F.Additive] [G.Additive] (adj : F ⊣ G)
    (FD : DerivedCategory A ⥤ DerivedCategory B)
    (GD : DerivedCategory B ⥤ DerivedCategory A)
    (φ : DerivedCategory.Q ⋙ FD ≅ F.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q)
    (ψ : DerivedCategory.Q ⋙ GD ≅ G.mapHomologicalComplex (.up ℤ) ⋙ DerivedCategory.Q) :
    ∃ ad : FD ⊣ GD, ∀ P K (f : (F.mapHomologicalComplex (.up ℤ)).obj P ⟶ K),
      ad.homEquiv (DerivedCategory.Q.obj P) (DerivedCategory.Q.obj K)
        (φ.hom.app P ≫ DerivedCategory.Q.map f) =
      DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).homEquiv P K f) ≫
        ψ.inv.app K := by
  let : CatCommSq (F.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q FD := ⟨φ.symm⟩
  let : CatCommSq (G.mapHomologicalComplex (.up ℤ)) DerivedCategory.Q
      DerivedCategory.Q GD := ⟨ψ.symm⟩
  let ad := (adj.mapHomologicalComplex (.up ℤ)).localization DerivedCategory.Q
    (HomologicalComplex.quasiIso A (.up ℤ)) DerivedCategory.Q
    (HomologicalComplex.quasiIso B (.up ℤ)) FD GD
  refine ⟨ad, ?_⟩
  intro P K f
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc]
  rw [show ad.unit.app (DerivedCategory.Q.obj P) =
    DerivedCategory.Q.map ((adj.mapHomologicalComplex (.up ℤ)).unit.app P) ≫
      ψ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫ GD.map (φ.inv.app P) from
        Adjunction.localization_unit_app _ _ _ _ _ _ _ P]
  simp only [Category.assoc, ← GD.map_comp, Iso.inv_hom_id_app]
  erw [Category.id_comp]
  have hn := ψ.inv.naturality f
  change DerivedCategory.Q.map ((G.mapHomologicalComplex (.up ℤ)).map f) ≫ ψ.inv.app K =
    ψ.inv.app ((F.mapHomologicalComplex (.up ℤ)).obj P) ≫
      GD.map (DerivedCategory.Q.map f) at hn
  rw [← hn, ← Category.assoc, ← DerivedCategory.Q.map_comp, Adjunction.homEquiv_unit]

end ExactAdjunction

private theorem etalePullbackFiniteLimits {T U : Scheme.{u}} (g : T ⟶ U) :
    PreservesFiniteLimits (Scheme.etaleSetPullback g) := by
  unfold Scheme.etaleSetPullback Functor.sheafPullbackConstruction.sheafPullback
  let : AB5OfSize.{u, u + 1} (Type (u + 1)) :=
    AB5OfSize_of_univLE.{u, u + 1, u + 1, u + 1} (Type (u + 1))
  infer_instance

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
/-- Construct the ordinary and derived compact-support system, including the coefficient
restriction comparison for its open part.
Source: Stacks 03S2, 03DI and 03DJ; Zheng, Constructions 4.1 and 5.15
(blueprint: lem-pur-etale-compact-support-construction).

Proof: apply the coefficient-evaluation derived-left-adjoint theorem on X, Z and Y,
and the ordinary-image and unbounded-image comparison theorems to j and g. Identify
modules over the constant quotient ring sheaves with sheaves of modules over the
quotient rings. On the small étale site, extension by zero along j is exact and left
adjoint to inverse image. Its presheaf formula commutes with coefficient restriction:
the sections and restriction maps are unchanged and only the scalar action is restricted.
Transport these level functors to the ringed-site presentation. Their adjunction
transposes commute with semilinear transitions, so they define an exact functor on
strict systems with the asserted evaluation isomorphisms. Derive these exact functors
termwise. The ordinary Hom transpose equations descend through localization, giving
all the transpose and representative equations in StrictEtaleCompactSupport. The same
identity on underlying section maps gives the displayed restriction isomorphism.
Use coefficientRestrictionOpenMap_isIso for the normalized level comparison before
transport. Its mate is the inverse-image restriction comparison because both
transposes are the restricted open-adjunction unit. Finally apply the ordinary transition equation
termwise and descend through localization. The representative equations identify the
result with the chosen derived evaluations; thus the last equation holds on all
objects of the unbounded derived category, not only on bounded complexes. -/
theorem etaleCompactSupport_construction
    (O : Type (u + 1)) [CommRing O] (t : O)
    (hregular : ∀ x : O, t * x = 0 → x = 0)
    [IsAdicComplete (Ideal.span ({t} : Set O)) O]
    {X Y : Scheme.{u}} {f : X ⟶ Y} (c : Compactification f) :
    ∃ (S : StrictEtaleCompactSupport O t c)
      (a : ∀ {m n : ℕ} (h : n ≤ m),
        (S.PX.scalar h).restriction ⋙ S.levelDerivedOpen m ≅
          S.levelDerivedOpen n ⋙ (S.PZ.scalar h).restriction),
      (∀ {m n : ℕ} (h : n ≤ m),
        (mateEquiv (S.levelDerivedOpenAdjunction n) (S.levelDerivedOpenAdjunction m)
          (.mk _ _ _ _ (a h).hom)) =
          (S.openDerived.restrictedInverse h).inv) ∧
      (∀ {m n : ℕ} (h : n ≤ m)
        (K : DerivedCategory (strictEtaleCoefficientSystem X O t)),
        (S.PZ.transition h).app (S.derivedOpen.obj K) ≫
          (S.PZ.scalar h).restriction.map ((S.openDerivedEvaluation n).hom.app K) =
        (S.openDerivedEvaluation m).hom.app K ≫
          (S.levelDerivedOpen m).map ((S.PX.transition h).app K) ≫
          (a h).hom.app ((S.PX.evaluation n).obj K))  := by
  let (T : Scheme.{u}) : HasDerivedCategory.{u + 2} (strictEtaleCoefficientSystem T O t) :=
    strictEtaleSystemDerived T O t
  let (T : Scheme.{u}) (n : ℕ) : HasDerivedCategory.{u + 2} (strictEtaleLevel T O t n) :=
    strictEtaleLevelDerived T O t n
  have := etalePullbackFiniteLimits c.g
  have := etalePullbackFiniteLimits c.i
  have proper : ∃ (IY : StrictEtaleOrdinaryImage O t c.g)
      (PY : StrictEtaleEvaluation Y O t) (PZ : StrictEtaleEvaluation c.Z O t),
      Nonempty (CoefficientSystemDerivedImage (J := Y.smallEtaleTopology)
        (K := c.Z.smallEtaleTopology) O t _ _ _ IY PY PZ) :=
    coefficientSystemDerivedComparison.{u + 1, u, u + 1, u, u + 1, u + 2} O t
      (Scheme.etaleSetPullback c.g) _ (strictEtaleSetAdjunction c.g) hregular
  obtain ⟨IY, PY, PZ, ⟨DY⟩⟩ := proper
  obtain ⟨IX⟩ := coefficientSystemOrdinaryImage_exists.{u + 1, u, u + 1, u, u + 1} O t
    (Scheme.etaleSetPullback c.i) _ (strictEtaleSetAdjunction c.i)
  obtain ⟨PX⟩ := (show Nonempty (StrictEtaleEvaluation X O t) from
    coefficientEvaluationDerivedLeftAdjoint.{u + 1, u, u + 1, u + 2}
      (J := X.smallEtaleTopology) hregular)
  obtain ⟨DX, hDX⟩ := strictEtaleImageWithRestriction_exists O t c.i IX PZ PX
  obtain ⟨H⟩ := strictEtaleOrdinaryOpen_exists O t c.i IX PX PZ
  let : IX.inverse.Additive := IX.systemInverseAdditive
  let : IX.rightSystem.Additive := IX.systemRightAdditive
  let (n : ℕ) : (IX.right n).Additive := IX.rightAdditive n
  let (n : ℕ) : (IX.lift n).modules.Additive := IX.inverseAdditive n
  let : H.extension.Additive := H.additive
  let (n : ℕ) : (H.level n).Additive := H.levelAdditive n
  have hlim : PreservesFiniteLimits H.extension := H.exact.1
  have hcolim : PreservesFiniteColimits H.extension := H.exact.2
  have hllim (n : ℕ) : PreservesFiniteLimits (H.level n) := (H.levelExact n).1
  have hlcolim (n : ℕ) : PreservesFiniteColimits (H.level n) := (H.levelExact n).2
  obtain ⟨ad, had⟩ := localizeOpenAdjunction H.extension IX.inverse H.adjunction
    H.extension.mapDerivedCategory DX.system.inverse
    H.extension.mapDerivedCategoryFactors DX.system.inverseFactors
  have hl (n : ℕ) := localizeOpenAdjunction (H.level n) (IX.lift n).modules
    (H.levelAdjunction n) (H.level n).mapDerivedCategory (DX.level n).inverse
    (H.level n).mapDerivedCategoryFactors (DX.level n).inverseFactors
  choose al hal using hl
  have he (n : ℕ) := derivedSquare_exists H.extension
    (coefficientEvaluation.{u + 1, u, u + 1} (J := X.smallEtaleTopology) n)
    (coefficientEvaluation.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) n) (H.level n)
    H.extension.mapDerivedCategory (PX.evaluation n) (PZ.evaluation n)
    (H.level n).mapDerivedCategory H.extension.mapDerivedCategoryFactors
    (PX.evaluationFactors n) (PZ.evaluationFactors n)
    (H.level n).mapDerivedCategoryFactors (H.evaluation n)
  choose e he using he
  have hb {m n : ℕ} (h : n ≤ m) := derivedSquare_exists
    (coefficientRestriction.{u + 1, u, u + 1} (J := X.smallEtaleTopology) O t h)
    (H.level n) (H.level m)
    (coefficientRestriction.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) O t h)
    (PX.scalar h).restriction (H.level n).mapDerivedCategory
    (H.level m).mapDerivedCategory (PZ.scalar h).restriction
    (PX.scalar h).restrictionFactors (H.level n).mapDerivedCategoryFactors
    (H.level m).mapDerivedCategoryFactors (PZ.scalar h).restrictionFactors (H.restriction h)
  choose a ha using @hb
  have hmate {m n : ℕ} (h : n ≤ m) :
      (mateEquiv (al n) (al m) (.mk _ _ _ _ (a h).hom)) =
        (DX.restrictedInverse h).inv := by
    let τ : TwoSquare (DX.level n).inverse (PZ.scalar h).restriction
        (PX.scalar h).restriction (DX.level m).inverse :=
      .mk _ _ _ _ (DX.restrictedInverse h).inv
    have hr := derivedSquare_symm_rep
      (coefficientRestriction.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) O t h)
      (IX.lift n).modules (IX.lift m).modules
      (coefficientRestriction.{u + 1, u, u + 1} (J := X.smallEtaleTopology) O t h)
      (PZ.scalar h).restriction (DX.level n).inverse (DX.level m).inverse
      (PX.scalar h).restriction (PZ.scalar h).restrictionFactors
      (DX.level n).inverseFactors (DX.level m).inverseFactors
      (PX.scalar h).restrictionFactors (IX.restrictInverse h) (DX.restrictedInverse h)
      (hDX h)
    have hi (P : strictEtaleLevel X O t n) :
        (H.levelAdjunction m).homEquiv _ _ ((H.restriction h).hom.app P) =
      (coefficientRestriction.{u + 1, u, u + 1} (J := X.smallEtaleTopology) O t h).map
        ((H.levelAdjunction n).unit.app P) ≫
          (IX.restrictInverse h).inv.app ((H.level n).obj P) := by
      rw [Adjunction.homEquiv_unit]
      have hu := unit_mateEquiv (H.levelAdjunction n) (H.levelAdjunction m)
        (.mk _ _ _ _ (H.restriction h).hom) P
      change (coefficientRestriction.{u + 1, u, u + 1}
        (J := X.smallEtaleTopology) O t h).map ((H.levelAdjunction n).unit.app P) ≫
          ((mateEquiv (H.levelAdjunction n) (H.levelAdjunction m)
            (.mk _ _ _ _ (H.restriction h).hom))).app ((H.level n).obj P) =
        (H.levelAdjunction m).unit.app _ ≫
          (IX.lift m).modules.map ((H.restriction h).hom.app P) at hu
      rw [show (mateEquiv (H.levelAdjunction n) (H.levelAdjunction m)
        (.mk _ _ _ _ (H.restriction h).hom)) = (IX.restrictInverse h).inv from
          H.restrictionMate h] at hu
      exact hu.symm
    have hrep (P : CochainComplex (strictEtaleLevel X O t n) ℤ) :=
      derivedMate_comparison
        ((H.levelAdjunction n).mapHomologicalComplex (.up ℤ))
        ((H.levelAdjunction m).mapHomologicalComplex (.up ℤ)) (al n) (al m)
        (H.level n).mapDerivedCategoryFactors.hom (H.level m).mapDerivedCategoryFactors.hom
        (DX.level n).inverseFactors (DX.level m).inverseFactors
        (PX.scalar h).restrictionFactors (PZ.scalar h).restrictionFactors (hal n) (hal m)
        (.mk _ _ _ _ ((NatIso.mapHomologicalComplex (IX.restrictInverse h) (.up ℤ)).inv))
        τ hr (NatIso.mapHomologicalComplex (H.restriction h) (.up ℤ)).hom
        (fun P ↦ by
          rw [Adjunction.homEquiv_unit]
          apply HomologicalComplex.hom_ext
          intro i
          exact hi (P.X i)) P
    have heq : ((mateEquiv (al n) (al m)).symm τ) = (a h).hom := by
      apply (Localization.fullyFaithfulWhiskeringLeft DerivedCategory.Q
        (HomologicalComplex.quasiIso (strictEtaleLevel X O t n) (.up ℤ))
        (DerivedCategory (strictEtaleLevel c.Z O t m))).map_injective
      apply NatTrans.ext
      funext P
      apply (cancel_mono ((PZ.scalar h).restriction.map
        ((H.level n).mapDerivedCategoryFactors.hom.app P) ≫
        (PZ.scalar h).restrictionFactors.hom.app
          (((H.level n).mapHomologicalComplex (.up ℤ)).obj P))).1
      exact (hrep P).trans (ha h P).symm
    have heq' : (mateEquiv (al n) (al m)
        (.mk _ _ _ _ (a h).hom)) = τ := by
      rw [← heq]
      exact ((mateEquiv (al n) (al m)).apply_symm_apply τ)
    exact heq'
  have htransition {m n : ℕ} (h : n ≤ m)
      (K : DerivedCategory (strictEtaleCoefficientSystem X O t)) :
      (PZ.transition h).app (H.extension.mapDerivedCategory.obj K) ≫
      (PZ.scalar h).restriction.map ((e n).hom.app K) =
      (e m).hom.app K ≫ (H.level m).mapDerivedCategory.map ((PX.transition h).app K) ≫
        (a h).hom.app ((PX.evaluation n).obj K) := by
    have ht := transition_localization H.extension
      (coefficientEvaluation.{u + 1, u, u + 1} (J := X.smallEtaleTopology) n)
      (coefficientEvaluation.{u + 1, u, u + 1} (J := X.smallEtaleTopology) m)
      (coefficientEvaluation.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) n)
      (coefficientEvaluation.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) m)
      (H.level n) (H.level m)
      (coefficientRestriction.{u + 1, u, u + 1} (J := X.smallEtaleTopology) O t h)
      (coefficientRestriction.{u + 1, u, u + 1} (J := c.Z.smallEtaleTopology) O t h)
      H.extension.mapDerivedCategory (PX.evaluation n) (PX.evaluation m)
      (PZ.evaluation n) (PZ.evaluation m) (H.level n).mapDerivedCategory
      (H.level m).mapDerivedCategory (PX.scalar h).restriction (PZ.scalar h).restriction
      H.extension.mapDerivedCategoryFactors (PX.evaluationFactors n) (PX.evaluationFactors m)
      (PZ.evaluationFactors n) (PZ.evaluationFactors m)
      (H.level n).mapDerivedCategoryFactors (H.level m).mapDerivedCategoryFactors
      (PX.scalar h).restrictionFactors (PZ.scalar h).restrictionFactors
      (H.evaluation n) (H.evaluation m) (H.restriction h) (e n) (e m) (a h)
      (PX.strictTransition h) (PZ.strictTransition h) (PX.transition h) (PZ.transition h)
      (he n) (he m) (ha h) (PX.transition_rep h) (PZ.transition_rep h) (H.transition h) K
    exact ht
  let D : StrictEtaleCompactSupportData O t c := {
    PX := PX
    PY := PY
    PZ := PZ
    openImage := IX
    properImage := IY
    properDerived := DY
    openExtension := H.extension
    openAdjunction := H.adjunction
    levelOpen := H.level
    levelOpenAdjunction := H.levelAdjunction
    openEvaluation := H.evaluation
    derivedOpen := H.extension.mapDerivedCategory
    openDerived := DX
    derivedOpenAdjunction := ad
    openFactors := H.extension.mapDerivedCategoryFactors
    levelDerivedOpen := fun n ↦ (H.level n).mapDerivedCategory
    levelDerivedOpenAdjunction := al
    levelOpenFactors := fun n ↦ (H.level n).mapDerivedCategoryFactors
    openDerivedEvaluation := e }
  have hD : StrictEtaleCompactSupportCoherence O t c D :=
    ⟨H.exact, H.evaluationMate, had, hal, he⟩
  let S : StrictEtaleCompactSupport O t c := ⟨D, hD⟩
  exact ⟨S, fun {_ _} h ↦ a h, fun h ↦ hmate h, fun h K ↦ htransition h K⟩

end AlgebraicGeometry

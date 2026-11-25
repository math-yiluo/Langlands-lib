/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.CategoryTheory.Flat.FlatScalarKoszulModelsSupplement
import all WeilConjectures.CategoryTheory.Strict.StrictScalarKoszulInstances
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarTensorComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarPositiveComparison
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarPositiveBasis
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomDiagram
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomNaturality
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomCoordinates
import all WeilConjectures.CategoryTheory.Koszul.KoszulScalarHomUnit
import all WeilConjectures.CategoryTheory.Koszul.KoszulTensorEvaluationCoordinates

/-! # StrictScalarKoszulComparison for strict Koszul comparison

Source: Stacks Project, Tags 0A0E and 0913.
(blueprint: lem-weil-pbc-strict-scalar-koszul-comparison).
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 4096

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace CategoryTheory.FlatScalarKoszul

variable {S : Type u} [SmallCategory S] {J : GrothendieckTopology S}
variable {R B : Sheaf J CommRingCat.{u}}

open MonoidalCategory
open scoped CategoryTheory.Prod

attribute [local irreducible] homComplexFunctor
  SheafOfModules.tensorObjIsoSheafification PresheafOfModules.sheafificationAdjunction
  Localization.Monoidal.tensorBifunctor

attribute [local instance] gradedTensorCache gradedGoodTensorLeftCache
  gradedGoodTensorRightCache gradedFourCache tensorPreservesEmptyLeftCache
  tensorPreservesEmptyRightCache cachedModuleMonoidal cachedModuleSymmetric
  cachedModulePreadditive cachedModuleClosed cachedComplexMonoidal
  cachedComplexBraided cachedComplexClosed

private theorem koszulEvaluation_coordinates (O : Sheaf J CommRingCat.{u}) (r : ℕ)
    (a : Fin r → (O.obj ⋙ forget CommRingCat).sections) (N : ringedSiteComplex O)
    (m : ℕ) (b : Fin r → Bool) (n : ℤ) :
    ((koszulEvaluation O r a N).hom.app (op m)).f n ≫
        homCoordinate O r a N m b n = coordinate O r a N m b n := by
  exact evaluation_coordinates O ((ringedKoszulDiagram O r a).obj m) N
    (degree r b) (positiveBasis O r a m b) n

private theorem comparisonCoordinates
    {D : Type*} [Category D] {D' : Type*} [Category D']
    (F : D ⥤ D') {X Y Z : D} {U V : D'}
    (i : X ≅ Y) (j : U ≅ V) (k : F.obj Y ⟶ V)
    (cX : X ⟶ Z) (cY : Y ⟶ Z) (cU : U ⟶ F.obj Z) (cV : V ⟶ F.obj Z)
    (hi : i.hom ≫ cY = cX) (hj : j.hom ≫ cV = cU)
    (hk : k ≫ cV = F.map cY) :
    F.map i.hom ≫ k ≫ j.inv ≫ cU = F.map cX := by
  rw [← hj, Iso.inv_hom_id_assoc, hk, ← F.map_comp, hi]

private theorem strictComparisonFromPositive_coordinates (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    (hb : ∀ (m : ℕ) (b : Fin r → Bool),
      (extension φ).map (positiveBasis R r a m b) ≫ (e.hom.app m).f (degree r b) =
        (SheafOfModules.scalarExtensionUnitIso φ).hom ≫
          positiveBasis B r (imageSections φ a) m b) :
    ∀ (N : ringedSiteComplex B) (m : ℕ) (b : Fin r → Bool) (n : ℤ),
      (((strictComparisonFromPositive φ r a e).hom.app N).f n).app (op m) ≫
          coordinate R r a ((restrictComplex φ).obj N) m b n =
        (restriction φ).map (coordinate B r (imageSections φ a) N m b n) := by
  intro N m b n
  exact comparisonCoordinates (restriction φ)
    ((HomologicalComplex.eval (Modules B) (.up ℤ) n).mapIso
      ((koszulEvaluation B r (imageSections φ a) N).app (op m)))
    ((HomologicalComplex.eval (Modules R) (.up ℤ) n).mapIso
      ((koszulEvaluation R r a ((restrictComplex φ).obj N)).app (op m)))
    (((homDiagramComparison φ r a e N).hom.app (op m)).f n)
    (coordinate B r (imageSections φ a) N m b n)
    (homCoordinate B r (imageSections φ a) N m b n)
    (coordinate R r a ((restrictComplex φ).obj N) m b n)
    (homCoordinate R r a ((restrictComplex φ).obj N) m b n)
    (koszulEvaluation_coordinates B r (imageSections φ a) N m b n)
    (koszulEvaluation_coordinates R r a ((restrictComplex φ).obj N) m b n)
    (homDiagramComparison_coordinates φ r a e hb N m b n)

private theorem strictComparisonFromPositive_unit (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections)
    (e : ringedKoszulDiagram R r a ⋙
      (extension φ).mapHomologicalComplex (.up ℤ) ≅
        ringedKoszulDiagram B r (imageSections φ a))
    (hp : ∀ m : ℕ,
      ((extension φ).mapHomologicalComplex (.up ℤ)).map
          (ringedKoszulProjection R r a m) ≫ (scalarTensorComparison φ).j.hom =
        e.hom.app m ≫ ringedKoszulProjection B r (imageSections φ a) m) :
    ∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
      (restriction φ).map
          ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
          (((strictComparisonFromPositive φ r a e).hom.app N).f n).app m =
        (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n := by
  intro N m n
  change ((restrictComplex φ).map
      (ringedKoszulTensorUnitComponent B r (imageSections φ a) N m)).f n ≫
      ((tensorDiagramComparison φ r a e N).hom.app m).f n = _
  exact congrArg (fun f ↦ f.f n)
    (tensorDiagramComparison_unit φ r a e
      hp N m)

/-- The finite ordered Koszul comparison is independent of flatness and of derived
categories.

Source: Stacks Project, algebraization.tex, Tag 0A0E (finite Koszul calculation);
more-algebra.tex, Tag 0913 (Koszul complexes).
(blueprint: lem-weil-pbc-strict-scalar-koszul-comparison).

Proof: Let E be ordinary scalar extension along φ, left adjoint to restriction. Its
binary tensor and unit isomorphisms, transported from the localization tensor to the
site tensor, satisfy the right-unit coherence; since E preserves coproducts they extend
to total tensor complexes. Each positive Koszul factor is the two-term complex given by
multiplication by a power of a section, and E carries it to the factor over B of the
image section; induction on the ordered list gives a natural isomorphism E(K_R) ≅ K_B
of strict inverse diagrams preserving every positiveBasis and the projection to the
unit complex. Every finite Koszul stage is dualizable, so the canonical evaluation
identifies N ⊗ Hom(K, unit) with Hom(K, N). Composing the B evaluation, precomposition
with E(K_R) ≅ K_B, the normalized scalar-restriction Hom isomorphism θ and the inverse
R evaluation gives an isomorphism natural in N and in the stage, hence of complexes of
strict towers. On the summand N^p ⊗ Hom(K,unit)^q evaluation followed by a Hom
coordinate carries the signs (-1)^(dn), (-1)^(pq), (-1)^(dq) (d the basis degree); it
vanishes unless d + q = 0, where the total exponent is 2dq, and it equals dualCoordinate
followed by the right unitor; so coordinates are preserved. Canonical evaluation carries
the coaugmentation to precomposition with the Koszul projection after the inverse
Hom-unit evaluation, and naturality of θ with its unit formula gives the coaugmentation
identity. The case r = 0 is the base of the induction; no flatness is used. -/
theorem strictScalarKoszulComparison (φ : R ⟶ B) (r : ℕ)
    (a : Fin r → (R.obj ⋙ forget CommRingCat).sections) :
    ∃ h : ringedKoszulTensorTowerFunctor B r (imageSections φ a) ⋙
        restrictTowerComplex φ ≅
      restrictComplex φ ⋙ ringedKoszulTensorTowerFunctor R r a,
      (∀ (N : ringedSiteComplex B) (m : ℕ) (e : Fin r → Bool) (n : ℤ),
        ((h.hom.app N).f n).app (op m) ≫
            coordinate R r a ((restrictComplex φ).obj N) m e n =
          (restriction φ).map (coordinate B r (imageSections φ a) N m e n)) ∧
      (∀ (N : ringedSiteComplex B) (m : ℕᵒᵖ) (n : ℤ),
        (restriction φ).map
            ((ringedKoszulTensorUnitComponent B r (imageSections φ a) N m).f n) ≫
            ((h.hom.app N).f n).app m =
          (ringedKoszulTensorUnitComponent R r a ((restrictComplex φ).obj N) m).f n) := by
  let H := scalarTensorComparison φ
  let e := (positiveComparison φ r a H H.j).1
  refine ⟨strictComparisonFromPositive φ r a e, ?_, ?_⟩
  · exact strictComparisonFromPositive_coordinates φ r a e (scalarPositiveBasis φ r a)
  · exact strictComparisonFromPositive_unit φ r a e (positiveComparison φ r a H H.j).2

end CategoryTheory.FlatScalarKoszul

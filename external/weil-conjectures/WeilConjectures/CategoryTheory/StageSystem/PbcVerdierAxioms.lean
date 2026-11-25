/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Pbc.PbcCommonStageCones
public import Mathlib.CategoryTheory.Triangulated.Triangulated
public import Mathlib.CategoryTheory.Triangulated.Functor
public import WeilConjectures.CategoryTheory.StageSystem.StageSystemVerdier
import Mathlib.CategoryTheory.Triangulated.Adjunction
import Mathlib.CategoryTheory.Localization.Triangulated
import WeilConjectures.CategoryTheory.DerivedCategory.Complete.RationalizationHom

/-! # Verdier axioms for the specified common-stage triangles

Source: blueprint `thm-weil-pbc-verdier-axioms`, order 1540.
(blueprint: thm-weil-pbc-verdier-axioms)
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true
universe w u v
open CategoryTheory CategoryTheory.Pretriangulated CategoryTheory.Limits
-- Compare the concrete tensor-Hom model with the existing Verdier localization.
private noncomputable def stageRationalComparison
    (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    ScalarLocalization R C p ⥤ Rationalization (Submonoid.powers p) C where
  obj X := (Rationalization.Q (Submonoid.powers p) C).obj X.obj
  map {X Y} f := Rationalization.tensorHomEquiv (Submonoid.powers p)
    (Localization.Away p) X.obj Y.obj f
  map_id X := by
    change Rationalization.tensorHomEquiv _ _ _ _ (1 ⊗ₜ[R] 𝟙 X.obj) = _
    simp
  map_comp {X Y Z} f g := by
    induction f using TensorProduct.inductionOn with
    | tmul a f =>
      induction g using TensorProduct.inductionOn with
      | tmul b g =>
        change Rationalization.tensorHomEquiv _ _ _ _
          (ScalarLocalization.composition R C p _ _ _ (b ⊗ₜ[R] g) (a ⊗ₜ[R] f)) = _
        rw [ScalarLocalization.composition_tmul]
        simp only [Rationalization.tensorHomEquiv_tmul, Functor.map_comp,
          Linear.smul_comp, Linear.comp_smul, smul_smul, mul_comm]
      | add g h hg hh =>
        rw [Preadditive.comp_add X Y Z (a ⊗ₜ[R] f) g h]
        simp only [_root_.map_add]
        rw [hg, hh]
        exact (Preadditive.comp_add _ _ _ _ _ _).symm
    | add f h hf hh =>
      rw [Preadditive.add_comp X Y Z f h g]
      simp only [_root_.map_add]
      rw [hf, hh]
      exact (Preadditive.add_comp _ _ _ _ _ _).symm

private theorem stageLocalization
    (R : Type*) [CommRing R] (C : Type u) [Category.{v} C]
    [Preadditive C] [Linear R C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C] [IsTriangulated C]
    [∀ n : ℤ, (shiftFunctor C n).Linear R] (p : R) :
    (ScalarLocalization.localization R C p).IsLocalization
      (Rationalization.W (Submonoid.powers p) C) := by
  classical
  let M := Submonoid.powers p
  let F := stageRationalComparison R C p
  have : F.Full := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).surjective⟩
  have : F.Faithful := ⟨fun {X Y} ↦
    (Rationalization.tensorHomEquiv M (Localization.Away p) X.obj Y.obj).injective⟩
  have : F.EssSurj := ⟨fun X ↦ by
    obtain ⟨Y, ⟨e⟩⟩ := Rationalization.exists_iso_obj X
    exact ⟨⟨Y⟩, ⟨e⟩⟩⟩
  have : F.IsEquivalence := {}
  let Q := ScalarLocalization.localization R C p
  have fac : Q ⋙ F ≅ Rationalization.Q M C :=
    NatIso.ofComponents (fun X ↦ Iso.refl _) (by
      intro X Y f
      dsimp [Q, F, ScalarLocalization.localization, stageRationalComparison]
      simp only [Category.comp_id, Category.id_comp,
        Rationalization.tensorHomEquiv_tmul, one_smul]
      rfl)
  exact Functor.IsLocalization.of_equivalence_target (Rationalization.Q M C)
      (Rationalization.W M C) Q F.asEquivalence.symm
      (Functor.isoWhiskerRight fac.symm F.inv ≪≫ Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft Q F.asEquivalence.unitIso.symm ≪≫ Q.rightUnitor)

namespace CategoryTheory.StageSystem

variable {I : Type w} [Preorder I] [IsDirectedOrder I] [Nonempty I]
    {C : I → Type u} [∀ i, Category.{v} (C i)] (S : StageSystem C)
    [∀ i, HasShift (C i) ℤ]
    [∀ {i j : I} (h : i ≤ j), (S.T h).CommShift ℤ]
    [∀ {i j k : I} (h : i ≤ j) (h' : j ≤ k),
      NatTrans.CommShift (S.assoc h h').hom ℤ]
    [∀ i, Preadditive (C i)]
    [∀ {i j : I} (h : i ≤ j), (S.T h).Additive]
    [∀ i, HasZeroObject (C i)]
    [∀ i, ∀ n : ℤ, (shiftFunctor (C i) n).Additive]
    [∀ i, Pretriangulated (C i)]
    [stageTriangulated : ∀ i, IsTriangulated (C i)]
    [transitionExact : ∀ {i j : I} (h : i ≤ j), (S.T h).IsTriangulated]

set_option linter.unusedSectionVars false in
/-- Finite-stage inclusions preserve the already recorded common-stage addition.
Source: blueprint order 1540, exact stage inclusion
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: both included sums are represented by the transition image of the same
sum at the original stage. Additivity of the transitions makes this the sum of
the two included representatives; pairPreadditiveNormalized identifies the classes. -/
@[instance] theorem qbarStageInclusionAdditive (i : I) : (S.ι i).Additive := by
  constructor
  intro X Y f g
  change PairCategory.mkHom (X := ⟨i, X⟩) (Y := ⟨i, Y⟩) i le_rfl le_rfl
    ((S.T le_rfl).map (f + g)) = _
  rw [Functor.map_add]
  exact ((pairPreadditive_exists S).exists.choose_spec _ _ _ _ _ _ _).1

set_option linter.unusedSectionVars false in
/-- The actual transition identification commutes with the induced pair shift.
Source: blueprint order 1540, exact transition identifications
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: the components of transIso are finite-stage identity maps with the
specified associators. Expand the induced pair shift on those representatives.
The associator CommShift equation identifies the two resulting arrows at the
same common stage, so their classes agree. This is precisely NatTrans.CommShift. -/
@[instance] theorem qbarTransIsoCommShift {i j : I} (h : i ≤ j) :
    NatTrans.CommShift (S.transIso h).hom ℤ := by
  constructor
  intro n
  ext X
  simp only [Functor.commShiftIso_comp_hom_app, NatTrans.comp_app,
    Functor.whiskerRight_app, Functor.whiskerLeft_app]
  change ((S.ι j).map (((S.T h).commShiftIso n).hom.app X) ≫
    𝟙 _) ≫ (pbcPairShift S n).map ((S.transIso h).hom.app X) =
    (S.transIso h).hom.app ((shiftFunctor (C i) n).obj X) ≫ 𝟙 _
  simp only [Category.comp_id]
  simp only [transIso_hom_app, isoToStage, pbcPairShift]
  erw [Morphism.functor_map_mkHom, ι_map_eq (le_rfl : j ≤ j),
    PairCategory.mkHom_comp_mkHom]
  congr 1
  change (S.T (le_rfl : j ≤ j)).map (((S.T h).commShiftIso n).hom.app X) ≫
    (((S.T (le_rfl : j ≤ j)).commShiftIso n).hom.app ((S.T h).obj X) ≫
      (shiftFunctor (C j) n).map ((S.assoc h le_rfl).hom.app X) ≫
        ((S.T h).commShiftIso n).inv.app X) =
    (S.assoc h le_rfl).hom.app ((shiftFunctor (C i) n).obj X)
  have eq := congrArg (fun f ↦ f ≫ ((S.T h).commShiftIso n).inv.app X)
    (pbcStageShift_coherence S n h le_rfl X)
  simpa only [Category.assoc, Iso.hom_inv_id_app, Functor.comp_obj,
    Category.comp_id] using eq

/-- The recorded Verdier theorem uniquely fixes the pretriangulation by the
recorded CommonStageDistinguished predicate. Its data is the specified triangle
set; the inherited HasShift and Hom group structures are retained.
Source: blueprint order 1540 (blueprint: thm-weil-pbc-verdier-axioms). -/
instance qbarPairPretriangulated : Pretriangulated S.PairCategory :=
  (commonStage_verdier_existsUnique S).exists.choose

end CategoryTheory.StageSystem

namespace AlgebraicGeometry.Scheme
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme
variable (l : ℕ) [Fact l.Prime] (Qbar : Type w)
    [Field Qbar] [Algebra ℚ_[l] Qbar] [IsAlgClosure ℚ_[l] Qbar]
    (T : Scheme.{u}) [IsNoetherian T]
    [hDim : Fact (∃ n : ℕ, topologicalKrullDim T ≤ (n : WithBot ℕ∞))]
    [hInv : Fact (∀ t : T, IsUnit (l : T.presheaf.stalk t))]

/-- The finite stage is triangulated for exactly its integral-image triangles.
Source: blueprint order 1540, finite-stage input (blueprint: thm-weil-pbc-verdier-axioms).
Proof: apply raw scalar-localization triangulation to the inherited integral
triangulation. Its normalized shift agrees with the published rational shift;
its image-triangle characterization is qbarStagePretriangulated_exists, which
specifies the same distinguished set. Transport TR4 along these identifications. -/
@[instance] theorem qbarStageTriangulated (E : Padic.FiniteCoefficientFields l Qbar) :
    IsTriangulated (pbcStageCategory l Qbar T E) := by
  let C := pbcIntegralStage l Qbar T E
  let R := PbcIntegralRing l (pbcFiniteField.{u} l Qbar E)
  let p : R := pbcStageUniformizer.{u} l Qbar E
  let Q := pbcStageLocalization l Qbar T E
  have : Q.IsLocalization (Rationalization.W (Submonoid.powers p) C) :=
    stageLocalization R C p
  let t := Triangulated.Localization.pretriangulated Q
    (Rationalization.W (Submonoid.powers p) C)
  have ht : (fun [pInst : Pretriangulated (pbcStageCategory l Qbar T E)] ↦
      ∀ D : Triangle (pbcStageCategory l Qbar T E),
        D ∈ distTriang (pbcStageCategory l Qbar T E) ↔
          ∃ D' : Triangle C, D' ∈ distTriang C ∧
            Nonempty (D ≅ Q.mapTriangle.obj D')) (pInst := t) := by
    intro D
    change (∃ D', ∃ _ : D ≅ Q.mapTriangle.obj D', D' ∈ distTriang C) ↔ _
    constructor
    · rintro ⟨D', e, hD'⟩
      exact ⟨D', hD', ⟨e⟩⟩
    · rintro ⟨D', hD', ⟨e⟩⟩
      exact ⟨D', e, hD'⟩
  have heq : t = qbarStagePretriangulated l Qbar T E :=
    (qbarStagePretriangulated_exists l Qbar T E).unique ht
      (qbarStagePretriangulated_exists l Qbar T E).exists.choose_spec
  let := t
  have ht4 : IsTriangulated (pbcStageCategory l Qbar T E) :=
    Triangulated.Localization.isTriangulated Q (Rationalization.W (Submonoid.powers p) C)
  change @IsTriangulated _ _ _ _ _ _ t at ht4
  rw [heq] at ht4
  exact ht4

/-- The prescribed coefficient tensor preserves the integral-image triangles.
Source: blueprint order 1540, exact finite-stage input
(blueprint: thm-weil-pbc-verdier-axioms).
Proof: on K-flat complexes integral tensor takes cone triangles to cone triangles.
It preserves the defining integral subcategories. The normalized localization
square therefore takes every integral image triangle to a target integral image
triangle, with the actual tensor shift comparison. Isomorphism closure gives
exactness on every distinguished rational triangle, including identity fields. -/
@[instance] theorem qbarScalarExtensionExact {E F : Padic.FiniteCoefficientFields l Qbar}
    (h : E ≤ F) : (pbcScalarExtension l Qbar T hDim.out hInv.out h).IsTriangulated := by
  let A := pbcAmbientScalarExtension l Qbar T h
  let B := pbcIntegralScalarExtension l Qbar T hDim.out hInv.out h
  let Q := pbcStageLocalization l Qbar T E
  let Q' := pbcStageLocalization l Qbar T F
  let G := pbcScalarExtension l Qbar T hDim.out hInv.out h
  have : (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Qbar T h)).CommShift ℤ :=
    Adjunction.commShift_of_rightAdjoint _ ℤ
  have : (pbcDerivedRestrict (pbcCompletedScalarMap l Qbar T h)).IsTriangulated :=
    inferInstanceAs (((pbcRestrict (pbcCompletedScalarMap l Qbar T h)).mapDerivedCategory
      ).IsTriangulated)
  have : A.IsTriangulated :=
    (pbcDerivedScalarAdjunction (pbcCompletedScalarMap l Qbar T h)).isTriangulated_leftAdjoint
  let eB : B ⋙ pbcStageInclusion l Qbar T F ≅ pbcStageInclusion l Qbar T E ⋙ A :=
    Iso.refl _
  have : NatTrans.CommShift eB.hom ℤ :=
    Functor.CommShift.ofComp_compatibility (F := B)
      (G := pbcStageInclusion l Qbar T F) eB ℤ
  have : B.IsTriangulated :=
    (Functor.isTriangulated_iff_comp_right eB).2 inferInstance
  have hQ (D : Triangle (pbcIntegralStage l Qbar T F)) (hD : D ∈ distTriang _) :
      Q'.mapTriangle.obj D ∈ distTriang _ :=
    ((qbarStagePretriangulated_exists l Qbar T F).exists.choose_spec _).2
      ⟨D, hD, ⟨Iso.refl _⟩⟩
  have : NatTrans.CommShift
      (pbcScalarIntegralComparison l Qbar T hDim.out hInv.out h).hom ℤ :=
    (pbcScalarShift_exists l Qbar T hDim.out hInv.out h).exists.choose_spec
  constructor
  intro D hD
  obtain ⟨D', hD', ⟨e⟩⟩ :=
    ((qbarStagePretriangulated_exists l Qbar T E).exists.choose_spec D).1 hD
  have hBD := hQ (B.mapTriangle.obj D') (B.map_distinguished D' hD')
  let c := (Functor.mapTriangleCompIso Q G).symm.app D' ≪≫
    (Functor.mapTriangleIso
      (pbcScalarIntegralComparison l Qbar T hDim.out hInv.out h)).app D' ≪≫
    (Functor.mapTriangleCompIso B Q').app D'
  exact isomorphic_distinguished _ hBD _
    ((G.mapTriangle.mapIso e) ≪≫ c)

/-- The actual common-stage triangulation satisfies all four Verdier axioms.
Source: blueprint order 1540 (blueprint: thm-weil-pbc-verdier-axioms).
Proof: apply commonStage_verdier_existsUnique to the actual completed integral
rational stages and their exact scalar transitions. Its proof moves finitely
many representatives and equations to one common stage: finite-stage TR1 gives
cones and identity triangles, TR2 gives signed rotation, and TR3 completes
commutative squares. Cone independence and finite-stage TR4 give the octahedron.
Its distinguished set is exactly CommonStageDistinguished by construction.
The same theorem gives exactness of the stage inclusions, and the specified
shift comparisons give qbarTransIsoCommShift for every transition identification. -/
theorem pbcVerdierAxioms :
    CategoryTheory.IsTriangulated (PbcFiniteStagePairCategory l Qbar T hDim.out hInv.out) ∧
    (∀ E : Padic.FiniteCoefficientFields l Qbar,
      ((pbcScalarSystem l Qbar T hDim.out hInv.out).ι E).IsTriangulated) ∧
    ∀ {E F : Padic.FiniteCoefficientFields l Qbar} (h : E ≤ F),
      NatTrans.CommShift ((pbcScalarSystem l Qbar T hDim.out hInv.out).transIso h).hom ℤ := by
  let S := pbcScalarSystem l Qbar T hDim.out hInv.out
  have ht := (CategoryTheory.StageSystem.commonStage_verdier_existsUnique S).exists.choose_spec
  exact ⟨ht.2.1, ht.2.2, fun h ↦ inferInstance⟩

end AlgebraicGeometry.Scheme

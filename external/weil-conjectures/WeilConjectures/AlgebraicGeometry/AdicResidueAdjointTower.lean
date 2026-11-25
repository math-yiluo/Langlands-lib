/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.AlgebraicGeometry.AdicResidueLiftComparisons
import WeilConjectures.CategoryTheory.DerivedCategory.ResolvingAdjunction
import all WeilConjectures.CategoryTheory.ModulePullbackPushforwardAdjunction
public import Mathlib.CategoryTheory.Adjunction.Basic

/-! # The quotient tower obtained by scalar adjunction

Source: Stacks Project, Tags 03CZ, 09T5, 0FND, 099M and 09C6.
(auxiliary; not a blueprint node).

The transition is the transpose of the reduction of the preceding counit.
Its action on all transposed morphisms follows from adjunction naturality.
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxSize 2048
attribute [-instance] CategoryTheory.GrothendieckTopology.hasSheafify_of_essentiallySmall
universe u v w
open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.ConstantCompletion

namespace AlgebraicGeometry.Scheme

/-- The scalar adjunction is uniquely specified by the existing normalized derived unit.
Source: Stacks Tags 03CZ, 09T5 and 0FND
(auxiliary; not a blueprint node).
Proof: derive the ordinary tensor/restriction adjunction using K-flat resolutions.
Compare the resulting left derived functor with the specified universal pair. The
comparison identifies its unit on K-flat complexes with the existing scalar unit;
uniqueness of that unit and extensionality of adjunctions give uniqueness. -/
theorem adicResidueScalarAdjunction_existsUnique
    {C : Type w} [SmallCategory C] {T : GrothendieckTopology C}
    {R S : Sheaf T CommRingCat.{w}} (f : R ⟶ S) :
    ∃! adj : extend f ⊣ dres f, adj.unit = adicFiniteUnit f := by
  let := HasDerivedCategory.standard (Mod R)
  let := HasDerivedCategory.standard (Mod S)
  let := (siteRestrictScalars_exact f).1
  let := (siteRestrictScalars_exact f).2
  obtain ⟨E, hobj, hmap, _, hpres, _⟩ :=
    SheafOfModules.derivedChangeOfRingsIndependentCoefficients f
  have hE : E = change f := CategoryTheory.Functor.ext hobj (fun _ _ a ↦ hmap a)
  have hpres' : ∀ {P Q : Cx R} (a : P ⟶ Q),
      P.IsKFlatIndependentCoefficients → Q.IsKFlatIndependentCoefficients →
        QuasiIso a → QuasiIso (((change f).mapHomologicalComplex (.up ℤ)).map a) := by
    cases hE
    exact hpres
  obtain ⟨_, L, ε, hu, _, adj, ha⟩ :=
    Adjunction.exists_leftDerived_adjunction (change f) (res f)
      (SheafOfModules.tensorAdjunction f)
      (CochainComplex.IsKFlatIndependentCoefficients (R := R))
      (fun P ↦ by
        obtain ⟨Y, s, hY, _, hs, _⟩ :=
          CochainComplex.exists_isKFlatResolutionIndependentCoefficients P
        exact ⟨Y, s, hY, hs⟩) hpres'
  let : (SheafOfModules.tensorFunctor f).Additive := change_additive f
  let : L.IsLeftDerivedFunctor ε (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := hu
  let : (extend f).IsLeftDerivedFunctor (extendComparison f)
      (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) := (derivedExtension f).universal
  let i := Functor.leftDerivedUnique (extend f) L ε
    (extendComparison f) (HomologicalComplex.quasiIso (Mod R) (.up ℤ))
  let adj' : extend f ⊣ dres f := adj.ofNatIsoLeft i
  have hi (P : Cx R) : i.hom.app ((Q R).obj P) ≫ (extendComparison f).app P = ε.app P := by
    simpa only [i, Functor.leftDerivedUnique, Functor.leftDerivedNatIso_hom,
      Functor.leftDerivedNatTrans, Iso.refl_hom, NatTrans.id_app, Category.comp_id] using
      (Functor.leftDerived_fac_app (extend f) (extendComparison f)
        (HomologicalComplex.quasiIso (Mod R) (.up ℤ)) L ε P)
  have hunit : adj'.unit = adicFiniteUnit f := by
    apply (adicFiniteUnit_existsUnique f).unique
    · intro P _
      have h := (adj'.homEquiv_unit _ _ ((extendComparison f).app P)).symm
      apply h.trans
      change (adj.ofNatIsoLeft i).homEquiv _ _ ((extendComparison f).app P) = _
      rw [Adjunction.homEquiv_ofNatIsoLeft_apply, hi]
      have ha := ha P (((change f).mapHomologicalComplex (.up ℤ)).obj P) (𝟙 _)
      simp only [CategoryTheory.Functor.map_id, Adjunction.homEquiv_id] at ha
      have hordinary : (SheafOfModules.tensorAdjunction f).unit =
          adicFiniteOrdinaryUnit f := by
        apply NatTrans.ext
        funext M
        apply (underlying R).map_injective
        exact ((insertion_existsUnique f M).unique
          (SheafOfModules.tensorUnit_apply f M)
          (insertion_existsUnique f M).exists.choose_spec).trans
            ((adicFiniteOrdinaryUnit_existsUnique f).exists.choose_spec M).symm
      have hcomplex : ((SheafOfModules.tensorAdjunction f).mapHomologicalComplex
          (.up ℤ)).unit.app P = adicFiniteOrdinaryUnitComplex f P := by
        ext q
        simp only [Adjunction.mapHomologicalComplex_unit_app_f, hordinary]
        rfl
      rw [hcomplex] at ha
      change adj.homEquiv ((Q R).obj P)
        (((change f).mapHomologicalComplex (.up ℤ) ⋙ Q S).obj P)
        (ε.app P ≫ 𝟙 _) =
          (Q R).map (adicFiniteOrdinaryUnitComplex f P) ≫
            (resFactors f).hom.app
              (((change f).mapHomologicalComplex (.up ℤ)).obj P) at ha
      rw [CategoryTheory.Category.comp_id] at ha
      exact ha
    · exact (adicFiniteUnit_existsUnique f).exists.choose_spec
  refine ⟨adj', hunit, ?_⟩
  intro a ha
  exact Adjunction.ext (ha.trans hunit.symm)

/-- The scalar adjunction on the actual slice, obtained from the tensor adjunction
and the universal derived comparison. No complete-object hypothesis is needed.
Source: Stacks Tags 03CZ, 09T5 and 0FND
(auxiliary; not a blueprint node). -/
def adicResidueScalarAdjunction (X : Scheme.{u})
    {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
    (U : coefficientProEtaleSiteModel.{u, v} X) (n : ℕ) :
    adicResidueLocalReduction.{u, v} X J U n ⊣
      dres (adicResidueLocalProjection.{u, v} X J U n) :=
  (adicResidueScalarAdjunction_existsUnique
    (adicResidueLocalProjection.{u, v} X J U n)).exists.choose

variable (X : Scheme.{u}) {A : Type (max v (u + 1))} [CommRing A] (J : Ideal A)
  (U : coefficientProEtaleSiteModel.{u, v} X)

private theorem homStep_naturality_left
    {T T' M : AdicResidueLocalDerived.{u, v} X J U} (a : T ⟶ T') (n : ℕ)
    (f : (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj T' ⟶
      (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M) :
    adicResidueHomStep.{u, v} X J U T M n
        ((adicResidueLocalReduction.{u, v} X J U (n + 1)).map a ≫ f) =
      (adicResidueLocalReduction.{u, v} X J U n).map a ≫
        adicResidueHomStep.{u, v} X J U T' M n f := by
  let V := (coefficientProEtaleModelTopology.{u, v} X).overPullback CommRingCat U
  let τ := V.map (transition (coefficientProEtaleModelTopology.{u, v} X) A J n)
  have h := congrArg
    (fun k ↦ k ≫ (extend τ).map f ≫
      (adicResidueLocalReductionStep.{u, v} X J U n).hom.app M)
    ((adicResidueLocalReductionStep.{u, v} X J U n).inv.naturality a).symm
  simpa only [adicResidueHomStep, adicResidueLocalReduction,
    CategoryTheory.Functor.map_comp, CategoryTheory.Functor.comp_map, Category.assoc,
    τ, V] using h

/-- The quotient successor is the adjoint of the reduction of the scalar counit.
This formula constructs the map; it does not choose a map from an existence theorem.
Source: Stacks Tags 03CZ, 09T5 and 09C6
(auxiliary; not a blueprint node). -/
def adicResidueAdjointStep (M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    (dres (adicResidueLocalProjection.{u, v} X J U (n + 1))).obj
        ((adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M) ⟶
      (dres (adicResidueLocalProjection.{u, v} X J U n)).obj
        ((adicResidueLocalReduction.{u, v} X J U n).obj M) :=
  (adicResidueScalarAdjunction.{u, v} X J U n).homEquiv _ _
    (adicResidueHomStep.{u, v} X J U _ M n
      ((adicResidueScalarAdjunction.{u, v} X J U (n + 1)).counit.app
        ((adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M)))

/-- Scalar transposes commute with the actual quotient successor.
Source: Stacks Tags 03CZ, 09T5 and 09C6
(auxiliary; not a blueprint node).
Proof: write a map as the scalar extension of its transpose followed by the counit.
Naturality of the balancing isomorphism moves the first factor out of HomStep;
naturality of the next scalar adjunction gives the asserted composite. -/
theorem adicResidueAdjointStep_transpose
    (T M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ)
    (f : (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj T ⟶
      (adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M) :
    (adicResidueScalarAdjunction.{u, v} X J U (n + 1)).homEquiv T _ f ≫
        adicResidueAdjointStep.{u, v} X J U M n =
      (adicResidueScalarAdjunction.{u, v} X J U n).homEquiv T _
        (adicResidueHomStep.{u, v} X J U T M n f) := by
  let a := (adicResidueScalarAdjunction.{u, v} X J U (n + 1)).homEquiv T _ f
  have hf : (adicResidueLocalReduction.{u, v} X J U (n + 1)).map a ≫
      (adicResidueScalarAdjunction.{u, v} X J U (n + 1)).counit.app
        ((adicResidueLocalReduction.{u, v} X J U (n + 1)).obj M) = f :=
    ((adicResidueScalarAdjunction.{u, v} X J U (n + 1)).homEquiv T _).symm_apply_apply f
  dsimp only [adicResidueAdjointStep]
  rw [← Adjunction.homEquiv_naturality_left]
  rw [← homStep_naturality_left, hf]

/-- The normalized scalar units commute with the constructed quotient successor.
Source: Stacks Tags 099M and 09C6
(auxiliary; not a blueprint node).
Proof: apply the proved transpose equation to the identity. The balancing isomorphism
cancels, so HomStep of the identity is the identity; its scalar transpose is the unit. -/
theorem adicResidueAdjointStep_unit
    (M : AdicResidueLocalDerived.{u, v} X J U) (n : ℕ) :
    (adicResidueScalarAdjunction.{u, v} X J U (n + 1)).unit.app M ≫
        adicResidueAdjointStep.{u, v} X J U M n =
      (adicResidueScalarAdjunction.{u, v} X J U n).unit.app M := by
  have hid : adicResidueHomStep.{u, v} X J U M M n (𝟙 _) = 𝟙 _ := by
    dsimp only [adicResidueHomStep, adicResidueLocalReduction]
    simp only [CategoryTheory.Functor.map_id]
    change (adicResidueLocalReductionStep.{u, v} X J U n).inv.app M ≫
      (𝟙 _ ≫ (adicResidueLocalReductionStep.{u, v} X J U n).hom.app M) = 𝟙 _
    rw [CategoryTheory.Category.id_comp, Iso.inv_hom_id_app]
  have h := adicResidueAdjointStep_transpose.{u, v} X J U M M n (𝟙 _)
  simpa only [hid, Adjunction.homEquiv_id] using h

/-- The constructed quotient tower in the common completed-coefficient category.
Source: Stacks Tags 099M and 09C6
(auxiliary; not a blueprint node). -/
def adicResidueAdjointTower (M : AdicResidueLocalDerived.{u, v} X J U) :
    ℕᵒᵖ ⥤ AdicResidueLocalDerived.{u, v} X J U :=
  Functor.ofOpSequence
    (X := fun n ↦ (dres (adicResidueLocalProjection.{u, v} X J U n)).obj
      ((adicResidueLocalReduction.{u, v} X J U n).obj M))
    (adicResidueAdjointStep.{u, v} X J U M)

end AlgebraicGeometry.Scheme

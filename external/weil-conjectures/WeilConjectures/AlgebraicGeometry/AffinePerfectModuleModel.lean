/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PerfectComplex
public import Mathlib.AlgebraicGeometry.Modules.Tilde
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.Algebra.Category.ModuleCat.Projective
import Mathlib.CategoryTheory.MorphismProperty.Retract

/-! # Module models of affine strictly perfect complexes

Source: Stacks Project, Tags 08CR and 06Z0.
(blueprint: lem-pc-affine-perfect-module-model).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme

/-- Associated sheaf on the spectrum, transported to the localized site of the affine open.
This is an actual functor, constructed from tilde, restriction, and the over equivalence. -/
noncomputable def affinePerfectSheafification (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) :
    ModuleCat.{u} (X.presheaf.obj (.op U)) ⥤
      SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U) :=
  tilde.functor (X.presheaf.obj (.op U)) ⋙
    Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse

/-- The affine sheafification functor preserves zero morphisms. -/
instance affinePerfectSheafification_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens)
    (hU : IsAffineOpen U) : (affinePerfectSheafification X U hU).PreservesZeroMorphisms := by
  let T := Modules.restrictFunctor hU.isoSpec.hom
  have : T.Additive := Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
  have : HasBinaryBiproducts (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts (Modules.overEquiv U).inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : (Modules.overEquiv U).inverse.Additive :=
    Functor.additive_of_preservesBinaryBiproducts _
  have : (tilde.functor (X.presheaf.obj (.op U))).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ tilde.map_zero⟩
  unfold affinePerfectSheafification
  infer_instance

private theorem counit_isIso_of_retract {C D : Type*} [Category* C] [Category* D]
    {F : C ⥤ D} {H : D ⥤ C} (adj : F ⊣ H) {V W : D}
    (r : Retract V W) [IsIso (adj.counit.app W)] : IsIso (adj.counit.app V) := by
  let rr : RetractArrow (adj.counit.app V) (adj.counit.app W) :=
    { i := Arrow.homMk ((H ⋙ F).map r.i) r.i (adj.counit.naturality r.i)
      r := Arrow.homMk ((H ⋙ F).map r.r) r.r (adj.counit.naturality r.r)
      retract := by ext <;> simp [← Functor.map_comp, r.retract] }
  exact (MorphismProperty.isomorphisms D).of_retract rr inferInstance

/-- A strictly perfect complex on an affine open is the sheafification of a K-projective
module complex, up to an actual complex isomorphism.
Source: Stacks Project, Tag 08CR, second proof, and Tag 06Z0, affine tilde/Gamma equivalence.
(blueprint: lem-pc-affine-perfect-module-model).

Proof: Transport K by the over equivalence and the affine spectrum isomorphism. Its terms
are retracts of finite free sheaves, so they are quasi-coherent. Apply global sections
termwise and transport the scalars through GammaSpecIso. Naturality of the affine counit
identifies the sheafification of this actual sections complex P with K as complexes.
Sections preserve the finite free retract equations; hence every P.X n is projective.
The same finite support bound holds because sections preserve zero objects. In particular
P is bounded above, and Mathlib's isKProjective_of_projective applies. This construction
also works for the empty affine open and the zero complex. -/
theorem affine_perfect_module_model (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U)
    (K : CochainComplex
      (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ)
    (hK : IsStrictlyPerfect X U K) :
    ∃ P : CochainComplex (ModuleCat.{u} (X.presheaf.obj (.op U))) ℤ,
      P.IsKProjective ∧
      Nonempty (((affinePerfectSheafification X U hU).mapHomologicalComplex (.up ℤ)).obj P
        ≅ K)  := by
  let R := X.presheaf.obj (.op U)
  let S := SheafOfModules.{u} (moduleRings (Spec R).toRingedSpace)
  let D := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)
  let rF := Modules.restrictFunctor hU.isoSpec.hom
  let rG := Modules.restrictFunctor hU.isoSpec.inv
  let e : S ≌ (U : Scheme.{u}).Modules := CategoryTheory.Equivalence.mk rF rG
    ((Modules.restrictFunctorId).symm ≪≫
      Modules.restrictFunctorCongr (by simp [R]) ≪≫
      Modules.restrictFunctorComp hU.isoSpec.inv hU.isoSpec.hom)
    ((Modules.restrictFunctorComp hU.isoSpec.hom hU.isoSpec.inv).symm ≪≫
      Modules.restrictFunctorCongr (by simp) ≪≫ Modules.restrictFunctorId)
  let E : S ≌ D := e.trans (Modules.overEquiv U).symm
  have : HasBinaryBiproducts S := HasBinaryBiproducts.of_hasBinaryProducts
  have : HasBinaryBiproducts D := HasBinaryBiproducts.of_hasBinaryProducts
  have : PreservesBinaryBiproducts E.functor :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : PreservesBinaryBiproducts E.inverse :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : E.functor.Additive := Functor.additive_of_preservesBinaryBiproducts _
  have : E.inverse.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let T := tilde.functor R
  let H := E.inverse ⋙ moduleSpecΓFunctor (R := R)
  let F := T ⋙ E.functor
  let adj : F ⊣ H := tilde.adjunction.comp E.toAdjunction
  have : H.IsRightAdjoint := adj.isRightAdjoint
  have : (moduleSpecΓFunctor (R := R)).PreservesZeroMorphisms :=
    ⟨fun _ _ ↦ rfl⟩
  have : H.PreservesZeroMorphisms := inferInstance
  have : PreservesBinaryBiproducts H := preservesBinaryBiproducts_of_preservesBinaryProducts _
  have : H.Additive := Functor.additive_of_preservesBinaryBiproducts _
  let P : CochainComplex (ModuleCat.{u} R) ℤ := (H.mapHomologicalComplex (.up ℤ)).obj K
  have hfree (m : ℕ) : Nonempty (F.obj
      (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) ≅
      SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
        (ULift.{u} (Fin m))) := by
    let unitIso := (Modules.overEquiv U).inverse.mapIso
      ((Modules.restrictUnitIso hU.isoSpec.hom) ≪≫
        Modules.overEquivFunctorObjUnitIso U) ≪≫
        ((Modules.overEquiv U).unitIso.app
          (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))).symm
    exact ⟨E.functor.mapIso (tildeFinsupp (ULift.{u} (Fin m))) ≪≫
      (SheafOfModules.mapFreeIso E.functor (ULift.{u} (Fin m)) unitIso.symm).symm⟩
  have hcounit (n : ℤ) : IsIso (adj.counit.app (K.X n)) := by
    obtain ⟨m, ι, π, hιπ⟩ := hK.2 n
    obtain ⟨ef⟩ := hfree m
    have := adj.isIso_counit_app_of_iso ef.symm
    exact counit_isIso_of_retract adj ⟨ι, π, hιπ⟩
  have hproj (n : ℤ) : Projective (P.X n) := by
    obtain ⟨m, ι, π, hιπ⟩ := hK.2 n
    obtain ⟨ef⟩ := hfree m
    let eH := H.mapIso ef.symm ≪≫ (asIso (adj.unit.app _)).symm
    have hm : Projective (ModuleCat.of R (ULift.{u} (Fin m) →₀ R)) :=
      ModuleCat.projective_of_categoryTheory_projective _
    have hp : Projective (H.obj
        (SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin m)))) := eH.retract.projective
            (p := by
              change Projective (ModuleCat.of R (ULift.{u} (Fin m) →₀ R))
              exact hm)
    exact (Retract.map (⟨ι, π, hιπ⟩ : Retract _ _) H).projective
  obtain ⟨a, b, hab⟩ := hK.1
  have : CochainComplex.IsStrictlyLE P b := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro n hn
    exact H.map_isZero (hab n (Or.inr hn))
  have : ∀ n : ℤ, Projective (P.X n) := hproj
  refine ⟨P, CochainComplex.isKProjective_of_projective P b, ⟨?_⟩⟩
  let ε := (NatTrans.mapHomologicalComplex adj.counit (.up ℤ)).app K
  have : IsIso ε := by
    have : ∀ n : ℤ, IsIso (ε.f n) := hcounit
    exact HomologicalComplex.Hom.isIso_of_components ε
  exact (asIso ε) ≪≫ (Functor.mapHomologicalComplexIdIso D (.up ℤ)).app K


end AlgebraicGeometry.Scheme

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Coefficient.DiagonalCoefficientReference
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRingComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Completed.CompletedCoefficientRootLineComparison
import WeilConjectures.AlgebraicGeometry.DiagonalCoefficients.Integral.DiagonalIntegralRootMap

/-! # Realizing completed coefficients as condensed coefficients

Source: the initial coefficient identification in diagonal tower coefficient changes.
(blueprint: lem-diagonal-completed-coefficient-realization).
-/

@[expose] public noncomputable section
set_option autoImplicit false
set_option genSizeOf false
set_option genInjectivity false
set_option synthInstance.maxSize 4096
universe u
open CategoryTheory CategoryTheory.Limits Opposite
open scoped CategoryTheory.Obj CategoryTheory.Functor
namespace AlgebraicGeometry.ProEtale.DiagonalCoefficients

attribute [local irreducible] upperStarFromPoint
  Scheme.purTwistZlCompletionOfUniverses
  InternalAbelianSheafModule.sectionModuleEquivalenceCore

private theorem counit_preimage_cancel
    {C D A : Type*} [Category C] [Category D] [Category A]
    (E : C ≌ D) (U : D ⥤ A) (M : D) (N : C) (s : M ≅ E.functor.obj N) :
    U.map (E.counitIso.inv.app M) ≫
      U.map (E.functor.map
        (E.fullyFaithfulFunctor.preimageIso (E.counitIso.app M ≪≫ s)).hom) =
      U.map s.hom := by
  rw [Functor.FullyFaithful.preimageIso_hom, E.fullyFaithfulFunctor.map_preimage]
  rw [← U.map_comp]
  congr 1
  exact (Iso.inv_hom_id_assoc (E.counitIso.app M) s.hom)

private def restrictionRoundTrip
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.restrictScalars.{u + 1} c.hom ⋙
      SheafOfModules.restrictScalars c.inv ≅ 𝟭 (SheafOfModules.{u + 1} S) :=
  NatIso.ofComponents (fun M ↦ (SheafOfModules.fullyFaithfulForget S).preimageIso
    (PresheafOfModules.isoMk (fun U ↦
      (ModuleCat.restrictScalarsComp'App (c.inv.hom.app U).hom
        (c.hom.hom.app U).hom (RingHom.id _) (by
          have h := congr_app (congrArg (fun f : S ⟶ S ↦ f.hom) c.inv_hom_id) U
          exact (congrArg RingCat.Hom.hom h).symm) (M.val.obj U)).symm ≪≫
        ModuleCat.restrictScalarsId'App (RingHom.id _) rfl (M.val.obj U))
      (by intro U V f; ext x; rfl)))
    (by intro M N f; ext U x; rfl)

private def restrictionEquivalence
    {C : Type (u + 1)} [Category.{u} C] {J : GrothendieckTopology C}
    {R S : Sheaf J RingCat.{u + 1}} (c : R ≅ S) :
    SheafOfModules.{u + 1} S ≌ SheafOfModules.{u + 1} R where
  functor := SheafOfModules.restrictScalars c.hom
  inverse := SheafOfModules.restrictScalars c.inv
  unitIso := (restrictionRoundTrip c).symm
  counitIso := restrictionRoundTrip c.symm
  functor_unitIso_comp M := by ext U x; rfl

private def sectionUnitIso (l : ℕ) [Fact l.Prime] (X : Scheme.{u})
    (e : (sheafCompose (Scheme.ProEt.topology X)
        (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
          (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
            (Scheme.ProEt.topology X)
            (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) ≅
        Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)) :
    (SheafOfModules.restrictScalars e.hom).obj
        (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≅
      (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
        (Scheme.ProEt.topology X)
        (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).functor.obj
          (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)) := by
  refine (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U ↦ ?_) ?_)
  · let M := (SheafOfModules.restrictScalars e.hom).obj
      (SheafOfModules.unit (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))
    let N := (InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
      (Scheme.ProEt.topology X)
      (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X)).functor.obj
        (Mod.regular (condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X))
    refine (show M.val.obj U ≃ₗ[_] N.val.obj U from
      { toFun := e.inv.hom.app U
        invFun := e.hom.hom.app U
        left_inv := fun x ↦ ConcreteCategory.congr_hom
          (congr_app (congrArg (fun f ↦ f.hom) e.inv_hom_id) U) x
        right_inv := fun x ↦ ConcreteCategory.congr_hom
          (congr_app (congrArg (fun f ↦ f.hom) e.hom_inv_id) U) x
        map_add' := map_add _
        map_smul' := ?_ }).toModuleIso
    intro r x
    let x' : (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)).obj.obj U := x
    change e.inv.hom.app U (e.hom.hom.app U r * x') = r * e.inv.hom.app U x'
    rw [map_mul]
    congr 1
    exact ConcreteCategory.congr_hom
      (congr_app (congrArg (fun f ↦ f.hom) e.hom_inv_id) U) r
  · intro U V f
    ext x
    exact ConcreteCategory.congr_hom (e.inv.hom.naturality f) x

/-- The completed coefficient category has an exact condensed realization, with
its underlying sheaf, regular module, and root-limit normalizations.

Source: blueprint latest, sec-six-functors-basics/sk-prop-diagonal-tower/
sk-prop-diagonal-tower-coefficients.proof.md, paragraph (1), using the integral
comparison in lemma-comparison-completed-coefficients.
(blueprint: lem-diagonal-completed-coefficient-realization).

Proof: the completed ring and the pulled-back condensed Z_l ring are limits of
canonically identified finite constant rings. Their projections give a ring
isomorphism. Apply the internal/sectionwise module equivalence and transport
scalars by this ring isomorphism. Both operations are exact equivalences and
preserve the underlying abelian sheaf. The image of the regular module is the
regular module, with normalization checked after every finite ring projection.
The completed Tate module and the integral condensed line are limits of the
same finite root modules. Their projection maps determine the line comparison;
its underlying map is the root-limit comparison followed by the free-module
units. These maps commute with the power transitions. Invertibility of l makes
the root modules invertible locally, so these comparisons are isomorphisms. -/
theorem completedCoefficientRealization_exists (l : ℕ) [Fact l.Prime]
    (X : Scheme.{u}) [IsNoetherian X] (hX : IsUnit (l : Γ(X, ⊤))) :
    Nonempty (CompletedRealization l X) := by
  obtain ⟨e, he, _⟩ := completedCoefficientRingComparison_existsUnique l X
  obtain ⟨roots⟩ := Nonempty.intro (diagonalIntegralRoots l X (bottomField l))
  obtain ⟨s, hs⟩ := completedCoefficientRootLineComparison_exists l X hX e he roots
  let R := condensedRingObj (Profinite.continuousMapRingObj.{u} ℤ_[l]) X
  let E := InternalAbelianSheafModule.sectionModuleEquivalence.{u + 1, u + 1, u}
    (Scheme.ProEt.topology X) R
  let H := (restrictionEquivalence e).functor
  let F := H ⋙ E.inverse
  have : E.functor.Additive :=
    { map_add := by intros; ext U x; rfl }
  have : E.inverse.Additive := inferInstance
  have : H.Additive := inferInstanceAs (SheafOfModules.restrictScalars e.hom).Additive
  have : F.Additive := inferInstance
  have : F.IsEquivalence := inferInstance
  let U := SheafOfModules.toSheaf
    ((sheafCompose (Scheme.ProEt.topology X)
      (forget₂ CommRingCat.{u + 1} RingCat.{u + 1})).obj
        (InternalAbelianSheafModule.sectionRingSheaf.{u + 1, u + 1, u}
          (Scheme.ProEt.topology X) R))
  let underlying : F ⋙ Mod.forget R ≅
      diagonalCompletedRestriction l X ⋙ diagonalForget l X :=
    NatIso.ofComponents (fun M ↦ U.mapIso (E.counitIso.app (H.obj M))) (by
      intro M N f
      exact congrArg U.map (E.counitIso.hom.naturality (H.map f)))
  let unitIso := E.fullyFaithfulFunctor.preimageIso
    (E.counitIso.app (H.obj (SheafOfModules.unit
      (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l)))) ≪≫ sectionUnitIso l X e)
  let lineIso := E.fullyFaithfulFunctor.preimageIso
    (E.counitIso.app (H.obj (Scheme.purTwistZlModule X l)) ≪≫ s)
  refine ⟨{ F := F
            underlying := underlying
            unitIso := unitIso
            unit_normalization := ?_
            lineIso := lineIso
            roots := roots
            line_normalization := ?_ }⟩
  · intro n
    apply heq_of_eq
    have hu : underlying.inv.app (SheafOfModules.unit
        (Scheme.purTwistRing X (Scheme.purTwistZlCompletion X l))) ≫ unitIso.hom.hom =
        U.map (sectionUnitIso l X e).hom := by
      exact counit_preimage_cancel E U _ (Mod.regular R) (sectionUnitIso l X e)
    rw [← Category.assoc, hu]
    have hu' : U.map (sectionUnitIso l X e).hom =
        (sheafCompose (Scheme.ProEt.topology X)
          (forget₂ RingCat.{u + 1} Ab.{u + 1})).map e.inv := by
      ext V x
      rfl
    rw [hu']
    exact he n
  · apply heq_of_eq
    exact (counit_preimage_cancel E U _ (zlLine l X) s).trans hs

end AlgebraicGeometry.ProEtale.DiagonalCoefficients

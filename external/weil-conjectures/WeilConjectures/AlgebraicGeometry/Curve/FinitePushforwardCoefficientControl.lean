/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.CurveCoefficientPair
public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
public import Mathlib.Algebra.Category.Grp.ZModuleEquivalence
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.AlgebraicGeometry.Morphisms.Finite
import WeilConjectures.AlgebraicGeometry.Curve.FinitePushforwardConstructibleDescent
import WeilConjectures.AlgebraicGeometry.ConstructibleIntegralCoefficients
import WeilConjectures.AlgebraicGeometry.TorsionSheafCharacterizations
import WeilConjectures.SixFunctors.Finite.Stalk

/-! # Coefficient hypotheses for finite direct images

Source: Stacks Project, Lemma 0A5D and Tags 03QP, 095G, 09BH.
(blueprint: g1-finite-pushforward-coefficient-control)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The finite direct-image counit is stalkwise a split product projection. -/
private theorem finite_counit_epi {X Y : Scheme.{u}} (f : X ⟶ Y) [IsFinite f]
    (Λ : Type (u + 1)) [CommRing Λ]
    (F : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) :
    Epi ((Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F) := by
  classical
  have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} (ModuleCat.{u + 1} Λ) :=
    CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
  let beta := (Etale.upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) f).counit.app F
  have hstalk (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (s : Spec (.of Ω) ⟶ X) :
      Epi ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
    let D := fun t : Scheme.Hom.GeometricFiber f (s ≫ f) ↦
      (Scheme.pointSmallEtale t.1).sheafFiber.obj F
    have : CategoryTheory.Limits.HasLimit (Discrete.functor D) :=
      CategoryTheory.Limits.HasLimitsOfShape.has_limit _
    have hrestrict : Epi (Etale.stalkRestrict (ModuleCat.{u + 1} Λ) f
        (s ≫ f) ⟨s, rfl⟩ F) := by
      have he : (Etale.stalkIsoPi (ModuleCat.{u + 1} Λ) f (s ≫ f) F).hom ≫
          CategoryTheory.Limits.Pi.π D ⟨s, rfl⟩ = _ :=
        CategoryTheory.Limits.Pi.lift_comp_π _ _
      rw [← he]
      infer_instance
    exact epi_of_epi_fac
      (Etale.stalkRestrict_eq_counit (ModuleCat.{u + 1} Λ) f s F).symm
  have : LocallySmall.{u + 1} X.Etale := locallySmall_max.{u + 1} (C := X.Etale)
  let hpoints := Scheme.isConservativeFamilyOfPoints_ulift_pointSmallEtale X
  apply (hpoints.jointlyReflectEpimorphisms (ModuleCat.{u + 1} Λ)).epi_iff beta |>.mpr
  rintro ⟨-, ⟨x⟩⟩
  let e := (Scheme.pointSmallEtale (X.algClosurePoint x)).uliftSheafFiberIso.{u + 1}
    (ModuleCat.{u + 1} Λ)
  have := hstalk _ (X.algClosurePoint x)
  let Φ := Scheme.pointSmallEtale (X.algClosurePoint x)
  change Epi ((Φ.ulift.{u + 1}).sheafFiber.map beta)
  rw [← epi_comp_iff_of_isIso _ (e.hom.app F)]
  change Epi (((Scheme.pointSmallEtale (X.algClosurePoint x)).ulift.{u + 1}).sheafFiber.map
    beta ≫ e.hom.app F)
  erw [e.hom.naturality beta]
  infer_instance

/-- Coefficient hypotheses descend from finite direct image.
Source: Stacks Project, Lemma 0A5D (lemma-finite-pushforward-statements), the primary-part
argument and the constructibility converse supplied by Tags 03QP, 095G and 09BH
(blueprint: g1-finite-pushforward-coefficient-control).

Proof:
1. The finite stalk formula identifies each source stalk with a direct factor of the
   direct-image stalk at its image. The projection is surjective: extend an element by
   zero in the other factors. Thus an annihilating power of p, or a positive integer
   invertible on Spec k, for the extended element also annihilates its projection.
   This proves the first and third clauses, including p = 0 and p = 1. For a separably
   closed point, extend its field to an algebraic closure; this purely inseparable
   extension induces the same geometric stalk, so the argument applies to the points
   used by the recorded predicates as well.
2. For constructibility, first forget the ULift Z action. A finitely generated torsion
   Z-module is finite, so finite local constancy in the module predicate is precisely
   finite local constancy of the underlying abelian sheaf. The equivalence with modules
   preserves pullback and these local trivializations. Use the same stratifications to
   identify this condition with (fun P : AlgebraicGeometry.CurveCoefficientPair k ↦
    (Scheme.IsConstructibleEtaleSheafOfSets
      ((sheafCompose P.C.smallEtaleTopology
        (CategoryTheory.forget AddCommGrpCat.{u + 1})).obj P.F))).
3. Apply CurveCoefficientPair.isConstructible_of_finite_pushforward to these abelian
   sheaves. Its torsion hypothesis holds by the finite stalk formula and the torsion
   characterization. Concretely, the counit is surjective on stalks, being projection
   to the selected factor, so the source sheaf is a quotient of the pullback of its
   constructible direct image. On Noetherian curves, pullback and torsion quotients
   preserve constructibility. Finally apply the coefficient equivalence to the source
   stratification to recover the module predicate. The equivalence adds no module data
   beyond the canonical Z action and preserves the underlying additive stalks. -/
theorem IsCurve.finite_pushforward_coefficient_control {k : Type u} [Field k] [IsAlgClosed k]
    (P : CurveCoefficientPair k) {Y : Scheme.{u}}
    (g : Y ⟶ Spec (.of k)) [IsCurve g] (f : P.C ⟶ Y) [IsFinite f]
    (hf : f ≫ g = P.toSpec) :
    let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
      ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
    let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
    let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
    let FY := (sheafCompose Y.smallEtaleTopology E).obj G
    (∀ p : ℕ, Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FY p →
        Scheme.IsPrimaryTorsionSheaf (ULift.{u + 1} ℤ) FX p) ∧
      (Scheme.IsConstructibleSheaf FY → Scheme.IsConstructibleSheaf FX) ∧
      (Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FY →
        Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k)) FX) := by
  classical
  dsimp only
  let E := (forget₂ (ModuleCat.{u + 1} ℤ) AddCommGrpCat.{u + 1}).inv ⋙
    ModuleCat.restrictScalars (ULift.ringEquiv : ULift.{u + 1} ℤ ≃+* ℤ).toRingHom
  let FX := (sheafCompose P.C.smallEtaleTopology E).obj P.F
  let G := (Etale.lowerStar AddCommGrpCat.{u + 1} f).obj P.F
  let FY := (sheafCompose Y.smallEtaleTopology E).obj G
  let beta := (Etale.upperStarLowerStarAdjunction
    (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).counit.app FX
  have : Epi beta := finite_counit_epi f _ FX
  have hsurj (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ P.C) :
      Function.Surjective ((Scheme.pointSmallEtale s).sheafFiber.map beta) := by
    have : CategoryTheory.Limits.HasLimitsOfSize.{u, u}
        (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) :=
      CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
    have : ((Scheme.pointSmallEtale s).sheafFiber
        (A := ModuleCat.{u + 1} (ULift.{u + 1} ℤ))).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction
        ((Scheme.pointSmallEtale s).skyscraperSheafAdjunction)
    exact (ModuleCat.epi_iff_surjective _).mp inferInstance
  refine ⟨?_, ?_, ?_⟩
  · intro p h Ω _ _ s x
    obtain ⟨z, rfl⟩ := hsurj Ω s x
    let e := ((Etale.upperStarCompSheafFiberIso
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f s).app
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj FX)).toLinearEquiv
    change Scheme.IsPrimaryTorsionSheaf _
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj FX) p at h
    obtain ⟨n, hn⟩ := h Ω (s ≫ f) (e z)
    have hz : p ^ n • z = 0 := e.injective (by
      simpa only [map_nsmul, map_zero] using hn)
    refine ⟨n, ?_⟩
    simpa only [map_nsmul, map_zero] using
      congrArg ((Scheme.pointSmallEtale s).sheafFiber.map beta).hom hz
  · intro h
    have hT : Y.IsTorsionAbelianSheaf G := by
      classical
      have : CategoryTheory.Limits.HasLimitsOfSize.{u, u} AddCommGrpCat.{u + 1} :=
        CategoryTheory.Limits.hasLimitsOfSizeShrink.{u, u, u + 1, u + 1} _
      apply (Scheme.isTorsionAbelianSheaf_characterizations _).2.mpr
      intro Ω inst inst' y
      let T := Scheme.Hom.GeometricFiber f y
      let M := fun t : T ↦
        ((Scheme.pointSmallEtale t.1).sheafFiber (A := AddCommGrpCat.{u + 1})).obj P.F
      have : CategoryTheory.Limits.HasLimit (Discrete.functor M) :=
        CategoryTheory.Limits.HasLimitsOfShape.has_limit _
      have : Small.{u + 1} (Discrete T) := small_max.{u + 1} _
      have : CategoryTheory.Limits.PreservesLimitsOfShape (Discrete T)
          (forget AddCommGrpCat.{u + 1}) :=
        AddCommGrpCat.forget_preservesLimitsOfShape.{u, u + 1, u} (J := Discrete T)
      let e := Etale.stalkIsoPi AddCommGrpCat.{u + 1} f y P.F
      let φ : ((Scheme.pointSmallEtale y).sheafFiber (A := AddCommGrpCat.{u + 1})).obj G →+
          (∀ t : T, M t) :=
        { toFun := fun x t ↦ Etale.stalkRestrict AddCommGrpCat.{u + 1} f y t P.F x
          map_zero' := by funext t; exact map_zero _
          map_add' := by intro x z; funext t; exact map_add _ _ _ }
      have hφ : Function.Injective φ := by
        intro x z hxz
        apply (ConcreteCategory.bijective_of_isIso e.hom).1
        apply CategoryTheory.Limits.Concrete.limit_ext
        intro t
        change (e.hom ≫ CategoryTheory.Limits.Pi.π M t.as) x =
          (e.hom ≫ CategoryTheory.Limits.Pi.π M t.as) z
        dsimp only [e]
        rw [Etale.stalkIsoPi_hom]
        erw [CategoryTheory.Limits.Pi.lift_comp_π]
        exact congrFun hxz t.as
      intro x
      apply hφ.isOfFinAddOrder_iff.mp
      apply IsOfFinAddOrder.pi
      intro t
      exact (Scheme.isTorsionAbelianSheaf_characterizations P.F).2.mp
        
          ((Scheme.isTorsionAbelianSheaf_characterizations
            P.F).1.mpr P.isTorsion) Ω t.1 (φ x t)
    have hC := (Scheme.isConstructibleSheaf_integral_iff G hT).mp h
    have hP := CurveCoefficientPair.isConstructible_of_finite_pushforward P g f hf hT hC
    exact (Scheme.isConstructibleSheaf_integral_iff P.F 
      ((Scheme.isTorsionAbelianSheaf_characterizations
        P.F).1.mpr P.isTorsion)).mpr hP
  · intro h
    change Scheme.IsTorsionSheafOfInvertibleOrder (Spec (.of k))
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj FX) at h
    let := h
    constructor
    intro Ω _ _ s x
    obtain ⟨z, rfl⟩ := hsurj Ω s x
    let e := ((Etale.upperStarCompSheafFiberIso
      (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f s).app
      ((Etale.lowerStar (ModuleCat.{u + 1} (ULift.{u + 1} ℤ)) f).obj FX)).toLinearEquiv
    obtain ⟨n, hn, hu, he⟩ :=
      Scheme.IsTorsionSheafOfInvertibleOrder.exists_isUnit_nsmul_eq_zero
        (S := Spec (.of k)) Ω (s ≫ f) (e z)
    have hz : n • z = 0 := e.injective (by
      simpa only [map_nsmul, map_zero] using he)
    refine ⟨n, hn, hu, ?_⟩
    simpa only [map_nsmul, map_zero] using
      congrArg ((Scheme.pointSmallEtale s).sheafFiber.map beta).hom hz

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import WeilConjectures.Algebra.Homology.ModuleStalkFunctor
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
import WeilConjectures.Mathlib.AlgebraicGeometry.Modules.Sheaf
import WeilConjectures.AlgebraicGeometry.SquareZeroStalkCoefficientsSpread
import WeilConjectures.AlgebraicGeometry.AffineFreeSheafStalkRealization

/-! # A bounded free complex on an affine neighbourhood of a stalk

Source: Stacks Project, Tags 0BCD, 0BC7 and 00CR, finite-matrix spreading.
(blueprint: lem-sc-bounded-free-stalk-complex-local-lift).
-/

@[expose] public section

universe u
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme
noncomputable section

/-- Ordinary direct image on an open preserves zero morphisms sectionwise.
Source: the definition of module direct image in the direct-image step of
lem-sc-bounded-free-stalk-complex-local-lift. -/
instance openModuleDirectImage_preservesZeroMorphisms (X : Scheme.{u}) (U : X.Opens) :
    Functor.PreservesZeroMorphisms (SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U)) where
  map_zero M N := by
    ext V m
    rfl

private theorem affineSheafification_coordinate_free
    (X : Scheme.{u}) (U : X.Opens) (hU : IsAffineOpen U) (n : ℕ) :
    Nonempty ((affinePerfectSheafification X U hU).obj
      (ModuleCat.of Γ(X, U) (ULift.{0} (Fin n → Γ(X, U)))) ≅
        SheafOfModules.free (R := (moduleRings X.toRingedSpace).over U)
          (ULift.{u} (Fin n))) := by
  let R := Γ(X, U)
  let e : ULift.{0} (Fin n → R) ≃ₗ[R] (ULift.{u} (Fin n) →₀ R) :=
    (ULift.moduleEquiv.trans (Finsupp.linearEquivFunOnFinite R R (Fin n)).symm).trans
      (Finsupp.domLCongr (Equiv.ulift.symm : Fin n ≃ ULift.{u} (Fin n)))
  let H := Modules.restrictFunctor hU.isoSpec.hom ⋙ (Modules.overEquiv U).inverse
  have : PreservesColimitsOfSize.{u, u} (Modules.overEquiv U).inverse :=
    (Modules.overEquiv U).symm.toAdjunction.leftAdjoint_preservesColimits
  have : PreservesColimitsOfSize.{u, u} H := by
    dsimp [H]
    infer_instance
  let unitIso := (Modules.overEquiv U).inverse.mapIso
    ((Modules.restrictUnitIso hU.isoSpec.hom) ≪≫
      Modules.overEquivFunctorObjUnitIso U) ≪≫
      ((Modules.overEquiv U).unitIso.app
        (SheafOfModules.unit ((moduleRings X.toRingedSpace).over U))).symm
  refine ⟨(affinePerfectSheafification X U hU).mapIso e.toModuleIso ≪≫
    H.mapIso (tildeFinsupp (ULift.{u} (Fin n))) ≪≫ ?_⟩
  exact (SheafOfModules.mapFreeIso H (ULift.{u} (Fin n)) unitIso.symm).symm

/-- The affine-local part of bounded free stalk-complex lifting.

Source: Stacks Project, Tags 0BCD and 0BC7 (finite-presentation spreading),
and Algebra Tag 00CR. The stalk of a sheaf on the open is expressed using ordinary
open direct image followed by the ambient stalk functor; no global boundedness or
restriction comparison is asserted here.
(blueprint: lem-sc-bounded-free-stalk-complex-local-lift).

Proof:
1. Use hterms to identify every term with its standard rank-d i free module.
   Express each differential in the standard bases. The hypothesis hd makes all
   ranks zero outside [a,b], so only finitely many matrices have any entries.
2. Choose an affine neighbourhood V of x. Its stalk is the localization of its
   section ring at the prime corresponding to x. Every entry of the finitely many
   matrices is a fraction with denominator outside that prime. Multiply these
   denominators to obtain a principal affine neighbourhood where all entries lift.
3. Each composite of consecutive matrices has zero germ. Every one of its finitely
   many entries therefore vanishes after multiplication by an element outside the
   prime. Shrink again using the product of these elements. The lifted matrices
   now square to zero, and define the differentials between the rank-d i free
   sheaves on the resulting affine open U. Outside [a,b] take the zero differentials;
   rank zero gives zero sheaves there, so the resulting complex L is bounded.
4. The stalks of finite free sheaves have their standard finite bases. The chosen
   bases of F identify them with these stalks and commute with the differentials
   by the definition of the lifted matrices, giving an isomorphism of complexes.
   In the ambient direct image, neighbourhoods contained in U are cofinal at x;
   this identifies that stalk with the local one, compatibly with scalar action
   and differentials, and yields the displayed isomorphism.
For an empty degree interval every rank is zero, so there are no coefficients or
relations to lift. No point exists on an empty scheme; rank-zero terms introduce
no coefficients. Nothing assumes that the open immersion is quasi-compact.
-/
theorem exists_boundedFree_stalk_complex_local_lift
    (X : Scheme.{u}) (x : X) (d : ℤ → ℕ)
    (F : CochainComplex (ModuleCat.{u} (X.presheaf.stalk x)) ℤ)
    (hterms : ∀ i : ℤ, F.X i = ModuleCat.of (X.presheaf.stalk x)
      (ULift.{0} (Fin (d i) → X.presheaf.stalk x)))
    (a b : ℤ) (hd : ∀ i : ℤ, i < a ∨ b < i → d i = 0) :
    ∃ U : X.Opens, x ∈ U ∧ IsAffineOpen U ∧
      ∃ L : CochainComplex
          (SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U)) ℤ,
        (∀ i : ℤ, i < a ∨ b < i → IsZero (L.X i)) ∧
        (∀ i : ℤ, Nonempty (L.X i ≅ SheafOfModules.free
          (R := (moduleRings X.toRingedSpace).over U) (ULift.{u} (Fin (d i))))) ∧
        Nonempty (F ≅
          (((SheafOfModules.pushforward.{u}
              (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
            RingedSpace.moduleStalkFunctor X.toRingedSpace x).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj L)) := by
  classical
  let E (i : ℤ) : ModuleCat.{u} (X.presheaf.stalk x) :=
    ModuleCat.of (X.presheaf.stalk x) (ULift.{0} (Fin (d i) → X.presheaf.stalk x))
  let eF (i : ℤ) : F.X i ≅ E i := eqToIso (hterms i)
  let δ (i : ℤ) : E i ⟶ E (i + 1) :=
    (eF i).inv ≫ F.d i (i + 1) ≫ (eF (i + 1)).hom
  have hδ (i : ℤ) : δ i ≫ δ (i + 1) = 0 := by
    simp only [δ, Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc (F.d i (i + 1)), F.d_comp_d, zero_comp, comp_zero]
  obtain ⟨U, hxU, hU, D, hD, hcoeff⟩ :=
    exists_squareZero_stalk_coefficients_spread X x d a b hd δ hδ
  obtain ⟨e, he⟩ :=
    exists_affine_freeSheaf_stalk_realization X x U hxU hU
  let Φ := affinePerfectSheafification X U hU
  let C := CochainComplex.of
    (fun i : ℤ ↦ ModuleCat.of Γ(X, U) (ULift.{0} (Fin (d i) → Γ(X, U)))) D hD
  let L := (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj C
  let T := SheafOfModules.pushforward.{u}
      (SheafOfModules.pushforwardOver (R := moduleRings X.toRingedSpace) U) ⋙
    RingedSpace.moduleStalkFunctor X.toRingedSpace x
  refine ⟨U, hxU, hU, L, ?_, ?_, ?_⟩
  · intro i hi
    apply Φ.map_isZero
    change IsZero (ModuleCat.of Γ(X, U) (ULift.{0} (Fin (d i) → Γ(X, U))))
    rw [hd i hi]
    exact ModuleCat.isZero_of_subsingleton _
  · intro i
    exact affineSheafification_coordinate_free X U hU (d i)
  · refine ⟨HomologicalComplex.Hom.isoOfComponents (fun i ↦ eF i ≪≫ e (d i)) ?_⟩
    intro i j hij
    obtain rfl : i + 1 = j := hij
    change (eF i).hom ≫ (e (d i)).hom ≫ T.map (Φ.map (C.d i (i + 1))) =
      F.d i (i + 1) ≫ (eF (i + 1)).hom ≫ (e (d (i + 1))).hom
    simp only [C, CochainComplex.of_d]
    rw [he (d i) (d (i + 1)) (D i) (δ i) (hcoeff i)]
    simp [δ, Category.assoc]


end
end AlgebraicGeometry.Scheme

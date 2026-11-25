/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.PseudoCoherentComplex
public import Mathlib.AlgebraicGeometry.AffineScheme
import WeilConjectures.AlgebraicGeometry.PseudoCoherentQCoh
import WeilConjectures.AlgebraicGeometry.AffineOpenLocalizedModel
import WeilConjectures.RingTheory.FiniteLocalizationFreeModel
import WeilConjectures.AlgebraicGeometry.QcOpenDerivedLift

/-! # Lifting pseudo-coherent objects from quasi-compact opens of affine schemes

Source: Stacks Project, Derived Categories of Schemes, Tag 08EE,
Lemma 36.13.3, lemma-lift-pseudo-coherent (blueprint: lem-sc-affine-pseudo-coherent-lift).
-/

@[expose] public section

set_option autoImplicit false

universe u w

open CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.Scheme

attribute [local instance] Functor.additive_of_preserves_binary_products
  comp_preservesFiniteLimits comp_preservesFiniteColimits

set_option backward.isDefEq.respectTransparency false in
/-- A pseudo-coherent derived object on a quasi-compact open of an affine scheme has a
bounded-above finite-free complex on the whole scheme representing it after restriction.
The ranks may vary with the degree, and the complex need not be bounded below.
Source: Stacks Project, Tag 08EE, lemma-lift-pseudo-coherent
(blueprint: lem-sc-affine-pseudo-coherent-lift).

Proof:
1. PseudoCoherentQCoh makes E quasi-coherent. QcOpenDerivedLift supplies a
   quasi-coherent E' on X and an isomorphism E' restricted to U ≅ E.
2. Construct T by associating sheaves on Spec Gamma(X) and restricting along
   X.isoSpec.hom. AffineOpenLocalizedModel gives a module complex M representing
   E', a finite family of pseudo-coherent localizations, and detection of
   quasi-isomorphisms after restriction to U.
3. FiniteLocalizationFreeModel performs the descending cone construction and
   denominator clearing, giving a bounded-above finite-free F and a chain map
   F → M which is a quasi-isomorphism at each of those localizations.
4. Apply T termwise. T preserves zero objects, hence the upper bound. A finite
   basis of each term, tildeFinsupp, and mapFreeIso identify its associated sheaf
   with a finite free sheaf of the same rank.
5. The detection clause makes the derived restriction of the map T(F) → T(M)
   invertible. Compose its isomorphism with the restriction of Q(T(M)) ≅ E'
   and with E' restricted to U ≅ E.
-/
theorem exists_boundedAbove_finiteFree_lift
    (X : Scheme.{u}) [IsAffine X] (U : X.Opens) (hU : IsCompact (U : Set X))
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))]
    [∀ V : U.toScheme.Opens,
      HasDerivedCategory.{w}
        (SheafOfModules.{u} ((moduleRings U.toScheme.toRingedSpace).over V))]
    (E : schemeDerivedCategory U.toScheme) (hE : IsPseudoCoherent U.toScheme E) :
    ∃ P : CochainComplex (SheafOfModules.{u} (moduleRings X.toRingedSpace)) ℤ,
      (∃ N : ℤ, ∀ i : ℤ, N < i → IsZero (P.X i)) ∧
      (∀ i : ℤ, ∃ r : ℕ, Nonempty (P.X i ≅ SheafOfModules.free
        (R := moduleRings X.toRingedSpace) (ULift.{u} (Fin r)))) ∧
      Nonempty
        (((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
          Equivalence.functor
            (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
            (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
            (Modules.overEquiv U)).mapDerivedCategory.obj (DerivedCategory.Q.obj P) ≅ E) := by
  classical
  let A := X.presheaf.obj (.op ⊤)
  let G := Modules.restrictFunctor X.isoSpec.hom
  have : G.Additive := Functor.additive_of_iso (Modules.restrictFunctorIsoPullback _).symm
  have : (tilde.functor A).PreservesZeroMorphisms := ⟨fun _ _ ↦ tilde.map_zero⟩
  let T := tilde.functor A ⋙ G
  let TC := T.mapHomologicalComplex (ComplexShape.up ℤ)
  let R := ((SheafOfModules.overFunctor.{u} (moduleRings X.toRingedSpace) U) ⋙
    Equivalence.functor
      (C := SheafOfModules.{u} ((moduleRings X.toRingedSpace).over U))
      (D := SheafOfModules.{u} (moduleRings U.toScheme.toRingedSpace))
      (Modules.overEquiv U)).mapDerivedCategory
  let E₀ : schemeDerivedQCohCategory U.toScheme :=
    ⟨E, schemeDerivedQCohProperty_of_isPseudoCoherent U.toScheme E hE⟩
  obtain ⟨E', ⟨e⟩⟩ := exists_qc_derived_lift_of_isCompact_open X U hU E₀
  let : ∀ f : A, HasDerivedCategory.{u + 1} (ModuleCat.{u} (Localization.Away f)) :=
    fun _ ↦ HasDerivedCategory.standard _
  obtain ⟨M, r, f, hlocal, ⟨eM⟩, hdetect⟩ :=
    exists_affine_open_localized_model X U hU T ⟨Iso.refl _⟩ E' E hE ⟨e⟩
  obtain ⟨F, b, hbound, hfree, α, hα⟩ :=
    DerivedCategory.exists_finite_localization_free_model A M r f hlocal
  have : F.IsStrictlyLE b := hbound
  refine ⟨TC.obj F, ⟨b, ?_⟩, ?_, ?_⟩
  · intro i hi
    exact T.map_isZero (F.isZero_of_isStrictlyLE b i hi)
  · intro i
    have : Module.Free A (F.X i) := (hfree i).1
    have : Module.Finite A (F.X i) := (hfree i).2
    let r := Fintype.card (Module.Free.ChooseBasisIndex A (F.X i))
    let basis := (Module.Free.chooseBasis A (F.X i)).reindex
      ((Fintype.equivFin _).trans (Equiv.ulift.symm : Fin r ≃ ULift.{u} (Fin r)))
    let eF := (tilde.functor A).mapIso basis.repr.toModuleIso ≪≫
      tildeFinsupp (R := A) (ULift.{u} (Fin r))
    refine ⟨r, ⟨G.mapIso eF ≪≫ ?_⟩⟩
    exact (SheafOfModules.mapFreeIso G (ULift.{u} (Fin r))
      (Modules.restrictUnitIso X.isoSpec.hom).symm).symm
  · have : IsIso (R.map (DerivedCategory.Q.map (TC.map α))) := hdetect F α hα
    exact ⟨asIso (R.map (DerivedCategory.Q.map (TC.map α))) ≪≫ R.mapIso eM ≪≫ e⟩

end AlgebraicGeometry.Scheme

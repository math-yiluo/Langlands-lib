/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.AlgebraicGeometry.Morphisms.Smooth
public import WeilConjectures.SixFunctors.Etale.Derived.Dualizing
public import WeilConjectures.SixFunctors.Etale.Derived.UpperShriekCanonicalMaps
import WeilConjectures.AlgebraicGeometry.SfAffineLineCanonicalDuality
import WeilConjectures.AlgebraicGeometry.SfEtaleUnitTensorArbitraryBase
import WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality.AffineSpace

/-!
# Smooth duality from the étale and affine-line cases

`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor_of_finite` has the statement of
`proposition-exceptional-inverse-image-smooth-morphism`. It applies the tip's reduction
`exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine` to two lemmas: the étale case
(the unit/tensor comparison for an étale map over an arbitrary base) and the affine-line case
(the canonical duality on the compactified affine line). This module does not import
`WeilConjectures.SixFunctors.Etale.Derived.SmoothDuality`, so that the smooth generic direct
image (`lemma-smooth-morphisms-locally-constant-sheaves`), which uses smooth duality, has no import
path back to `Finiteness/Deligne.lean`.
-/

@[expose] public section

universe u

open CategoryTheory Limits MonoidalCategory

open scoped CategoryTheory.Functor

namespace AlgebraicGeometry

open Scheme

namespace Etale

variable (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] {X Y : Scheme.{u}}
  [HasInvertibleExponent Λ X]
  (f : X ⟶ Y) [HasCompactification f] (d : ℕ) [SmoothOfRelativeDimension d f]

attribute [local instance high] SymmetricCategory.toBraidedCategory

-- Move the unitor inside the adjunction bijection to match the ambient normalization.
private lemma ambientTensorMap_eq {V W : Scheme.{u}} (e : V ⟶ W)
    [HasCompactification e]
    (K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    sfEtaleAmbientTensorMap Λ (HasCompactification.compactification e)
        (R(e)^![Λ]) (rightDerivedUpperShriekAdjunction Λ e) K =
      dualizingComplexTensorMap Λ e K := by
  unfold sfEtaleAmbientTensorMap dualizingComplexTensorMap lowerShriekRightAdjointUnitTensorMap
    lowerShriekRightAdjointTensorMap Adjunction.projectionTensorMap
  dsimp only [rightDerivedLowerShriek, projectionMap, derivedTensorLeftUnitor]
  erw [← Adjunction.homEquiv_naturality_right]
  simp only [Category.assoc]
  rfl

private lemma etaleSmoothDuality : EtaleSmoothDuality Λ := by
  intro V W e _ _
  have : IsSeparated e := (HasCompactification.compactification e).isSeparated
  obtain ⟨-, -, -, hunit, htheta⟩ := sfEtaleUnitTensorArbitraryBase Λ e
    (HasCompactification.compactification e) (R(e)^![Λ])
    (rightDerivedUpperShriekAdjunction Λ e)
  exact ⟨fun K ↦ by simpa only [ambientTensorMap_eq] using htheta K, ⟨asIso
    (sfEtaleRightAdjointUnit Λ e (HasCompactification.compactification e)
      (R(e)^![Λ]) (rightDerivedUpperShriekAdjunction Λ e))⟩⟩

-- The compactification comparison preserves projection, and its two counit factors cancel.
private lemma ambientTensorMap_compactification {V W : Scheme.{u}} (e : V ⟶ W)
    [HasCompactification e] [QuasiCompact e] (c : Compactification e)
    (K : _root_.DerivedCategory (Sheaf W.smallEtaleTopology (ModuleCat.{u + 1} Λ))) :
    sfEtaleAmbientTensorMap Λ c (R(e)^![Λ])
        ((rightDerivedUpperShriekAdjunction Λ e).ofNatIsoLeft
          (rightDerivedLowerShriekIso Λ c).symm) K =
      sfEtaleAmbientTensorMap Λ (HasCompactification.compactification e)
        (R(e)^![Λ]) (rightDerivedUpperShriekAdjunction Λ e) K := by
  let E := rightDerivedLowerShriekIso Λ c
  let M := (R(e)^![Λ]).obj (constantComplex Λ W)
  have hp := projectionMapOfCompactification_rightDerivedLowerShriekOfCompactificationIso
    Λ c (HasCompactification.compactification e) M K
  have := (sfEtaleAmbientAdjointProjection Λ c).2 M K
  have := (sfEtaleAmbientAdjointProjection Λ
    (HasCompactification.compactification e)).2 M K
  have hpi : E.inv.app
        (((derivedTensor (ModuleCat.{u + 1} Λ) V).obj M).obj
          ((L((e)^*[ModuleCat.{u + 1} Λ])).obj K)) ≫
      inv (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ) c).app M).app K) ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) W).map (E.hom.app M)).app K =
      inv (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
        (HasCompactification.compactification e)).app M).app K) := by
    rw [← cancel_mono (((projectionMapOfCompactification (ModuleCat.{u + 1} Λ)
      (HasCompactification.compactification e)).app M).app K)]
    simp only [Category.assoc, IsIso.inv_hom_id]
    dsimp only [E, rightDerivedLowerShriekIso]
    erw [← hp]
    simp only [IsIso.inv_hom_id_assoc, Iso.inv_hom_id_app]
  unfold sfEtaleAmbientTensorMap
  rw [Adjunction.homEquiv_ofNatIsoLeft_apply]
  congr 1
  simp only [Adjunction.ofNatIsoLeft_counit, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.map_comp, Category.assoc]
  simpa only [E, M, Iso.symm_hom, Iso.symm_inv, Category.assoc] using
    congrArg (fun z ↦ z ≫
      ((derivedTensor (ModuleCat.{u + 1} Λ) W).map
        ((rightDerivedUpperShriekAdjunction Λ e).counit.app
          (constantComplex Λ W))).app K ≫
      (derivedTensorLeftUnitor (ModuleCat.{u + 1} Λ) W K).hom) hpi

-- Lift the geometric point to a trivializing cover and apply its module-linear local basis.
private lemma finiteTateLine_stalk (T : Scheme.{u}) (N : ℕ) (hN : 0 < N)
    (hA : (N : Λ) = 0) (hT : ∀ t : T, IsUnit (N : T.presheaf.stalk t)) :
    ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T),
      Nonempty ((pointSmallEtale s).sheafFiber.obj (finiteEtaleTateLine T N Λ hA) ≅
        ModuleCat.of Λ Λ) := by
  classical
  obtain ⟨⟨cover, hcover⟩, -, -, -⟩ := finite_etale_torsion_twist_line T N hN hT Λ hA 1
  intro Ω _ _ s
  obtain ⟨i, y, hy⟩ := cover.exists_eq (s.base (IsLocalRing.closedPoint _))
  have : AlgebraicGeometry.Etale (cover.f i) := cover.map_prop i
  obtain ⟨s', rfl⟩ := exists_comp_eq_of_etale (cover.f i) s ⟨y, hy⟩
  let U := cover.etalePrecoverageToEtale i
  let E := Etale.overSheafEquiv U (ModuleCat.{u + 1} Λ)
  let c := (Etale.overEquiv U).constantSheafSheafCongrIso
    (T.smallEtaleTopology.over U) U.left.smallEtaleTopology (ModuleCat.{u + 1} Λ)
    Over.mkIdTerminal
  let ei : ((cover.f i)^*[ModuleCat.{u + 1} Λ]).obj (finiteEtaleTateLine T N Λ hA) ≅
      𝟙_ _ :=
    (overSheafEquivFunctorObjOverIso (ModuleCat.{u + 1} Λ) U
      (finiteEtaleTateLine T N Λ hA)).symm ≪≫
      E.functor.mapIso (hcover i).some ≪≫ c.app (ModuleCat.of Λ Λ)
  exact ⟨((Etale.upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (cover.f i) s').app
      (finiteEtaleTateLine T N Λ hA)).symm ≪≫
    (pointSmallEtale s').sheafFiber.mapIso ei ≪≫
    ((pointSmallEtale s').uliftSheafFiberIso.{u + 1} (ModuleCat.{u + 1} Λ)).symm.app _ ≪≫
    sheafFiberUnitIso (ModuleCat.{u + 1} Λ) s'⟩

private lemma affineLineSmoothDuality : AffineLineSmoothDuality Λ := by
  intro S _ _ _
  let p := AffineSpace (ULift.{u} (Fin 1)) S ↘ S
  obtain ⟨N, hN, hA, hS⟩ := HasInvertibleExponent.exists_isUnit_natCast (Λ := Λ) (X := S)
  have hS' (s : S) : IsUnit (N : S.presheaf.stalk s) := by
    simpa only [map_natCast] using hS.map (S.presheaf.germ ⊤ s trivial).hom
  have hT (t : AffineSpace (ULift.{u} (Fin 1)) S) :
      IsUnit (N : (AffineSpace (ULift.{u} (Fin 1)) S).presheaf.stalk t) := by
    simpa only [map_natCast] using (hS' (p.base t)).map (p.stalkMap t).hom
  let c := sfAffineLineCompactification S
  let adj := (rightDerivedUpperShriekAdjunction Λ p).ofNatIsoLeft
    (rightDerivedLowerShriekIso Λ c).symm
  obtain ⟨gamma, hgamma⟩ := sfAffineLineCanonicalDuality Λ N hN hA S hS'
    (R(p)^![Λ]) adj
  have hline := (finite_etale_torsion_twist_line
    (AffineSpace (ULift.{u} (Fin 1)) S) N hN hT Λ hA 1).2.1
  refine ⟨⟨finiteEtaleTateLine _ N Λ hA, hline, finiteTateLine_stalk Λ _ N hN hA hT,
    ⟨gamma.symm⟩⟩, ?_⟩
  intro K
  have := hgamma K
  have : IsIso (sfEtaleAmbientTensorMap Λ c (R(p)^![Λ]) adj K) :=
    IsIso.of_isIso_comp_left
      (((derivedTensor (ModuleCat.{u + 1} Λ) _).map gamma.hom).app
        ((L((p)^*[ModuleCat.{u + 1} Λ])).obj K)) _
  change IsIso (dualizingComplexTensorMap Λ p K)
  rw [← ambientTensorMap_eq Λ p K]
  exact (ambientTensorMap_compactification Λ p c K) ▸ this

include d in
/-- Smooth cohomological duality without a chosen orientation (the statement of blueprint
`proposition-exceptional-inverse-image-smooth-morphism`,
`AlgebraicGeometry.Etale.exists_dualizingComplex_iso_and_tensor`), proved from
`exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine` by the étale case and the
affine-line case below. It is kept apart from `SmoothDuality.lean` so that the prime-field case of
`lemma-smooth-morphisms-locally-constant-sheaves` does not import that file.

Let `f : X ⟶ Y` be smooth, separated, compactifiable and of pure relative dimension `d`, let `Λ`
be a finite ring whose exponent is invertible on `X`, and put `ω_f = Rf^! Λ_Y`. Then `ω_f[-2d]` is
a locally constant sheaf `L` of free rank-one `Λ`-modules: `L` is locally constant, every stalk
of `L` at a geometric point is free of rank one, and `ω_f ≅ L[2d]`. For every complex `K` on `Y`,
the canonical map `θ_{f,K} : ω_f ⊗ᴸ Lf^* K ⟶ Rf^! K`
(`AlgebraicGeometry.Etale.dualizingComplexTensorMap`) is an isomorphism. -/
theorem exists_dualizingComplex_iso_and_tensor_of_finite :
    ∃ L : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ), IsLocallyConstantSheaf L ∧
      (∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X),
        Nonempty ((pointSmallEtale s).sheafFiber.obj L ≅ ModuleCat.of Λ Λ)) ∧
      Nonempty (dualizingComplex Λ f ≅
        ((_root_.DerivedCategory.singleFunctor _ 0).obj L)⟦(2 * d : ℤ)⟧) ∧
      ∀ K : _root_.DerivedCategory (Sheaf Y.smallEtaleTopology (ModuleCat.{u + 1} Λ)),
        IsIso (dualizingComplexTensorMap Λ f K) := by
  exact exists_dualizingComplex_iso_and_tensor_of_etale_of_affineLine
    (etaleSmoothDuality Λ) (affineLineSmoothDuality Λ) f d

end Etale

end AlgebraicGeometry

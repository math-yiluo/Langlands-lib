/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.EtaleCohomology.Purity.Smooth.KummerClass
public import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
public import WeilConjectures.AlgebraicGeometry.Sites.Kummer
public import Mathlib.Algebra.Module.ZMod
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
public import Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
public import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
public import WeilConjectures.CategoryTheory.RingedSiteModules
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTateLineOverField
import WeilConjectures.AlgebraicGeometry.SmoothPurity.NormalGenericLocallyConstantUnit
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLinePullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateSheaf
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateTwist
import WeilConjectures.AlgebraicGeometry.Sites.Kummer
import Mathlib.Algebra.Module.ZMod
import Mathlib.Algebra.Category.ModuleCat.Monoidal.Closed
import Mathlib.CategoryTheory.Sites.Monoidal
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.TensorProduct
import WeilConjectures.AlgebraicGeometry.EtaleConstantRingModuleEquivalence
import WeilConjectures.CategoryTheory.RingedSiteModules
import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.InternalHom
import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.TensorColimits
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Coherence
import WeilConjectures.EtaleCohomology.TateTwist.Sheaf
import WeilConjectures.EtaleCohomology.TateTwist.RootsOfUnityPullback
import WeilConjectures.AlgebraicGeometry.FiniteEtaleTateLocalLine
import WeilConjectures.AlgebraicGeometry.Sites.SmallEtaleRepresentablePresheafSheaf
import WeilConjectures.ConstructibleSheaf.Pullback
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.Monoidal
import WeilConjectures.CategoryTheory.Sites.ConstantSheafMonoidal
import WeilConjectures.Mathlib.AlgebraicGeometry.AffineScheme
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
import Mathlib.RingTheory.IntegralClosure.IntegrallyClosed
import Mathlib.RingTheory.Localization.Away.Basic
import Mathlib.AlgebraicGeometry.GammaSpecAdjunction

/-! # Comparing normalized and finite-root Tate lines
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

open Scheme

/-- The degree-one line of a normalized Tate datum is the finite root-of-unity line. -/
theorem nonempty_normalizedTateLineComparison
    (Λ : Type (u + 1)) [CommRing Λ] [Finite Λ] [HasTateTwist Λ]
    [HasTateTwist.IsNormalized Λ] (N : ℕ) (hN : 0 < N) (hΛ : (N : Λ) = 0)
    (X : Scheme.{u}) [HasInvertibleExponent Λ X] (hX : IsUnit (N : Γ(X, ⊤))) :
    Nonempty (tateObject Λ X 1 ≅
      (_root_.DerivedCategory.singleFunctor _ 0).obj
        (Scheme.finiteEtaleTateLine X N Λ hΛ))  := by
  let R := ULift.{u} ℤ
  let B := Localization.Away (N : R)
  let V := Spec (CommRingCat.of B)
  have : IsDomain R := Function.Injective.isDomain
    (ULift.ringEquiv : R ≃+* ℤ).toRingHom ULift.ringEquiv.injective
  have hNR : (N : R) ≠ 0 := by
    intro hz
    have hz' := congrArg (ULift.ringEquiv : R ≃+* ℤ) hz
    have : (N : ℤ) = 0 := by
      simpa only [map_natCast, map_zero] using hz'
    exact (Nat.ne_of_gt hN) (Int.ofNat_eq_zero.mp this)
  have : IsDomain B := Localization.Away.isDomain hNR
  have : IsIntegrallyClosed R := IsIntegrallyClosed.of_equiv ULift.ringEquiv.symm
  have : IsIntegrallyClosed B :=
    isIntegrallyClosed_of_isLocalization B (Submonoid.powers (N : R))
      (Submonoid.powers_le.mpr (mem_nonZeroDivisors_of_ne_zero hNR))
  have : IsIntegral V := inferInstance
  have hV : IsNormalScheme V := ⟨inferInstance, fun v ↦
    ⟨inferInstance, Scheme.isIntegrallyClosed_stalk_Spec B v⟩⟩
  have hB : IsUnit (N : Γ(V, ⊤)) := by
    have h : IsUnit (N : B) := by
      exact (map_natCast (algebraMap R B) N) ▸
        IsLocalization.Away.algebraMap_isUnit (S := B) (N : R)
    exact (map_natCast (Scheme.ΓSpecIso (.of B)).inv.hom N) ▸
      h.map (Scheme.ΓSpecIso (.of B)).inv.hom
  have : HasInvertibleExponent Λ V := ⟨N, hN, hΛ, hB⟩
  let g := V.fromSpecStalk (genericPoint V)
  have : HasInvertibleExponent Λ (Spec (.of V.functionField)) := .of_hom g
  have hg : IsUnit (N : Γ(Spec (.of V.functionField), ⊤)) := by
    simpa only [map_natCast] using hB.map g.appTop.hom
  obtain ⟨L, hL, _, ⟨eL⟩⟩ :=
    HasTateTwist.exists_isLocallyConstantSheaf_twistObject (Λ := Λ) V 1
  have := hL
  let M := Scheme.finiteEtaleTateLine V N Λ hΛ
  obtain ⟨cover, hc⟩ := Scheme.finiteEtaleTateLine_localTrivial V N hN
    (fun v ↦ (map_natCast (V.presheaf.germ ⊤ v trivial).hom N) ▸
      hB.map (V.presheaf.germ ⊤ v trivial).hom) Λ hΛ
  have : IsLocallyConstantSheaf M := by
    refine ⟨⟨⟨cover, fun i ↦ ?_⟩⟩⟩
    apply (isConstant_over_iff_upperStar _ _ M).2
    exact Sheaf.isConstant_of_iso _ ((hc i).some ≪≫
      Functor.Monoidal.εIso
        (constantSheaf (cover.X i).smallEtaleTopology (ModuleCat.{u + 1} Λ)))
  obtain ⟨c, _, _, _⟩ := Scheme.finiteEtaleTateLine_pullback_normalized Λ N hN hΛ
  obtain ⟨eg⟩ := nonempty_normalizedTateLineOverField Λ N hN hΛ V.functionField hg
  let σ := _root_.DerivedCategory.singleFunctor
    (Sheaf V.smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  let τ := _root_.DerivedCategory.singleFunctor
    (Sheaf (Spec (.of V.functionField)).smallEtaleTopology (ModuleCat.{u + 1} Λ)) 0
  let D := L((g)^*[ModuleCat.{u + 1} Λ])
  let e : (upperStar (ModuleCat.{u + 1} Λ) g).obj L ≅
      (upperStar (ModuleCat.{u + 1} Λ) g).obj M :=
    τ.preimageIso
      (((singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) g).app L).symm ≪≫
        D.mapIso eL.symm ≪≫ leftDerivedUpperStarTateObjectIso g 1 ≪≫ eg ≪≫
        (τ.mapIso (c g hB)).symm)
  have hunitL := isIso_normalGeneric_locallyConstant_unit Λ V hV L
  have hunitM := isIso_normalGeneric_locallyConstant_unit Λ V hV M
  let adj := upperStarLowerStarAdjunction (ModuleCat.{u + 1} Λ) g
  let eV : tateObject Λ V 1 ≅ σ.obj M :=
    eL ≪≫ σ.mapIso (asIso (adj.unit.app L) ≪≫
      (lowerStar (ModuleCat.{u + 1} Λ) g).mapIso e ≪≫ (asIso (adj.unit.app M)).symm)
  let φ : R →+* Γ(X, ⊤) :=
    (Int.castRingHom Γ(X, ⊤)).comp ULift.ringEquiv.toRingHom
  have hφ : IsUnit (φ (N : R)) := by
    rw [map_natCast]
    exact hX
  let f : X ⟶ V :=
    ΓSpec.adjunction.homEquiv X (Opposite.op (CommRingCat.of B))
      (CommRingCat.ofHom (IsLocalization.Away.lift (N : R) hφ)).op
  exact ⟨(leftDerivedUpperStarTateObjectIso f 1).symm ≪≫
    (L((f)^*[ModuleCat.{u + 1} Λ])).mapIso eV ≪≫
    (singleFunctorCompLeftDerivedUpperStarIso (ModuleCat.{u + 1} Λ) f).app M ≪≫
    (_root_.DerivedCategory.singleFunctor _ 0).mapIso (c f hB)⟩

end AlgebraicGeometry.Etale

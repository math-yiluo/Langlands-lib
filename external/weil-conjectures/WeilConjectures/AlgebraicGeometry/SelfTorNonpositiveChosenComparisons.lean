/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.Flat
public import WeilConjectures.Algebra.Homology.KFlat
public import WeilConjectures.AlgebraicGeometry.DerivedHomMayerVietoris
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.AlgebraicGeometry.DerivedSelfTorAffineCoordinates
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison
import WeilConjectures.Algebra.Homology.BoundedAboveFlatRingedSpaceKFlat

import WeilConjectures.AlgebraicGeometry.QuotientResolutionTensorComparison

/-! # Chosen affine comparison for nonpositive flat resolutions
Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9, and 00LS(1).
(blueprint: new-h3-self-tor-nonpositive-chosen-comparisons). -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

-- Derived tensor transport unfolds the large sheaf and derived category instance terms.
set_option synthInstance.maxSize 2048 in
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Nonpositive flat resolutions have affine coordinates compatible with one
augmented quotient-resolution lift on each basic inclusion. Compatibility with
arbitrary supplied lifts is a separate algebraic homotopy argument.

Source: Stacks Project, Tags 08DX(2), 06YG, 06YB, 01I9, and 00LS(1).
(blueprint: new-h3-self-tor-nonpositive-chosen-comparisons).

Proof: Bounded-above termwise flatness makes K K-flat. Apply the natural
K-flat derived tensor comparison to the constant families K and B[0]. The
quasi-isomorphism q becomes an isomorphism d under derived localization. Tensor
d inverse with the identity of Q(B[0]), then compose with the K-flat comparison.
Apply homology in degree -n and the homology factorization isomorphism. This gives
a global sheaf isomorphism from intrinsic derived self-Tor to the stated homology.

Take normalized affine coordinates for intrinsic derived self-Tor from
exists_derived_selfTor_affine_coordinates. Compose each coordinate equivalence
with the linear equivalence on sections induced by the global sheaf isomorphism.
For a basic inclusion V in U, restriction carries the kernel ideal on U into
that on V. The augmented quotient-resolution tensor comparison therefore provides
psi, a and k with the quotient, augmentation and pure-tensor equations.

Apply the intrinsic coordinate restriction equation to these supplied comparisons.
Naturality of the global sheaf isomorphism identifies restriction of its U section
map with its V section map after restriction. Substitute the intrinsic equation
and apply the V section map to both sides. This proves the desired equation for
the composed coordinates, using the same restriction-of-scalars homology comparison.
The algebraic lifting theorem does not require projective restricted target terms.
Degree zero, zero quotients, and empty basic opens use these same constructions. -/
theorem exists_selfTor_nonpositive_chosen_comparisons
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [IsClosedImmersion i]
    (K : CochainComplex (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) ℤ)
    (q : K ⟶ (CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0).obj
        ((Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)))
    (hbounded : ∀ j : ℤ, 0 < j → IsZero (K.X j))
    (hflat : ∀ j : ℤ, SheafOfModules.IsFlat (K.X j)) (hq : QuasiIso q) (n : ℕ) :
    letI := SheafOfModules.monoidalCategory Y.sheaf
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := CochainComplex.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (CochainComplex.mapBifunctor K (S.obj B)
      (curriedTensor (SheafOfModules.{u} (moduleRings Y.toRingedSpace)))).homology
        (-(n : ℤ))
    ∃ c : ∀ U : Y.affineOpens,
        ((((tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).mapHomologicalComplex (.down ℕ)).obj
            (projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
              ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).complex).homology n) ≃ₗ[Γ(Y, U.1)]
              Q.val.obj (op U.1),
      ∀ (V U : Y.affineOpens) (h : V.1 ≤ U.1)
        (_hbasic : ∃ f : Γ(Y, U.1), Y.basicOpen f = V.1),
          let A := (Γ(Y, U.1) : Type u)
          let C := (Γ(Y, V.1) : Type u)
          let I := i.ker.ideal U
          let J := i.ker.ideal V
          let φ := (Y.presheaf.map (homOfLE h).op).hom
          let P := projectiveResolution (ModuleCat.of A (A ⧸ I))
          let R := projectiveResolution (ModuleCat.of C (C ⧸ J))
          let TA := (tensorRight (ModuleCat.of A (A ⧸ I))).mapHomologicalComplex
            (.down ℕ)
          let TC := (tensorRight (ModuleCat.of C (C ⧸ J))).mapHomologicalComplex
            (.down ℕ)
          ∃ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) ∧
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) ∧
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) ∧
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
          ∀ x, Q.val.map (homOfLE h).op (c U x) =
            c V (e.hom (HomologicalComplex.homologyMap k n x)) := by
  classical
  let M := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  let := HasDerivedCategory.standard M
  let := SheafOfModules.monoidalCategory Y.sheaf
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let S := CochainComplex.singleFunctor M 0
  let T := S.obj B
  have hK : K.IsKFlatTensor := CochainComplex.isKFlat_of_boundedAbove_flat_ringedSpace
    Y.toRingedSpace K ⟨0, hbounded⟩ hflat
  let F := (Functor.const PUnit.{1}).obj K
  let G := (Functor.const PUnit.{1}).obj T
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso Y F G (fun _ ↦ hK)
  let e := (comparison.app PUnit.unit.{1}).app PUnit.unit.{1}
  have : QuasiIso q := hq
  let d := asIso (DerivedCategory.Q.map q)
  let H := DerivedCategory.homologyFunctor M (-(n : ℤ))
  let eQ := H.mapIso ((MonoidalCategory.tensorIso d (Iso.refl _)).symm ≪≫ e) ≪≫
    (DerivedCategory.homologyFunctorFactors M (-(n : ℤ))).app _
  obtain ⟨c, hc⟩ := exists_derived_selfTor_affine_coordinates i n
  refine ⟨fun U ↦ (c U).trans (Scheme.Modules.appLinearEquivOfIso eQ U.1), ?_⟩
  intro V U h hbasic A C I J φ P R TA TC
  have hI : ∀ x ∈ I, φ x ∈ J := by
    intro x hx
    exact i.ker.ideal_le_comap_ideal h hx
  refine (exists_quotient_resolution_tensor_comparison A C I J φ hI P R).imp
    (fun ψ hψ ↦ hψ.imp (fun a ha ↦ ha.imp (fun k hk ↦ ?_)))
  refine ⟨hk.1, hk.2.1, hk.2.2, ?_⟩
  intro e' x
  have hn := hc V U h hbasic ψ a k hk.1 hk.2.1 hk.2.2 x
  have hs := PresheafOfModules.naturality_apply eQ.hom.val (homOfLE h).op (c U x)
  change _ = eQ.hom.val.app (op V.1) _
  exact hs.symm.trans (congrArg (eQ.hom.val.app (op V.1)) hn)

end AlgebraicGeometry

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
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

public import WeilConjectures.Mathlib.AlgebraicGeometry.IdealSheaf.Module

import WeilConjectures.Algebra.Homology.KFlatResolution
import WeilConjectures.AlgebraicGeometry.SelfTorOrdinaryResolutionSections
import WeilConjectures.AlgebraicGeometry.QuotientResolutionTensorComparison
import WeilConjectures.AlgebraicGeometry.KFlatDerivedTensorComparison

/-! # Ambient self-Tor coordinates on affine sections

Source: Stacks Project, Tags 08DX(2), 06YG and 00LS.
(blueprint: new-h2-self-tor-ambient-localized-comparisons). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
set_option synthInstance.maxSize 2048 in

/-- Ambient affine coordinates compatible with one localized resolution comparison for each
basic inclusion. This asserts existence of comparison lifts, not compatibility with all lifts.
Source: Stacks Project, Tag 08DX(2), with Tags 06YG and 00LS(1).
(blueprint: new-h2-self-tor-ambient-localized-comparisons).

Proof: For each affine U, identify the closed structure sheaf with tilde(A/I).
Sheafify its chosen projective resolution and augmentation using
lem-sc-affine-quotient-resolution-sheafification. Extend it to nonpositive
cochain degrees. Projective modules are flat, and their associated sheaves are
flat. Apply lem-pc-bounded-above-flat-kflat and the natural affine computation
lem-pc-affine-derived-pullback-tensor-tilde. Exactness of tilde and affine
sections identifies the negative-n homology of the ambient self-tensor with
homology of the quotient tensor resolution. This gives c_U directly on the tensor
complex homology, before the separate isoLeftDerivedObj transport to Tor.
These coordinates come from the same natural derived comparison.
For each basic V inside U, the ideal restriction induces the quotient map psi.
Localize the chosen U-resolution, obtaining a projective resolution over C.
Lift its augmentation to the chosen V-resolution by the projective lifting
argument of 00LS(1). Precompose with localization to obtain a and tensor with
psi to obtain k, so the three displayed equations hold. Naturality of the
K-flat comparison (lem-pc-kflat-derived-tensor-comparison), exact restriction
of scalars, and the affine section unit gives the displayed equality for this
one lift. No uniqueness or homotopy independence is asserted here.
For n=0 the same homology comparison applies. For I=top or an empty basic
open, quotient and section modules are zero; the constructions and equations
remain valid. -/
theorem exists_selfTor_ambient_localized_comparisons
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q :=
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
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
  intro B S Q
  classical
  let := SheafOfModules.monoidalCategory Y.sheaf
  let C := SheafOfModules.{u} (moduleRings Y.toRingedSpace)
  -- Reuse the abelian structure instead of synthesizing it at each comparison step.
  let : Abelian C := inferInstance
  let N := (CochainComplex.singleFunctor C 0).obj B
  obtain ⟨K, q, hK, _, hq, _⟩ := CochainComplex.exists_isKFlatResolution N
  have : QuasiIso q := hq
  let : K.HasMapBifunctor N (curriedTensor C) := inferInstance
  obtain ⟨comparison⟩ := kFlat_derivedTensor_comparison_natIso Y
    ((Functor.const (Discrete PUnit.{1})).obj K)
    ((Functor.const (Discrete PUnit.{1})).obj N) (fun _ ↦ hK)
  let eK : DerivedCategory.Q.obj K ≅ (DerivedCategory.singleFunctor C 0).obj B :=
    asIso (DerivedCategory.Q.map q) ≪≫
      ((DerivedCategory.singleFunctorIsoCompQ C 0).app B).symm
  let eN := (DerivedCategory.singleFunctorIsoCompQ C 0).app B
  let eTensor : (DerivedCategory.singleFunctor C 0).obj B ⊗
      (DerivedCategory.singleFunctor C 0).obj B ≅
        DerivedCategory.Q.obj (CochainComplex.mapBifunctor K N (curriedTensor C)) :=
    (tensorIso eK eN.symm).symm ≪≫
      (comparison.app ⟨PUnit.unit⟩).app ⟨PUnit.unit⟩
  let e := ((DerivedCategory.homologyFunctor C (-(n : ℤ))).mapIso eTensor ≪≫
    (DerivedCategory.homologyFunctorFactors C (-(n : ℤ))).app
      (CochainComplex.mapBifunctor K N (curriedTensor C))).symm
  obtain ⟨d, hd⟩ := exists_selfTor_ordinary_resolution_sections i K q hK hq n
  let eu := fun U : Y.affineOpens ↦
    (show _ ≃ₗ[Γ(Y, U.1)] _ from
      ((SheafOfModules.evaluation Y.ringCatSheaf (op U.1)).mapIso e).toLinearEquiv)
  let c := fun U : Y.affineOpens ↦ (d U).trans (eu U)
  refine ⟨c, ?_⟩
  intro V U h hbasic A D I J φ P R TA TC
  obtain ⟨ψ, a, k, hψ, ha, hk⟩ := exists_quotient_resolution_tensor_comparison
    A D I J φ (fun x hx ↦ i.ker.ideal_le_comap_ideal h hx) P R
  refine ⟨ψ, a, k, hψ, ha, hk, ?_⟩
  intro es x
  have hn := hd V U h hbasic ψ a k hψ ha hk x
  change _ = e.hom.val.app (op V.1) _
  have he := (PresheafOfModules.naturality_apply e.hom.val
    (homOfLE h).op (d U x)).symm
  exact he.trans (congrArg (fun y ↦ e.hom.val.app (op V.1) y) hn)

end AlgebraicGeometry

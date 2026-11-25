/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.CategoryTheory.Abelian.Projective.Resolution
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import Mathlib.CategoryTheory.Monoidal.Tor
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import WeilConjectures.AlgebraicGeometry.DerivedTensorStructure

public import WeilConjectures.AlgebraicGeometry.SelfTorAffineSection

import WeilConjectures.AlgebraicGeometry.SelfTorAmbientResolutionCharts
import WeilConjectures.AlgebraicGeometry.TensorPullbackOverIsoUnit

/-! # Affine derived-Tor charts from chosen resolution comparisons

Source: Stacks Project, Tags 06YH, 06YG and 00LS.
(blueprint: new-q1-self-tor-chosen-resolution-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

-- Elaborating augmented tensor charts requires substantial definitional reduction.
set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The augmentation comparisons defining the affine derived-Tor charts commute
with every augmented tensor chain comparison between the chosen resolutions.
Source: Stacks Project, Tags 06YH, 06YG, 00LS and 01I6.
(blueprint: new-p4-self-tor-augmented-resolution-charts).

Proof: Sheafify the chosen projective quotient resolution on each affine chart.
Projective modules are summands of free modules, so their associated sheaves
are flat. Extend into nonpositive cochain degrees and use bounded-above flat
K-flatness. The augmentation identifies the quotient tensor with the restriction
of the fixed derived tensor. Exactness of tilde and isoLeftDerivedObj identify
homology with associated self-Tor. The quotient ideal annihilates this homology,
so tensor pullback preserves it. These augmentation comparisons define t.
For a basic inclusion and the given augmented chain map a, its sheafification
commutes with the augmentations. The pure tensor equation for k identifies
its sheafification with the tensor comparison. Inverting the augmentation
quasi-isomorphisms preserves this commutative square in the derived category.
Apply homology, the exact restriction-of-scalars comparison, and the tilde
comparison to get the square for the explicit q. Naturality of the tilde and
pullback units gives the section equation. Any two augmented lifts are
homotopic, so the comparison works for every given a and k, not just one lift.
Degree zero and empty basic opens use the same augmentation and homology maps. -/
theorem exists_selfTor_augmented_resolution_charts
    {Z Y : Scheme.{u}} (i : Z ⟶ Y)
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]
    [IsClosedImmersion i] (n : ℕ) :
    let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
    let S := DerivedCategory.singleFunctor
      (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
    let Q := (Scheme.Modules.tensorPullback i).obj
      ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
          (S.obj B ⊗ S.obj B))
    let T := fun U : Y.affineOpens ↦
      tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
        Scheme.Modules.pushforward U.1.ι ⋙ Scheme.Modules.tensorPullback i
    ∃ t : ∀ U : Y.affineOpens,
        ((T U).obj _).over (i ⁻¹ᵁ U.1) ≅ Q.over (i ⁻¹ᵁ U.1),
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
          ∀ (ψ : (A ⧸ I) →+* (C ⧸ J))
            (a : P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj R.complex)
            (k : TA.obj P.complex ⟶ ((ModuleCat.restrictScalars φ).mapHomologicalComplex
              (.down ℕ)).obj (TC.obj R.complex)),
            (∀ x : A, ψ (Ideal.Quotient.mk I x) = Ideal.Quotient.mk J (φ x)) →
            (∀ x : P.complex.X 0, R.π.f 0 (a.f 0 x) = ψ (P.π.f 0 x)) →
            (∀ (j : ℕ) (x : P.complex.X j) (y : A ⧸ I),
              k.f j (x ⊗ₜ[A] y) = (show R.complex.X j from a.f j x) ⊗ₜ[C] (ψ y)) →
            let e := ((TC.obj R.complex).sc n).mapHomologyIso
              (ModuleCat.restrictScalars φ)
            let q := fun x ↦
              (R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
                (e.hom (HomologicalComplex.homologyMap k n
                  ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
                (((T U).obj _).val.map (homOfLE (i.preimage_mono h)).op
                  (selfTorAffineSection i U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
                (selfTorAffineSection i V _ (q x)) := by
  classical
  dsimp only
  let B := (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf)
  let S := DerivedCategory.singleFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) 0
  let H := (DerivedCategory.homologyFunctor
    (SheafOfModules.{u} (moduleRings Y.toRingedSpace)) (-(n : ℤ))).obj
      (S.obj B ⊗ S.obj B)
  let F := fun U : Y.affineOpens ↦
    tilde.functor Γ(Y, U.1) ⋙ Scheme.Modules.restrictFunctor U.2.isoSpec.hom ⋙
      Scheme.Modules.pushforward U.1.ι
  let M := fun U : Y.affineOpens ↦
    (((Tor' (ModuleCat.{u} (Γ(Y, U.1) : Type u)) n).obj
      (ModuleCat.of (Γ(Y, U.1) : Type u) ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))).obj
      (ModuleCat.of (Γ(Y, U.1) : Type u) ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U)))
  let s := fun (U : Y.affineOpens) (x : M U) ↦
    let L := (tilde.functor Γ(Y, U.1)).obj (M U)
    (Scheme.Modules.restrictAppIso U.2.isoSpec.hom L (U.1.ι ⁻¹ᵁ U.1)).inv
      (L.val.map (homOfLE le_top).op ((tilde.adjunction.unit.app (M U)) x))
  let η := (Classical.choose (Scheme.Modules.exists_tensorPullbackAdjunction i)).unit
  obtain ⟨r, hr⟩ := exists_selfTor_ambient_resolution_charts.{u, w} i n
  choose t ht using fun U : Y.affineOpens ↦
    Scheme.Modules.exists_tensorPullback_over_iso_unit i U.1 ((F U).obj (M U)) H (r U)
  refine ⟨t, ?_⟩
  intro V U h hbasic ψ a k hψ ha hk x
  let P := projectiveResolution (ModuleCat.of (Γ(Y, U.1) : Type u)
    ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))
  let R := projectiveResolution (ModuleCat.of (Γ(Y, V.1) : Type u)
    ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))
  let TC := (tensorRight (ModuleCat.of (Γ(Y, V.1) : Type u)
    ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))).mapHomologicalComplex (.down ℕ)
  let e := ((TC.obj R.complex).sc n).mapHomologyIso
    (ModuleCat.restrictScalars (Y.presheaf.map (homOfLE h).op).hom)
  let q := fun x ↦
    (R.isoLeftDerivedObj (tensorRight (ModuleCat.of (Γ(Y, V.1) : Type u)
      ((Γ(Y, V.1) : Type u) ⧸ i.ker.ideal V))) n).inv
      (e.hom (HomologicalComplex.homologyMap k n
        ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of (Γ(Y, U.1) : Type u)
          ((Γ(Y, U.1) : Type u) ⧸ i.ker.ideal U))) n).hom x)))
  have hu := ht U V.1 h (((F U).obj (M U)).val.map (homOfLE h).op (s U x))
  have hv := ht V V.1 le_rfl (s V (q x))
  have hn := PresheafOfModules.naturality_apply (η.app ((F U).obj (M U))).val
    (homOfLE h).op (s U x)
  have hc := hr V U h hbasic ψ a k hψ ha hk x
  change (r U).hom.val.app (op (Over.mk (homOfLE h)))
      (((F U).obj (M U)).val.map (homOfLE h).op (s U x)) =
    (r V).hom.val.app (op (Over.mk (𝟙 V.1))) (s V (q x)) at hc
  change (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
      (((Scheme.Modules.tensorPullback i).obj ((F U).obj (M U))).val.map
        (homOfLE (i.preimage_mono h)).op
        ((η.app ((F U).obj (M U))).val.app (op U.1) (s U x))) =
    (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
      ((η.app ((F V).obj (M V))).val.app (op V.1) (s V (q x)))
  change (η.app ((F U).obj (M U))).val.app (op V.1)
      (((F U).obj (M U)).val.map (homOfLE h).op (s U x)) =
    (((Scheme.Modules.tensorPullback i).obj ((F U).obj (M U))).val.map
      (homOfLE (i.preimage_mono h)).op
      ((η.app ((F U).obj (M U))).val.app (op U.1) (s U x))) at hn
  exact (congrArg ((t U).hom.val.app
    (op (Over.mk (homOfLE (i.preimage_mono h))))) hn.symm).trans
      (hu.trans ((congrArg ((η.app H).val.app (op V.1)) hc).trans hv.symm))


end AlgebraicGeometry

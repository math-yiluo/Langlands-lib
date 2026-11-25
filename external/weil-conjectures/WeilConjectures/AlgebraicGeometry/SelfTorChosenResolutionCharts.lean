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

import WeilConjectures.AlgebraicGeometry.SelfTorAugmentedResolutionCharts
import WeilConjectures.AlgebraicGeometry.QuotientResolutionTensorComparison

/-! # Affine derived-Tor charts from chosen resolution comparisons

Source: Stacks Project, Tags 06YH, 06YG and 00LS.
(blueprint: new-q1-self-tor-chosen-resolution-charts). -/

@[expose] public section
set_option autoImplicit false
universe u w
open CategoryTheory CategoryTheory.Limits Opposite MonoidalCategory
open scoped TensorProduct
namespace AlgebraicGeometry

/-- Affine derived-Tor charts commute with the tensor chain comparison for
Mathlib's chosen projective quotient resolutions. The Tor map is the explicit
homology map of the chain comparison.
No cycle formula or assertion about other resolutions is assumed.
Source: Stacks Project, Tags 06YH, 06YG, 00LS and 01I6.
(blueprint: new-q1-self-tor-chosen-resolution-charts).

Proof: On each affine U use projectiveResolution of A/I, with A = Γ(Y,U).
Sheafify its augmentation using exists_affine_quotient_sheafified_resolution.
Its projective terms are summands of free modules; their associated sheaves
are flat. Extend into nonpositive cochain degrees and apply the bounded-above
flat K-flat criterion. The augmentation identifies its quotient tensor with
the restriction of the fixed derived tensor. Exact tilde commutes with homology;
isoLeftDerivedObj computes that homology as algebraic self-Tor. Multiplication
by each element of I on the quotient tensor is zero, so tensor pullback does
not change its homology. Compose these comparisons to obtain the family t.
For a basic inclusion V = D(f), the restriction homomorphism sends I into J,
so the quotient homomorphism ψ exists. The restricted target resolution is
exact over A. Lift the source augmentation into it degree by degree using
projectivity (00LS). Tensor a with ψ to construct k; the balancing identity
follows from ψ being compatible with the ring restriction. It is a chain map
by the chain-map equation for a. Let q be exactly the displayed induced map on tensor homology,
transported through restriction-of-scalars homology and the two
isoLeftDerivedObj isomorphisms. The K-flat
augmentation comparisons commute with this chain map; their inverses in the
derived category therefore commute as well. Exact tilde and naturality of
the tilde and tensor-pullback adjunction units turn this homology square into
the displayed equation on selfTorAffineSection, for every class x.
This argument includes n = 0 and f = 0; localization and the zero-module
homology calculation include empty charts and zero quotients. All isomorphisms
are obtained from augmentations, not chosen independently of the chain maps.
Resolution independence is a separate algebraic step, deliberately omitted. -/
theorem exists_selfTor_chosen_resolution_charts
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
            let q := fun x ↦
              (R.isoLeftDerivedObj (tensorRight (ModuleCat.of C (C ⧸ J))) n).inv
                (e.hom (HomologicalComplex.homologyMap k n
                  ((P.isoLeftDerivedObj (tensorRight (ModuleCat.of A (A ⧸ I))) n).hom x)))
          ∀ x,
            (t U).hom.val.app (op (Over.mk (homOfLE (i.preimage_mono h))))
                (((T U).obj _).val.map (homOfLE (i.preimage_mono h)).op
                  (selfTorAffineSection i U _ x)) =
              (t V).hom.val.app (op (Over.mk (𝟙 (i ⁻¹ᵁ V.1))))
                (selfTorAffineSection i V _ (q x))  := by
  obtain ⟨t, ht⟩ := exists_selfTor_augmented_resolution_charts.{u, w} i n
  refine ⟨t, ?_⟩
  intro V U h hbasic
  obtain ⟨ψ, a, k, hψ, ha, hk⟩ := exists_quotient_resolution_tensor_comparison
    (Γ(Y, U.1) : Type u) (Γ(Y, V.1) : Type u)
    (i.ker.ideal U) (i.ker.ideal V) (Y.presheaf.map (homOfLE h).op).hom
    (fun x hx ↦ i.ker.ideal_le_comap_ideal h hx)
    (projectiveResolution _) (projectiveResolution _)
  exact ⟨ψ, a, k, hψ, ha, hk, ht V U h hbasic ψ a k hψ ha hk⟩

end AlgebraicGeometry

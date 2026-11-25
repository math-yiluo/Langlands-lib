/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Cohomology.FlatCohomologyComparison
public import WeilConjectures.AlgebraicGeometry.ModuleCohomologyFMap
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyCoefficientTransport
import WeilConjectures.AlgebraicGeometry.ModuleCohomologyExtEdgeComparison

/-! # Module and Ext cohomology comparisons compatible with scheme maps

Source: Stacks Project, Tags 03FD, 01FB and 01F7.
(blueprint: new-module-cohomology-ext-pullback-comparison)
-/

@[expose] public section

universe u
set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits Opposite
noncomputable section
namespace AlgebraicGeometry.Scheme.Modules


/-- The module/Ext comparison can be normalized on both schemes so that
it intertwines the base-change unit h-map with exact abelian inverse image on Ext.

Source: Stacks Project, Tag 03FD, Lemma 21.12.4; Tag 01FB, Remark 20.14.2;
Tag 01F7, Section 20.14.
(blueprint: new-module-cohomology-ext-pullback-comparison)

Proof: On each scheme use the comparison of universal cohomological delta functors
normalized in degree zero by evaluation of a section at the integer 1. Forgotten
injective modules are section-acyclic, so their section complexes compute abelian
cohomology. Identify the free abelian representable of the top open with the
constant integer sheaf by this same evaluation. These comparisons are natural in
module morphisms. For an h-map phi resolve both coefficients and the direct-image
complex as in 01FB. Its augmentation-preserving lift beta and the invertible section
comparison mu compute the module map as H(mu) inverse after H(beta). After forgetting
modules the same diagram computes the abelian map. Under the degree-zero-normalized
constant-sheaf identification, that map is exact inverse image on Ext followed by
the adjoint coefficient map. Homotopy independence removes the choices. Use
this normalization on Y and its base change; apply the argument to baseChangeUnit for each N,
with no flatness assumption. Degree zero gives phi on sections;
zero coefficients and empty schemes give zero complexes. -/
theorem exists_moduleCohomology_ext_pullback_comparison
    {R B : Type u} [CommRing R] [CommRing B] [Algebra R B]
    {Y : Scheme.{u}} (h : Y ⟶ Spec (.of R)) (p : ℕ) :
    ∃ E : ∀ M : Y.Modules,
        ((RingedSpace.moduleCohomology Y.toRingedSpace p).obj M) ≃+ H M p,
      ∃ E' : ∀ M : (baseChangedScheme (S := B) h).Modules,
        ((RingedSpace.moduleCohomology
          (baseChangedScheme (S := B) h).toRingedSpace p).obj M) ≃+ H M p,
        (∀ (M M' : Y.Modules) (φ : M ⟶ M')
          (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj M),
          E M' (((RingedSpace.moduleCohomology Y.toRingedSpace p).map φ).hom x) =
            H.map φ p (E M x)) ∧
        (∀ (M M' : (baseChangedScheme (S := B) h).Modules) (φ : M ⟶ M')
          (x : (RingedSpace.moduleCohomology
            (baseChangedScheme (S := B) h).toRingedSpace p).obj M),
          E' M' (((RingedSpace.moduleCohomology
            (baseChangedScheme (S := B) h).toRingedSpace p).map φ).hom x) =
            H.map φ p (E' M x)) ∧
        (∀ (N : Y.Modules)
          (x : (RingedSpace.moduleCohomology Y.toRingedSpace p).obj N),
          E' (baseChangedModule (S := B) h N)
            (moduleCohomologyFMap (baseChangeFst (S := B) h)
              (baseChangeUnit (S := B) h N) p x) =
            H.baseChangeLinear (S := B) h N p (E N x)) := by
  classical
  obtain ⟨E, E', hE, hE', hedge⟩ := exists_moduleCohomology_ext_edge_comparison
    (R := R) (B := B) (Y := Y) h p
  refine ⟨E, E', hE, hE', ?_⟩
  intro N x
  have hs := moduleCohomology_transport_coefficient
    (X := baseChangedScheme (S := B) h) (Y := Y)
    (baseChangeFst (S := B) h) N (baseChangedModule (S := B) h N)
    (baseChangeUnit (S := B) h N) p (fun M y ↦ E M y)
    (fun y ↦ E' (baseChangedModule (S := B) h N) y)
    (hE N _ (baseChangeUnit (S := B) h N)) (hedge (baseChangedModule (S := B) h N)) x
  dsimp only [H.baseChangeLinear, cohomologyComparisonLinear]
  exact hs

end AlgebraicGeometry.Scheme.Modules

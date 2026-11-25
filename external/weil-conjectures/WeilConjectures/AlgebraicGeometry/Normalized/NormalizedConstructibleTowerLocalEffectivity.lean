/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.Constructible.ProEtaleConstructibleCoefficientSheaf
public import WeilConjectures.AlgebraicGeometry.Adic.AdicCoefficientDatumSupplement
public import WeilConjectures.AlgebraicGeometry.Bounded.BoundedConstructibleTowerSupplement
public import WeilConjectures.AlgebraicGeometry.Refinement.RefinementCoefficientRealization
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.AlgebraicGeometry.Noetherian

import WeilConjectures.AlgebraicGeometry.Finite.Coefficient.FiniteCoefficientDerivedOriginPresentation
import WeilConjectures.AlgebraicGeometry.Normalized.NormalizedTowerCommonLisseStrata
import WeilConjectures.AlgebraicGeometry.Lisse.LisseNormalizedTowerLocalModels

/-!
# Local effectivity of normalized bounded constructible towers

The existing AdicTower packages the strict derived tower, quotient-linear levels,
evaluation identifications, normalization isomorphisms, transitions and quotient cocycle.
The positive level n+1 is indexed by n: ℕ. Intrinsic constructibility uses the canonical
constant-to-functions coefficient comparison. The etale-origin conclusion uses the
existing bounded-constructible essential image, transported on actual cochain
representatives along the canonical coefficient-ring isomorphism. Thus no new derived
scalar functor or chosen comparison equivalence is needed.

## References

* Stacks Tags 09AL, 09BU--09BX and 09AV
* Stacks Project, Tags 09AL, 09BU--09BX and 09AV
-/

@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Scheme

set_option backward.isDefEq.respectTransparency.instanceSearchTypes false in
/-- Bounded constructible etale origin of a level of the recorded adic tower. The witness
C represents an object in the existing finite-coefficient bounded-constructible essential
image. Its coefficient transport is restriction along the canonical ring-sheaf comparison,
termwise before localization. This is just a presentation of the same derived object,
not an additional condition on the representative. -/
def IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin
    (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d) (n : ℕ) : Prop :=
  letI : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
  letI : TopologicalSpace (A ⧸ d.ideal ^ (n + 1)) := ⊥
  letI : DiscreteTopology (A ⧸ d.ideal ^ (n + 1)) := discreteTopology_bot _
  ∃ C : CochainComplex
      (ProEtale.FiniteCoefficientModules X (A ⧸ d.ideal ^ (n + 1))) ℤ,
    ProEtale.isBoundedConstructibleFiniteCoefficient X (A ⧸ d.ideal ^ (n + 1))
      (DerivedCategory.Q.obj C) ∧
    Nonempty (DerivedCategory.Q.obj
      (((SheafOfModules.restrictScalars
        (AdicCoefficients.finiteRingComparison X (A ⧸ d.ideal ^ (n + 1))).hom).mapHomologicalComplex
          (.up ℤ)).obj C) ≅ M.level n)

private theorem inverse_normalization_square
    {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {N M : D} {N' M' : C} (e : N ≅ M) (e' : N' ≅ M')
    (rN : N ⟶ F.obj N') (rM : M ⟶ F.obj M')
    (h : e.hom ≫ rM = rN ≫ F.map e'.hom) :
    rM ≫ F.map e'.inv = e.inv ≫ rN := by
  apply (cancel_mono (F.map e'.hom)).1
  simp only [Category.assoc, ← F.map_comp, Iso.inv_hom_id, F.map_id, Category.comp_id]
  rw [← h]
  simp

/-- A normalized adic tower with intrinsically constructible cohomology in one common
interval has bounded constructible etale origin at every level and admits all the common
local-model data of uniformly bounded constructibility. Local terms need not be projective.
-/
theorem normalizedConstructibleTower_local_effectivity
    (X : Scheme.{u}) [IsNoetherian X] {A : Type (u + 1)} [CommRing A]
    (d : AdicCoefficientDatum A) (M : AdicTower X d)
    (hconstructible : ∀ (n : ℕ) (q : ℤ),
      @IsConstructibleProEtaleCoefficientModuleSheaf X (A ⧸ d.ideal ^ (n + 1)) _
        (d.quotientFinite n)
        ((pbcRestrict (pbcLevelConstantComparison X d n).hom).obj
          ((DerivedCategory.homologyFunctor _ q).obj (M.level n))))
    (a b : ℤ) (hab : a ≤ b)
    (hbounded : ∀ (n : ℕ) (q : ℤ), (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj (M.level n))) :
    (∀ n : ℕ, IsAdicTowerLevelOfBoundedConstructibleEtaleOrigin X d M n) ∧
      IsUniformlyBoundedConstructibleAdicTower d M := by
  constructor
  · intro n
    have : Finite (A ⧸ d.ideal ^ (n + 1)) := d.quotientFinite n
    exact finiteCoefficient_constructibleDerived_origin_presentation X _
      (pbcLevelConstantComparison X d n) (M.level n) (hconstructible n)
      a b hab (hbounded n)
  · obtain ⟨S, hS⟩ := normalizedTower_common_lisse_strata X d M
      (hconstructible 0) a b hab hbounded
    refine ⟨a, b, hab, S, ?_⟩
    intro i
    obtain ⟨V, hV, hmodels⟩ := lisseNormalizedTower_local_models X (S.domain i)
      (S.immersion i) d M a b hab hbounded (hS i)
    refine ⟨V, hV, ?_⟩
    intro U f hf
    obtain ⟨L, hL, hadic, hfinite, e, he⟩ := hmodels U f hf
    refine ⟨{
      complex := L
      bounded := hL
      adicLisse := hadic
      finiteLisse := hfinite
      identification := fun n ↦ (e n).symm
      compatible := ?_ }⟩
    intro m n hnm
    exact inverse_normalization_square _ (e m) (e n) _ _ (he m n hnm)

end AlgebraicGeometry.Scheme

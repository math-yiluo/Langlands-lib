/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FieldLinearModuleCohomologyOperations
public import Mathlib.Algebra.Homology.Embedding.ExtendHomology
public import Mathlib.Algebra.Homology.ShortComplex.PreservesHomology

/-! # Explicit nonnegative scalar cohomology models

Source: Stacks Project, Cohomology, Tag 01DZ; Varieties, Tag 0BED.
(blueprint: lem-sc-picard-kunneth-resolution-model).
-/

@[expose] public section

universe w
open CategoryTheory CategoryTheory.Limits
namespace AlgebraicGeometry.Scheme.Modules
noncomputable section

variable {k : Type w} [Field k] {X : Scheme.{w}}

/-- A fixed injective resolution, using the recorded enough-injectives structure.
Source: Stacks, Tag 01DZ (blueprint: lem-sc-picard-kunneth-resolution-model). -/
def picardScalarResolution (F : X.Modules) : InjectiveResolution F :=
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  injectiveResolution F

/-- Global sections of the fixed resolution with scalars restricted to k.
Source: Stacks, Tag 01DZ (blueprint: lem-sc-picard-kunneth-resolution-model). -/
def picardScalarResolutionComplex (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    CochainComplex (ModuleCat.{w} k) ℕ :=
  ((ModuleCat.restrictScalars (scalarMap f ⊤)).mapHomologicalComplex
    (ComplexShape.up ℕ)).obj (RingedSpace.globalSectionsComplex (picardScalarResolution F))

/-- Extend the actual sections complex by zero to negative degrees.
Source: Stacks, Tag 01DZ (blueprint: lem-sc-picard-kunneth-resolution-model). -/
def picardScalarModel (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) :
    CochainComplex (ModuleCat.{w} k) ℤ :=
  (picardScalarResolutionComplex f F).extend ComplexShape.embeddingUpNat

/-- The constructed model has zero terms in every negative degree.
Source: Stacks, Tag 01DZ (blueprint: lem-sc-picard-kunneth-resolution-model).
Proof: no negative integer is the image of a natural number under the extension embedding. -/
theorem picardScalarModel_negative (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules)
    (p : ℤ) (hp : p < 0) : IsZero ((picardScalarModel f F).X p) := by
  apply HomologicalComplex.isZero_extend_X
  intro n hn
  change (n : ℤ) = p at hn
  omega

/-- The canonical comparison from the homology of the constructed model to scalar cohomology.
No data is selected from an unproved existence statement: all three isomorphisms below
are Mathlib's explicit homology constructions.
Source: Stacks, Tag 01DZ (blueprint: lem-sc-picard-kunneth-resolution-model). -/
def picardScalarModelEquiv (f : X ⟶ Spec (CommRingCat.of k)) (F : X.Modules) (p : ℕ) :
    (picardScalarModel f F).homology (p : ℤ) ≃ₗ[k] scalarCohomology f F p := by
  letI : EnoughInjectives X.Modules :=
    (RingedSpace.moduleSheaves_abelian_enoughInjectives X.toRingedSpace).2
  letI := RingedSpace.globalSectionsFunctor_additive X.toRingedSpace
  let I := picardScalarResolution F
  let R := ModuleCat.restrictScalars (scalarMap f ⊤)
  let K := RingedSpace.globalSectionsComplex I
  let e := (picardScalarResolutionComplex f F).extendHomologyIso
    ComplexShape.embeddingUpNat (j := p) rfl
  let e' := (K.sc p).mapHomologyIso R
  let e'' := R.mapIso (I.isoRightDerivedObj
    (RingedSpace.globalSectionsFunctor X.toRingedSpace) p).symm
  exact (e ≪≫ e' ≪≫ e'').toLinearEquiv

end
end AlgebraicGeometry.Scheme.Modules

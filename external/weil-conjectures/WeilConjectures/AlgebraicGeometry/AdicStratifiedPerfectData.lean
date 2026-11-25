/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.Algebra.Category.ModuleCat.Sheaf.ExtensionTensorComparison
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatAllIndependentCoefficients
public import WeilConjectures.Algebra.Homology.ChangeOfRingsKFlatIndependentCoefficients
public import WeilConjectures.Algebra.Homology.DerivedChangeOfRingsCochainModel
public import WeilConjectures.Algebra.Homology.FlatScalarRestrictionKFlat
public import WeilConjectures.Algebra.Homology.KFlatFixedTensorTriangulated
public import WeilConjectures.Algebra.Homology.KFlatResolution
public import WeilConjectures.Algebra.Homology.SheafRingCoefficientOrdinaryAdjunction
public import WeilConjectures.Algebra.Homology.TensorColimitsIndependentCoefficients
public import WeilConjectures.AlgebraicGeometry.CoefficientRingedSequenceSite
public import WeilConjectures.AlgebraicGeometry.CompletedConstantSheafReduction
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionCompletedFinitePull
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionInverseImageExists
public import WeilConjectures.AlgebraicGeometry.ConstantCompletionKoszulReflector
public import WeilConjectures.AlgebraicGeometry.KFlatRingedToposPullback
public import WeilConjectures.AlgebraicGeometry.ProEtaleOperations
public import WeilConjectures.AlgebraicGeometry.RingedTopoiDerivedPullback
public import WeilConjectures.CategoryTheory.DerivedCategory.LeftDerivedFromResolvingClass
public import WeilConjectures.CategoryTheory.FlatScalarKoszulTowerComparison
public import WeilConjectures.CategoryTheory.NatTransFromResolvingClass
public import WeilConjectures.CategoryTheory.RingedSiteDerivedRestrictionUniverses
public import WeilConjectures.CategoryTheory.RingedToposKFlatPullback
public import WeilConjectures.SecSmoothPurity.CochainTensorCoherenceData
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import WeilConjectures.AlgebraicGeometry.LocallyClosedStratification
public import WeilConjectures.ConstructibleSheaf.Defs
public import WeilConjectures.Mathlib.CategoryTheory.Sites.Monoidal
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.ConcreteCoefficients

/-!
# Definitions for adic constructibility and stratified perfect models

Source: Bhatt--Scholze, Definition 6.5.1, Lemma 6.5.3 and Proposition 6.6.11
(auxiliary; not a blueprint node).

The coefficients are arbitrary complete Noetherian local rings. No finiteness of their
residue fields or perfectness of their quotient modules over the original ring is assumed.

## Main definitions

* `IsSfbAdicConstructible`: completeness and bounded constructible etale residue origin.
* `IsSfbStratifiedPerfect`: finite strata with pro-etale locally perfect coefficient models.
* `SfbAdicConstructibleCategory`: the full ambient subcategory of these objects.

The theorem `adic_stratified_perfect` is proved in
`WeilConjectures.AlgebraicGeometry.AdicStratifiedPerfect`.
This module retains its original coefficient constructions and predicates verbatim.
-/

@[expose] public noncomputable section

set_option autoImplicit false
set_option synthInstance.maxSize 2048
set_option backward.isDefEq.respectTransparency false

universe u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Opposite
open scoped ZeroObject

namespace AlgebraicGeometry.Scheme

/-- Read modules over the constant ring sheaf as fixed-scalar module-valued sheaves,
by restricting along the constant section map, retaining the underlying additive sheaf.
Source: Stacks Tag 093I; Bhatt--Scholze, Definition 6.3.1
(auxiliary; not a blueprint node). -/
def sfbFixedScalarRestriction (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k] :
    proEtaleRingModules X (adicLisseConstantRing X k) ⥤
      Sheaf (ProEt.topology X) (ModuleCat.{u + 1} k) where
  obj M :=
    { obj :=
        { obj := fun U ↦
            ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X k)).obj M.val).obj U
          map := fun f ↦
            ((PresheafOfModules.restrictScalars (adicLisseConstantUnit X k)).obj M.val).map f
          map_id := fun _ ↦ by ext x; simp; rfl
          map_comp := fun _ _ ↦ by ext x; simp; rfl }
      property := Presheaf.isSheaf_of_isSheaf_comp _ _
        (forget₂ (ModuleCat.{u + 1} k) AddCommGrpCat.{u + 1}) M.isSheaf }
  map f := ObjectProperty.homMk
    { app := fun U ↦ (ModuleCat.restrictScalars ((adicLisseConstantUnit X k).app U).hom).map
        (f.val.app U)
      naturality := fun {_ _} g ↦ by ext x; exact PresheafOfModules.naturality_apply f.val g x }

/-- This scalar restriction is additive, since it keeps the underlying additive maps.
Source: Stacks Tag 093I (auxiliary; not a blueprint node). -/
instance sfbFixedScalarRestriction_additive (X : Scheme.{u}) (k : Type (u + 1))
    [CommRing k] : (sfbFixedScalarRestriction X k).Additive where
  map_add := by intros; ext U x; rfl

/-- Tensor a complex of etale module sheaves termwise with a degree-zero module sheaf.
In the application the coefficient ring is a residue field. Every module sheaf is flat,
by the exact conservative geometric stalk functors, so this computes the derived tensor
for every representative complex, including unbounded representatives.
Source: Bhatt--Scholze, Remark 6.3.2 (auxiliary; not a blueprint node). -/
def sfbEtaleTensorDegreeZero (X : Scheme.{u}) (k : Type (u + 1)) [CommRing k]
    (C : CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ)
    (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) :
    CochainComplex (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} k)) ℤ :=
  letI := Sheaf.monoidalCategory X.smallEtaleTopology (ModuleCat.{u + 1} k)
  ((MonoidalCategory.tensorRight N).mapHomologicalComplex (.up ℤ)).obj C

/-- The residue reduction, read in fixed-scalar sheaves using the canonical constant
sections. The projection is to exponent one, written `0+1`, so the coefficient is A/I.
Source: Bhatt--Scholze, Definition 6.5.1
(auxiliary; not a blueprint node). -/
def sfbResidueComplex (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) :
    CochainComplex
      (Sheaf (ProEt.topology X) (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ :=
  ((sfbFixedScalarRestriction X (A ⧸ I ^ (0 + 1))).mapHomologicalComplex (.up ℤ)).obj
    (DerivedCategory.Q.objPreimage
      ((completedAdicDerivedChange X (limit.π (adicLisseRingSystem X I) (op 0))).obj K))

/-- Transport a commutative coefficient sheaf to the equivalent small model of the same
site; only the morphism universe is enlarged.
Source: Stacks Tags 00YY and 099F (auxiliary; not a blueprint node). -/
abbrev sfbModelRings (X : Scheme.{u}) :=
  (AsSmall.down : proEtaleSiteModel X ⥤ X.ProEt).sheafPushforwardContinuous
    CommRingCat.{u + 1} (proEtaleModelTopology X) (ProEt.topology X)

/-- Local derived completeness, using the recorded predicate on the equivalent small
site and the kernel of the actual residue projection. In the Noetherian case this kernel
is exactly the ideal generated by the constant sections in I. Transport a localization
representative termwise, so no choice of a new derived functor is involved.
Source: Stacks Tags 093M and 099F (auxiliary; not a blueprint node). -/
def IsSfbAdicComplete (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  let F := proEtaleModuleToModel ((adicLisseForget X).obj (adicLisseCompletedRing X I))
  letI : F.Additive := ⟨by intros; ext U x; rfl⟩
  ConstantCompletion.IsComplete
    ((sfbModelRings X).map (limit.π (adicLisseRingSystem X I) (op 0)))
    (ConstantCompletion.Q _ |>.obj
      ((F.mapHomologicalComplex (.up ℤ)).obj (DerivedCategory.Q.objPreimage K)))

/-- Condition (a), using the recorded global constructibility predicate. On a Noetherian
scheme this is exactly the affine-local notion as well. Module finiteness means finite
 generation, hence finite presentation over the residue field, never finite underlying sets.
The last clause explicitly tests every degree-zero module sheaf for finite Tor amplitude.
Source: Bhatt--Scholze, Definitions 6.3.1 and 6.5.1, Remark 6.3.2
(auxiliary; not a blueprint node). -/
def IsSfbAdicConstructible (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  IsSfbAdicComplete X I K ∧
    ∃ C : CochainComplex
        (Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1)))) ℤ,
      (∃ a b : ℤ, a ≤ b ∧ ∀ q : ℤ, (q < a ∨ b < q) → IsZero (C.homology q)) ∧
      (∀ q : ℤ, IsConstructibleSheaf (C.homology q)) ∧
      Nonempty (DerivedCategory.Q.obj (sfbResidueComplex X I K) ≅
        DerivedCategory.Q.obj
          (((ProEtale.comparisonUpperStar
            (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))) X).mapHomologicalComplex (.up ℤ)).obj C)) ∧
      ∃ a b : ℤ, a ≤ b ∧
        ∀ (N : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} (A ⧸ I ^ (0 + 1))))
          (q : ℤ), (q < a ∨ b < q) →
            IsZero ((sfbEtaleTensorDegreeZero X (A ⧸ I ^ (0 + 1)) C N).homology q)

/-- The termwise completed realization of an actual coefficient complex. The constant
module functor and scalar extension are the existing sheafification/tensor constructions.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def sfbCompletedModel (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) :
    DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I)) :=
  DerivedCategory.Q.obj
    (((completedAdicChange X (CompletedConstantReduction.base X I)).mapHomologicalComplex
      (.up ℤ)).obj ((CompletedConstantReduction.constantComplex X A).obj P))

/-- Restrict to a stratum, retaining the true inverse-image coefficient ring, and then to
one object of its pro-etale site. For immersions the coefficient identification with the
completion on the stratum is the canonical limit comparison, as in the recorded immersion
limit-preservation lemma.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def sfbLocalRestriction {X S : Scheme.{u}} (i : S ⟶ X)
    (R : Sheaf (ProEt.topology X) CommRingCat.{u + 1}) (U : S.ProEt)
    (K : DerivedCategory (proEtaleRingModules X R)) :=
  let R' := (adicLisseForget S).obj
    ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)
  letI := HasDerivedCategory.standard (SheafOfModules.{u + 1} (R'.over U))
  ringedSiteDerivedRestrictionOfUniverses
    ((adicLisseForget S).obj ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R)) U
    ((proEtaleRingDerivedPullback i R
      ((proEtaleSheafInverseImage i CommRingCat.{u + 1}).obj R) (Iso.refl _)).obj K)

/-- Condition (b): finite constructible locally closed strata, pro-etale covering sieves,
and bounded finite-projective coefficient complexes realizing K there.
Source: Bhatt--Scholze, Proposition 6.6.11
(auxiliary; not a blueprint node). -/
def IsSfbStratifiedPerfect (X : Scheme.{u}) {A : Type (u + 1)} [CommRing A] (I : Ideal A)
    (K : DerivedCategory (proEtaleRingModules X (adicLisseCompletedRing X I))) : Prop :=
  letI := HasDerivedCategory.standard (ModuleCat.{u + 1} A)
  ∃ s : Stratification X,
    (∀ α : Fin s.n, Topology.IsConstructible (s.stratum α)) ∧
    ∀ α : Fin s.n, ∃ V : Sieve (⊤_ (s.domain α).ProEt),
      V ∈ ProEt.topology (s.domain α) (⊤_ (s.domain α).ProEt) ∧
        ∀ (U : (s.domain α).ProEt) (f : U ⟶ ⊤_ (s.domain α).ProEt), V f →
          ∃ (P : CochainComplex (ModuleCat.{u + 1} A) ℤ) (a b : ℤ),
            DerivedCategory.IsPerfectRingComplex (DerivedCategory.Q.obj P) ∧
            P.IsStrictlyGE a ∧ P.IsStrictlyLE b ∧
            (∀ q : ℤ, Module.Projective A (P.X q) ∧ Module.Finite A (P.X q)) ∧
            Nonempty (sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U K ≅
              sfbLocalRestriction (s.immersion α) (adicLisseCompletedRing X I) U
                (sfbCompletedModel X I P))

end AlgebraicGeometry.Scheme

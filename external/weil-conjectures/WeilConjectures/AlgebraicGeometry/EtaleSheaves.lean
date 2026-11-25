/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.FiniteLocallyConstantSets


public import WeilConjectures.Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.HasDerivedCategory
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Sheaf
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence

/-!
# Sheaves on the small étale site

Locally constant and constructible sheaves of sets, and torsion cohomology of
complexes of abelian sheaves, as in blueprint `def-weil-pbc-etale-sheaves` in
`sec-abelian-varieties/lem-sc-finite-etale-points`.

Finite local constancy is the existing `Scheme.IsFiniteLocallyConstantSheafOfTypes`.
Its finiteness condition uses separably closed geometric points. For sheaves of sets,
finitely generated stalks mean finite stalks. The predicates and inverse image below
apply to sets; the corresponding APIs for abelian coefficient categories do not.
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A sheaf of sets on the small étale site of `T` is locally constant when an étale
cover of `T` makes its restriction to each member constant. The restriction `F.over U`
is on the site localized at `U`, equivalent to the small étale site of `U`.
Source: blueprint `def-weil-pbc-etale-sheaves`, locally constant sheaves clause. -/
def IsLocallyConstantEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ 𝒰 : Cover.{u} etalePrecoverage T, ∀ i : 𝒰.I₀,
    (F.over (𝒰.etalePrecoverageToEtale i)).IsConstant
      (T.smallEtaleTopology.over (𝒰.etalePrecoverageToEtale i))

/-- A sheaf of sets is lisse when it is finite locally constant. Finiteness is tested
at separably closed geometric points by `IsFiniteSheaf`, using the existing predicate
for sheaves of sets rather than the abelian-coefficient local-system class.
Source: blueprint `def-weil-pbc-etale-sheaves`, lisse sheaves clause. -/
abbrev IsLisseEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  IsFiniteLocallyConstantSheafOfTypes F

/-- The stalks of a finite locally constant sheaf of sets at separably closed geometric
points are finite. In particular this holds at algebraically closed geometric points. -/
theorem IsFiniteLocallyConstantSheafOfTypes.finite_sheafFiber {T : Scheme.{u}}
    {F : Sheaf T.smallEtaleTopology (Type (u + 1))} (hF : IsFiniteLocallyConstantSheafOfTypes F)
    (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T) :
    Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj F) :=
  (ConcreteCategory.isFinitelyGenerated_iff_finite _).mp
    (hF.2.isFinitelyGenerated_sheafFiber Ω s)

/-- A sheaf of sets is finite locally constant if it is locally constant on an étale cover
and its stalks at separably closed geometric points are finite. -/
theorem isFiniteLocallyConstantSheafOfTypes_of_finite_sheafFiber {T : Scheme.{u}}
    {F : Sheaf T.smallEtaleTopology (Type (u + 1))} (hF : IsLocallyConstantEtaleSheafOfSets F)
    (hfin : ∀ (Ω : Type u) [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ T),
      Finite (((pointSmallEtale s).sheafFiber (A := Type (u + 1))).obj F)) :
    IsFiniteLocallyConstantSheafOfTypes F :=
  ⟨hF, ⟨fun Ω _ _ s ↦ (ConcreteCategory.isFinitelyGenerated_iff_finite _).mpr (hfin Ω s)⟩⟩

/-- Inverse image of sheaves of sets along a morphism of schemes, constructed by left
Kan extension along base change on small étale sites followed by sheafification.
Source: blueprint `def-weil-pbc-etale-sheaves`, restriction to locally closed strata. -/
noncomputable def etaleSetPullback {T Z : Scheme.{u}} (g : Z ⟶ T) :
    Sheaf T.smallEtaleTopology (Type (u + 1)) ⥤
      Sheaf Z.smallEtaleTopology (Type (u + 1)) :=
  Functor.sheafPullbackConstruction.sheafPullback
    (MorphismProperty.Over.pullback @Etale ⊤ g) (Type (u + 1))
    (T.smallGrothendieckTopology @Etale) (Z.smallGrothendieckTopology @Etale)

/-- A sheaf of sets is constructible if a finite stratification into constructible,
locally closed subschemes makes its inverse image to each stratum finite locally constant.
Source: blueprint `def-weil-pbc-etale-sheaves`, constructible sheaves clause. -/
def IsConstructibleEtaleSheafOfSets {T : Scheme.{u}}
    (F : Sheaf T.smallEtaleTopology (Type (u + 1))) : Prop :=
  ∃ S : Stratification T, ∀ i : Fin S.n,
    IsFiniteLocallyConstantSheafOfTypes ((etaleSetPullback (S.immersion i)).obj F)

/-- An object of the unbounded derived category of abelian sheaves has torsion cohomology
when every cohomology sheaf is torsion in the local-section sense. There is no uniform
annihilator or boundedness hypothesis.
Source: blueprint `def-weil-pbc-etale-sheaves`, torsion cohomology clause. -/
def HasTorsionEtaleCohomology {T : Scheme.{u}}
    (K : DerivedCategory (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1})) : Prop :=
  ∀ r : ℤ, CategoryTheory.Sheaf.IsTorsion
    ((DerivedCategory.homologyFunctor
      (Sheaf T.smallEtaleTopology AddCommGrpCat.{u + 1}) r).obj K)

end AlgebraicGeometry.Scheme

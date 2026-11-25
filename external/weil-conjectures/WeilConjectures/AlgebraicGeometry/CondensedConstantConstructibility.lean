/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.ConstructibleSheaf.ProEtaleModule.DerivedCategory
public import WeilConjectures.SixFunctors.ProEtale.ModuleObject.Derived.Tensor

public import Mathlib.AlgebraicGeometry.AffineScheme
/-!
# Constructibility with finite constant scalar models

(blueprint: definition-constructible-sheaves).

A finite presentation over the condensed ring on the point is a finite matrix over
its scalar ring: maps between copies of the regular module are global sections of
the condensed ring. Pulling its cokernel to a scheme therefore gives precisely the
scalar-extension model in the source. The matrix is chosen on the point, before any
scheme restriction, so arbitrary local coefficient functions are not admitted.
-/

@[expose] public section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Limits

open scoped CategoryTheory.Obj

namespace AlgebraicGeometry.ProEtale

variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- A pro-etale cover on which the module is pulled back from a finite presentation
of the condensed ring on the point. Such presentations are finite matrices over
`Λ(*)`, so these are exactly the models `Λ_U ⊗_{Λ(*)} P` for finitely presented P.
Source: blueprint definition-constructible-sheaves, clause 1
(blueprint: definition-constructible-sheaves). -/
def HasFiniteConstantLocalModel (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ 𝒰 : Scheme.Cover.{u} Scheme.proetalePrecoverage X, ∀ i : 𝒰.I₀,
    ∃ P : Mod (Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1}) Λ,
      Mod.IsFinitelyPresented Λ P ∧
      Nonempty ((CondensedRing.upperStar Λ (𝒰.f i)).obj M ≅
        ((upperStarFromPoint (𝒰.X i)).mapMod Λ).obj P)

/-- Constructibility by a finite stratification into constructible locally closed
subschemes, with finite constant scalar models on the strata.
Source: blueprint definition-constructible-sheaves, clause 2 for qcqs schemes
(blueprint: definition-constructible-sheaves). -/
def IsFiniteConstantStratified (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  ∃ S : Scheme.Stratification X, ∀ a : Fin S.n,
    HasFiniteConstantLocalModel Λ (S.domain a)
      ((CondensedRing.upperStar Λ (S.immersion a)).obj M)

open Classical in
/-- On qcqs schemes use a finite constructible stratification; on other schemes impose
this condition on every affine open. Source: blueprint definition-constructible-sheaves, clause 2
(blueprint: definition-constructible-sheaves). -/
def IsConstantModelConstructible (X : Scheme.{u})
    (M : Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X)) : Prop :=
  if CompactSpace X ∧ QuasiSeparatedSpace X then IsFiniteConstantStratified Λ X M
  else ∀ U : X.Opens, IsAffineOpen U →
    IsFiniteConstantStratified Λ U.toScheme ((CondensedRing.upperStar Λ U.ι).obj M)

/-- Bounded complexes whose cohomology module sheaves have finite constant models.
Source: blueprint definition-constructible-sheaves, final paragraph
(blueprint: definition-constructible-sheaves). -/
def constantModelBoundedConstructible (X : Scheme.{u}) :
    ObjectProperty (DerivedCategory
      (Mod (Sheaf (Scheme.ProEt.topology X) Ab.{u + 1}) (condensedRingObj Λ X))) :=
  DerivedCategory.TStructure.t.bounded ⊓ fun K ↦ ∀ n : ℤ,
    IsConstantModelConstructible Λ X ((DerivedCategory.homologyFunctor _ n).obj K)

/-- The full bounded constructible derived category with its ambient derived morphisms.
Source: blueprint definition-constructible-sheaves, final paragraph
(blueprint: definition-constructible-sheaves). -/
abbrev ConstantModelBoundedConstructible (X : Scheme.{u}) :=
  (constantModelBoundedConstructible Λ X).FullSubcategory

end AlgebraicGeometry.ProEtale

namespace AlgebraicGeometry.ProEtale

section

set_option autoImplicit false
open CategoryTheory CategoryTheory.Limits
open scoped CategoryTheory.Obj
variable (Λ : Sheaf (coherentTopology Profinite.{u}) Ab.{u + 1})
  [MonObj Λ] [IsCommMonObj Λ]

/-- The bounded constructible objects of finite Tor amplitude, as a full subcategory.
Source: blueprint definition-constructible-sheaves, final paragraph
(blueprint: definition-constructible-sheaves). -/
abbrev ConstantModelConstructibleFiniteTor (X : Scheme.{u}) :=
  (constantModelBoundedConstructible Λ X ⊓ fun K ↦
    DerivedCategory.finiteTorAmplitude _ K).FullSubcategory

end

end AlgebraicGeometry.ProEtale

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.AffinePushforwardComparisonCoordinates
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization


public import WeilConjectures.Algebra.Homology.AffineTildePushforwardCohomologyNormalization
import all WeilConjectures.Algebra.Homology.MixedTensorUnderlyingHomology

/-! # Composition of the exact homology comparisons in affine pushforward

Source: Stacks Project, Tags 06Z0 and 0AVW.
(blueprint: lem-pc-affine-tilde-pushforward-homology-factorization). -/

@[expose] public section
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
universe u w
open CategoryTheory CategoryTheory.Limits
noncomputable section
namespace AlgebraicGeometry

local instance (priority := 2000) factorCoordinatesCategory (Y : Scheme.{u}) :
    Category Y.Modules := SheafOfModules.instCategory (R := Y.ringCatSheaf)
local instance (priority := 2000) factorCoordinatesPreadditive (Y : Scheme.{u}) :
    Preadditive Y.Modules := SheafOfModules.instPreadditive Y.ringCatSheaf
local instance (priority := 2000) factorCoordinatesAbelian (Y : Scheme.{u}) :
    Abelian Y.Modules := inferInstanceAs (Abelian (SheafOfModules.{u} Y.ringCatSheaf))

attribute [local irreducible] Functor.rightDerivedFunctor Functor.rightDerivedFunctorUnit
  affineTildePushforwardComparison

/-- Inverse homology comparisons compose in the opposite order.
Source: Mathlib's canonical short-complex homology comparison; Stacks, Tag 06Z0.
(blueprint: lem-pc-affine-tilde-pushforward-homology-factorization).

Proof: Cancel the forward comparison for the composite functor. Apply the existing
RingTensorCohomology.mapHomologyIso_hom_comp and cancel the two inverse/forward
pairs, using functoriality. -/
lemma mapHomologyIso_inv_comp
    {C D E : Type*} [Category C] [Category D] [Category E]
    [HasZeroMorphisms C] [HasZeroMorphisms D] [HasZeroMorphisms E]
    (S : ShortComplex C) [S.HasHomology]
    (F : C ⥤ D) (G : D ⥤ E)
    [F.PreservesZeroMorphisms] [G.PreservesZeroMorphisms]
    [F.PreservesHomology] [G.PreservesHomology] [(F ⋙ G).PreservesHomology] :
    (S.mapHomologyIso (F ⋙ G)).inv =
      G.map (S.mapHomologyIso F).inv ≫ ((S.map F).mapHomologyIso G).inv := by
  apply (cancel_mono (S.mapHomologyIso (F ⋙ G)).hom).1
  rw [Iso.inv_hom_id, ← RingTensorCohomology.mapHomologyIso_hom_comp S F G]
  simp only [Category.assoc, Iso.inv_hom_id_assoc, ← CategoryTheory.Functor.map_comp,
    Iso.inv_hom_id, CategoryTheory.Functor.map_id]
  rfl

variable [∀ Y : Scheme.{u},
  HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings Y.toRingedSpace))]

/-- The explicit pushforward cohomology map separates into restriction homology,
exact tilde homology, the quotient/homology comparison, the ordinary termwise
comparison and the actual derived unit. No tensor model or derived counit occurs.
Source: Stacks Project, Tags 06Z0 and 0AVW; definition of the affine pushforward
cohomology comparison.
(blueprint: lem-pc-affine-tilde-pushforward-homology-factorization).

Proof: Set F = restrictScalars psi and T = affinePushforwardTilde B. Expand
affineTildePushforwardCohomologyMap and its comparison-coordinate definition.
Its first factor is the inverse exact homology comparison for F followed by T.
For every short complex S, the canonical comparison for F followed by T is
T applied to the comparison for F, followed by the comparison for T on S.map F.
To verify this identity, compare the cycles maps using the universal property of
cycles (their inclusion is monic), then compare the homology maps using the
universal property of homology (the cycles projection is epic). Invert this
identity: the inverse comparison for F followed by T equals T applied to the
inverse comparison for F, followed by the inverse comparison for T on S.map F.
Apply this with S = Cg.sc i and compose the equality on the right with the
quotient/homology comparison, homology of the termwise ordinary comparison and
homology of the right-derived unit. The component inverse of the natural
quotient/homology isomorphism is its inverse natural transformation's component.
All remaining factors are exactly those in the defining formula. Compose on
the left with T.map v and use functoriality to combine its first two maps. This argument
uses only exactness of restriction and tilde, holds for all unbounded complexes,
and also applies to the zero complex and to zero rings. -/
theorem affineTildePushforwardHomologyFactorization
    (D B : Type u) [CommRing D] [CommRing B] (ψ : B →+* D)
    [(affinePushforwardTilde D ⋙
      Scheme.Modules.pushforward (Spec.map (CommRingCat.ofHom ψ))).PreservesZeroMorphisms]
    (Cg : CochainComplex (ModuleCat.{u} D) ℤ) (i : ℤ)
    (S : ModuleCat.{u} B)
    (v : S ⟶ (ModuleCat.restrictScalars ψ).obj (Cg.homology i)) :
    let T := affinePushforwardTilde B
    let _ : T.Additive := by
      constructor
      intro M N f g
      exact tilde.map_add (R := .of B) f g
    let _ : T.PreservesHomology := tilde_preservesHomology B
    let H := DerivedCategory.homologyFunctor
      (SheafOfModules.{u} (moduleRings (Spec (.of B)).toRingedSpace)) i
    let σ := affineTildePushforwardComparison D B ψ
    let a := (σ.hom.mapHomologicalComplex
      (.up ℤ)).app Cg
    let β := (RingedSpace.moduleDirectImage
      (Spec.map (CommRingCat.ofHom ψ)).toLRSHom.toShHom).rightDerivedFunctorUnit.app
        ((HomotopyCategory.quotient _ (.up ℤ)).obj
          (((affinePushforwardTilde D).mapHomologicalComplex (.up ℤ)).obj Cg))
    T.map (v ≫ ((Cg.sc i).mapHomologyIso (ModuleCat.restrictScalars ψ)).inv) ≫
        (((((ModuleCat.restrictScalars ψ).mapHomologicalComplex
          (.up ℤ)).obj Cg).sc i).mapHomologyIso T).inv ≫
        (DerivedCategory.homologyFunctorFactors _ i).inv.app
          ((T.mapHomologicalComplex (.up ℤ)).obj
            (((ModuleCat.restrictScalars ψ).mapHomologicalComplex (.up ℤ)).obj Cg)) ≫
        H.map (DerivedCategory.Q.map a) ≫ cast (by rfl) (H.map β) =
    T.map v ≫ affineTildePushforwardCohomologyMap D B ψ Cg i := by
  let T := affinePushforwardTilde B
  let : T.Additive := by
    constructor
    intro M N f g
    exact tilde.map_add (R := .of B) f g
  let : T.PreservesHomology := tilde_preservesHomology B
  let : PreservesFiniteLimits T := T.preservesFiniteLimits_of_preservesHomology
  let : PreservesFiniteColimits T := T.preservesFiniteColimits_of_preservesHomology
  have hc := mapHomologyIso_inv_comp (Cg.sc i) (ModuleCat.restrictScalars ψ) T
  dsimp only [affineTildePushforwardCohomologyMap,
    affinePushforwardCohomologyMapOfComparison]
  erw [hc]
  simp only [Functor.map_comp, Category.assoc]
  rfl

end AlgebraicGeometry

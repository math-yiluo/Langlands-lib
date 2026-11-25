/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module

public import WeilConjectures.AlgebraicGeometry.Ordinary.OrdinarySupportedKummerScalarSupplement
public import WeilConjectures.SixFunctors.Etale.Derived.RestrictScalarsLowerStar

/-!
# Normalized ordinary scalar maps for arbitrary coefficient homomorphisms

Source: literature/blueprint/latest/blueprint/sec-six-functors-basics/sk-lem-geo-cartier/
lem-amb-cartier-kummer-map.proof.md, final scalar-extension paragraph
(blueprint: lem-asd-supported-kummer-arbitrary-scalar-maps).
-/
@[expose] public noncomputable section

set_option autoImplicit false

universe u

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor

namespace AlgebraicGeometry.Etale

/--
For arbitrary commutative rings and a closed immersion, normalized coefficient maps exist on
both small étale sites.  Their components send a constant `r` to the constant `φ r`.
The direct-image composite is the corresponding restriction-of-scalars map on the ambient site,
with the same component formula.  The three proof steps are: (1) factor the sectionwise map from
the constant presheaf through sheafification on each site; (2) evaluate the factorization on every
étale object, including empty objects and zero rings; (3) use the objectwise direct-image formula
and `lowerStarCompRestrictScalarsIso` to identify the two restriction-of-scalars direct images.
The constructions use `def-weil-pbc-constant-sheaf`, `def-pc-sheaf-restrict-scalars`,
`def-weil-pbc-sheafification`, and `def-weil-pbc-direct-image`; the resulting ambient map has the
source and target required by `def-asd-ordinary-supported-kummer-scalar`.
Source: the final scalar-extension paragraph of the blueprint proof cited above
(blueprint: lem-asd-supported-kummer-arbitrary-scalar-maps).
-/
theorem exists_supported_kummer_arbitrary_scalar_maps
    {R S : Type (u + 1)} [CommRing R] [CommRing S] (φ : R →+* S)
    {D T : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i] :
    ∃ (ηD : ordinaryFiniteConstant R D ⟶
        (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant S D))
      (ηT : ordinaryFiniteConstant R T ⟶
        (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant S T)),
      (∀ (U : D.Etaleᵒᵖ) (r : R),
        ηD.hom.app U
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app U r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app U (φ r)) ∧
      (∀ (U : T.Etaleᵒᵖ) (r : R),
        ηT.hom.app U
          ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app U r) =
        (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app U (φ r)) ∧
      lowerStarCompRestrictScalarsIso φ i = Iso.refl _ ∧
      (∀ (W : T.Etaleᵒᵖ) (r : R),
        ((lowerStar (ModuleCat.{u + 1} R) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso φ i).inv.app
            (ordinaryFiniteConstant S D)).hom.app W
          ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
            (ModuleCat.of R R))).app (i.Etale.op.obj W) r) =
        (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of S S))).app (i.Etale.op.obj W) (φ r)) := by
  let c : ModuleCat.of R R ⟶
      (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S) :=
    ModuleCat.ofHom (X := ModuleCat.of R R)
      (Y := (ModuleCat.restrictScalars φ).obj (ModuleCat.of S S))
      { toFun := φ
        map_add' := φ.map_add
        map_smul' := fun r x ↦ φ.map_mul r x }
  let a (X : Scheme.{u}) :
      (Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of R R) ⟶
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj
          (ordinaryFiniteConstant S X)).obj :=
    (Functor.const X.Etaleᵒᵖ).map c ≫
      Functor.whiskerRight
        (toSheafify X.smallEtaleTopology
          ((Functor.const X.Etaleᵒᵖ).obj (ModuleCat.of S S)))
        (ModuleCat.restrictScalars φ)
  let η (X : Scheme.{u}) : ordinaryFiniteConstant R X ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).obj
        (ordinaryFiniteConstant S X) :=
    ⟨sheafifyLift X.smallEtaleTopology (a X)
      ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj
        (ordinaryFiniteConstant S X)).property⟩
  have hη (X : Scheme.{u}) (U : X.Etaleᵒᵖ) (r : R) :
      (η X).hom.app U
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of S S))).app U (φ r) := by
    have hfac :
        toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of R R)) ≫ (η X).hom = a X := by
      dsimp only [η]
      exact toSheafify_sheafifyLift X.smallEtaleTopology (a X)
        ((Sheaf.restrictScalars X.smallEtaleTopology φ).obj
          (ordinaryFiniteConstant S X)).property
    calc
      _ = (a X).app U r := by
        exact ConcreteCategory.congr_hom (NatTrans.congr_app hfac U) r
      _ = _ := by rfl
  refine ⟨η D, η T, hη D, hη T, rfl, ?_⟩
  intro W r
  change (η D).hom.app (i.Etale.op.obj W)
      ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of R R))).app (i.Etale.op.obj W) r) = _
  exact hη D (i.Etale.op.obj W) r

end AlgebraicGeometry.Etale

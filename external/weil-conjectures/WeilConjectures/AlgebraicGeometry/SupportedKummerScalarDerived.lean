/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/
module
public import Mathlib.Algebra.Category.ModuleCat.Products
public import WeilConjectures.AlgebraicGeometry.OrdinarySupportedKummerScalar
public import WeilConjectures.SixFunctors.BaseChange.RestrictScalars
import WeilConjectures.AlgebraicGeometry.FiniteOrdinaryScalarUnit
import WeilConjectures.CategoryTheory.Abelian.Flat.ModuleCat
import WeilConjectures.CategoryTheory.FlatScalarUnit
import WeilConjectures.SixFunctors.Etale.UpperLowerStar.FlatModuleCat
import WeilConjectures.SixFunctors.Finite.Stalk
public import Mathlib.Algebra.Category.ModuleCat.Products

/-! Derived universal properties of normalized supported scalar maps.
Source: Stacks Project, Tags 03QP, 03Q1 and 06YY
(auxiliary; not a blueprint node). -/
@[expose] public noncomputable section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open scoped CategoryTheory.Functor
namespace AlgebraicGeometry.Etale

attribute [local instance 10000] SheafExactDegreeZero.scalarWeakSheafify

private theorem constant_flat (X : Scheme.{u}) (R : Type (u + 1)) [CommRing R] :
    ObjectProperty.flat (ordinaryFiniteConstant R X) := by
  exact ObjectProperty.prop_unit ObjectProperty.flat

private theorem ring_hom_eval_one_bijective (R : Type (u + 1)) [CommRing R]
    (M : ModuleCat.{u + 1} R) :
    Function.Bijective (fun f : ModuleCat.of R R ⟶ M ↦ f (1 : R)) := by
  constructor
  · intro f g h
    apply ModuleCat.hom_ext
    exact LinearMap.ext_ring h
  · intro m
    exact ⟨ModuleCat.ofHom (LinearMap.toSpanSingleton R M m), by simp⟩

private theorem constant_ordinary_scalar_unit
    (X : Scheme.{u}) {R A : Type (u + 1)} [CommRing R] [CommRing A]
    (φ : R →+* A)
    (η : ordinaryFiniteConstant R X ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).obj (ordinaryFiniteConstant A X))
    (hη : ∀ (U : X.Etaleᵒᵖ) (r : R),
      η.hom.app U
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app U r) =
      (toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app U (φ r)) :
    ∀ H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} A),
      Function.Bijective (fun f : ordinaryFiniteConstant A X ⟶ H ↦
        η ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map f) := by
  intro H
  let t : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  let aR := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} R) t
  let aA := constantSheafAdj X.smallEtaleTopology (ModuleCat.{u + 1} A) t
  let eR := fun f : ordinaryFiniteConstant R X ⟶
      (Sheaf.restrictScalars X.smallEtaleTopology φ).obj H ↦
    (aR.homEquiv _ _ f) (1 : R)
  let eA := fun f : ordinaryFiniteConstant A X ⟶ H ↦ (aA.homEquiv _ _ f) (1 : A)
  have bR : Function.Bijective eR :=
    (ring_hom_eval_one_bijective R _).comp (aR.homEquiv _ _).bijective
  have bA : Function.Bijective eA :=
    (ring_hom_eval_one_bijective A _).comp (aA.homEquiv _ _).bijective
  have he (f : ordinaryFiniteConstant A X ⟶ H) :
      eR (η ≫ (Sheaf.restrictScalars X.smallEtaleTopology φ).map f) = eA f := by
    change f.hom.app (op (Scheme.Etale.mk (𝟙 X)))
      (η.hom.app (op (Scheme.Etale.mk (𝟙 X)))
        ((toSheafify X.smallEtaleTopology ((Functor.const X.Etaleᵒᵖ).obj
          (ModuleCat.of R R))).app _ (1 : R))) = _
    rw [hη, map_one]
    rfl
  constructor
  · intro f g h
    apply bA.1
    exact (he f).symm.trans ((congrArg eR h).trans (he g))
  · intro f
    obtain ⟨g, hg⟩ := bA.2 (eR f)
    exact ⟨g, bR.1 ((he g).trans hg)⟩

private theorem finite_constant_flat
    (T : Scheme.{u}) (R : Type (u + 1)) [CommRing R]
    {D : Scheme.{u}} (i : D ⟶ T) [IsFinite i] :
    ObjectProperty.flat ((lowerStar (ModuleCat.{u + 1} R) i).obj
      (ordinaryFiniteConstant R D)) := by
  classical
  apply GrothendieckTopology.flat_of_forall_flat_sheafFiber_obj
    (Scheme.jointlyReflectIsomorphisms_ulift_pointSmallEtale T (ModuleCat.{u + 1} R))
  rintro ⟨-, ⟨x⟩⟩
  let s := T.algClosurePoint x
  let E := Scheme.Hom.GeometricFiber i s
  have : PreservesFilteredColimitsOfSize.{u, u}
      (forget (ModuleCat.{u + 1} R)) :=
    preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1}
      (forget (ModuleCat.{u + 1} R))
  let e : (T.uliftPointSmallEtale x).sheafFiber.obj
      ((lowerStar (ModuleCat.{u + 1} R) i).obj (ordinaryFiniteConstant R D)) ≅
      ModuleCat.of R (E → R) :=
    ((Scheme.pointSmallEtale s).uliftSheafFiberIso.{u + 1}
      (ModuleCat.{u + 1} R)).app _ ≪≫
      stalkIsoPi (ModuleCat.{u + 1} R) i s (ordinaryFiniteConstant R D) ≪≫
      Pi.mapIso (fun t : E ↦ (Scheme.pointSmallEtale t.1).sheafFiberConstantSheafIso
        (ModuleCat.of R R)) ≪≫
      ModuleCat.piIsoPi.{u + 1, u, u + 1} (fun _ : E ↦ ModuleCat.of R R)
  have : Fintype E := Fintype.ofFinite E
  exact ObjectProperty.prop_of_iso ObjectProperty.flat e.symm
    ((ModuleCat.flat_iff_flat _).2 inferInstance)

/-- The normalized coefficient maps give the three derived scalar-extension units.
Source: Stacks Project, etale-cohomology Tag 03QP (finite stalk formula),
sites-cohomology Tags 06YQ, 06YY and 07A6 (flat-source derived scalar adjunction).
(auxiliary; not a blueprint node).

Proof: Constant R-module sheaves are the monoidal units, hence flat. A closed immersion
is finite. By the finite-stalk formula, every geometric stalk of i_*R_D is a finite
product of copies of R. Identify it with the finite free module R^E using the constant
stalk isomorphisms. The geometric-stalk criterion then proves flatness of i_*R_D.
This argument includes empty geometric fibres and needs no restriction on the rings.

The constant-sheaf/global-sections adjunction and evaluation of a linear map at 1
identify maps from R_X and from A_X to an A-module sheaf with the same section set.
The generator equations hD and hT identify composition with the prescribed coefficient
maps with the identity of that section set. Thus both constant maps are ordinary
scalar-extension units. Finite direct image preserves the ordinary universal property
by finite_ordinary_scalar_unit, with exactly the inverse restriction comparison in
the statement. Finally scalarUniversal_of_flat passes each of these three ordinary
units to the unbounded derived unit, using the flat source just proved. Unfold the
named supported scalar-unit property and assemble the three conclusions. -/
theorem supported_kummer_scalar_derived_units
    (T : Scheme.{u}) (R A : Type (u + 1)) [CommRing R] [CommRing A] (φ : R →+* A)
    {D : Scheme.{u}} (i : D ⟶ T) [IsClosedImmersion i]
    (ηD : ordinaryFiniteConstant (R) D ⟶
      (Sheaf.restrictScalars D.smallEtaleTopology φ).obj (ordinaryFiniteConstant A D))
    (ηT : ordinaryFiniteConstant (R) T ⟶
      (Sheaf.restrictScalars T.smallEtaleTopology φ).obj (ordinaryFiniteConstant A T))
    (hD : ∀ (U : D.Etaleᵒᵖ) (r : R),
      ηD.hom.app U
        ((toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
          (ModuleCat.of (R) (R)))).app U r) =
      (toSheafify D.smallEtaleTopology ((Functor.const D.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app U (φ r))
    (hT : ∀ (U : T.Etaleᵒᵖ) (r : R),
      ηT.hom.app U
        ((toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
          (ModuleCat.of (R) (R)))).app U r) =
      (toSheafify T.smallEtaleTopology ((Functor.const T.Etaleᵒᵖ).obj
        (ModuleCat.of A A))).app U (φ r)) :
    SupportedDerivedScalarUnit φ D
        (ordinaryFiniteConstant (R) D)
        (ordinaryFiniteConstant A D) ηD ∧
      SupportedDerivedScalarUnit φ T
        ((lowerStar (ModuleCat.{u + 1} (R)) i).obj
          (ordinaryFiniteConstant (R) D))
        ((lowerStar (ModuleCat.{u + 1} A) i).obj (ordinaryFiniteConstant A D))
        ((lowerStar (ModuleCat.{u + 1} (R)) i).map ηD ≫
          (lowerStarCompRestrictScalarsIso φ i).inv.app (ordinaryFiniteConstant A D)) ∧
      SupportedDerivedScalarUnit φ T
        (ordinaryFiniteConstant (R) T)
        (ordinaryFiniteConstant A T) ηT := by
  have hd := constant_ordinary_scalar_unit D φ ηD hD
  have ht := constant_ordinary_scalar_unit T φ ηT hT
  have hs := finite_ordinary_scalar_unit T φ i
    (ordinaryFiniteConstant R D) (ordinaryFiniteConstant A D) ηD hd
  refine ⟨?_, ?_, ?_⟩
  · unfold SupportedDerivedScalarUnit
    exact SheafExactDegreeZero.scalarUniversal_of_flat D.smallEtaleTopology φ _ _ ηD
      (constant_flat D R) hd
  · unfold SupportedDerivedScalarUnit
    exact SheafExactDegreeZero.scalarUniversal_of_flat T.smallEtaleTopology φ _ _ _
      (finite_constant_flat T R i) hs
  · unfold SupportedDerivedScalarUnit
    exact SheafExactDegreeZero.scalarUniversal_of_flat T.smallEtaleTopology φ _ _ ηT
      (constant_flat T R) ht
end AlgebraicGeometry.Etale

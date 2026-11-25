/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.DirectImageAlgebraDerivedCategory
public import WeilConjectures.AlgebraicGeometry.RingedSpaceDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.Adjunction
public import Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.Localization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraKInjectiveCounitHomologyFactorization
import WeilConjectures.AlgebraicGeometry.AffineAlgebraModuleAdjunctionCounitIso
import WeilConjectures.CategoryTheory.DerivedCategory.RightDerivedFunctor.KInjective

/-! # The canonical exact-derived affine algebra counit

Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof.
(blueprint: lem-sc-affine-algebra-exact-derived-counit-iso).
-/

@[expose] public section

universe v wX wA

open CategoryTheory

namespace AlgebraicGeometry

/-- The counit of the canonical derived adjunction of an exact affine algebra pullback
is invertible on complexes with quasi-coherent cohomology.
Source: Stacks Project, Tag 0AVW, perfect-lemma-affine-morphism-equivalence, proof;
Tag 079W, cohomology-lemma-adjoint, for the derived counit construction.
(blueprint: lem-sc-affine-algebra-exact-derived-counit-iso).

Proof: Put g : (X,O_X) -> (Y,f_*O_X). Exact restriction of algebra scalars to O_Y
identifies Rg_* followed by restriction with Rf_*. It uses the same K-injective
resolution and the identity g_* followed by restriction = f_*. On each affine open,
the unbounded affine cohomology calculation (0AVW, using the bound of 08D4)
identifies H^i(Rg_*K) with g_*H^i(K), with its f_*O_X action. These identifications
are natural in K and in open restrictions. Exact P commutes with cohomology, so
H^i(P.mapDerivedCategory(Rg_*K)) identifies with P(g_*H^i(K)).
The canonical derived adjunction is constructed from the termwise adjunction and
the right-derived comparison. Its counit equation (Adjunction.derived_counit,
or derivedε_fac_app) identifies its cohomology map with the ordinary counit under
these comparisons: represent K by its K-injective resolution, where the
right-derived comparison is invertible, and apply the termwise counit equation.
The kernel and image maps giving the homology comparisons commute with that
counit. On affine opens this is evaluation, sending a pure tensor b tensor s to
b*s. The ordinary affine module correspondence makes this evaluation invertible
for H^i(K), which is quasi-coherent. Thus the canonical derived counit induces
an isomorphism in every degree, and the derived homology criterion makes it an
isomorphism. An arbitrary underived adjunction a is transported from tensor
pullback by uniqueness of left adjoints; functoriality of the canonical derived
adjunction transports its counit, preserving invertibility. The argument uses
all integer degrees and includes empty schemes and zero cohomology. It does not
use any derived unit isomorphism or unit homology factorization. -/
theorem affine_algebra_exact_derived_counit_isIso
    {X Y : Scheme.{v}} (f : X ⟶ Y) [IsAffineHom f]
    [HasDerivedCategory.{wX} (SheafOfModules.{v} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{wA} (SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)))]
    (P : SheafOfModules.{v} (moduleRings (directImageAlgebraSpace f)) ⥤
      SheafOfModules.{v} (moduleRings X.toRingedSpace))
    [P.Additive] [Limits.PreservesFiniteLimits P] [Limits.PreservesFiniteColimits P]
    (a : P ⊣ RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f))
    (K : schemeDerivedCategory X) (hK : schemeDerivedQCohProperty X K) :
    IsIso ((a.mapDerivedCategoryRightDerivedAdjunction).counit.app K) := by
  let C := SheafOfModules.{v} (moduleRings X.toRingedSpace)
  let R := RingedSpace.moduleDirectImage (toDirectImageAlgebraSpace f)
  obtain ⟨I, hI, ⟨e⟩⟩ := DerivedCategory.exists_iso_Q_obj_of_isKInjective K
  have : I.IsKInjective := hI
  have hIQ : ∀ n : ℤ, (I.homology n).IsQuasicoherent := by
    intro n
    let c := (DerivedCategory.homologyFunctor C n).mapIso e ≪≫
      (DerivedCategory.homologyFunctorFactors C n).app I
    exact (SheafOfModules.isQuasicoherent (moduleRings X.toRingedSpace)).prop_of_iso
      c (hK n)
  have hq : QuasiIso ((a.mapHomologicalComplex (.up ℤ)).counit.app I) := by
    rw [quasiIso_iff]
    intro n
    rw [quasiIsoAt_iff_isIso_homologyMap]
    obtain ⟨c, hc⟩ := affine_algebra_kinjective_counit_homology_factorization f P a I hIQ n
    have : R.IsRightAdjoint := a.isRightAdjoint
    let b := Adjunction.ofIsRightAdjoint R
    have : IsIso (b.counit.app (I.homology n)) :=
      affine_algebra_module_adjunction_counit_iso f _ (hIQ n)
    have : IsIso (a.counit.app (I.homology n)) := by
      rw [← a.leftAdjointUniq_hom_app_counit b (I.homology n)]
      infer_instance
    rw [hc]
    infer_instance
  let J := (HomotopyCategory.quotient C (.up ℤ)).obj I
  have hε := (a.mapHomotopyCategory (.up ℤ)).derivedε_fac_app
    (HomotopyCategory.quasiIso C (.up ℤ))
    P.mapDerivedCategoryFactorsh.hom R.rightDerivedFunctorUnit J
  have hQ : IsIso (DerivedCategory.Qh.map ((a.mapHomotopyCategory (.up ℤ)).counit.app J)) := by
    dsimp [J]
    rw [Adjunction.mapHomotopyCategory_counit_app_quotient]
    have : IsIso (DerivedCategory.Q.map ((a.mapHomologicalComplex (.up ℤ)).counit.app I)) :=
      inferInstance
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso C)
      ((a.mapHomologicalComplex (.up ℤ)).counit.app I)).mp this
  have hderived : IsIso (a.mapDerivedCategoryRightDerivedAdjunction.counit.app
      (DerivedCategory.Qh.obj J)) := by
    have : IsIso (P.mapDerivedCategory.map (R.rightDerivedFunctorUnit.app J)) := by
      dsimp [J]
      infer_instance
    exact IsIso.of_isIso_fac_left hε
  have : IsIso (a.mapDerivedCategoryRightDerivedAdjunction.counit.app
      ((HomotopyCategory.quotient C (.up ℤ) ⋙ DerivedCategory.Qh).obj I)) := hderived
  let c := e ≪≫ ((DerivedCategory.quotientCompQhIso C).app I).symm
  have he := a.mapDerivedCategoryRightDerivedAdjunction.counit.naturality c.hom
  exact IsIso.of_isIso_fac_right he.symm

end AlgebraicGeometry

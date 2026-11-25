/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.AffinePerfectModuleModel
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
public import WeilConjectures.CategoryTheory.DerivedCategory.TorAmplitude
public import WeilConjectures.CategoryTheory.GrothendieckAbelian.Monoidal.FlatResolution
import WeilConjectures.AlgebraicGeometry.AffineTorAmplitudeCriterion
import WeilConjectures.AlgebraicGeometry.AffineSheafificationTensorVanishingTest

/-! # Tor bounds for an affine module model

Source: Stacks Project, Tags 08CG, 08E9 and 08DX.
(blueprint: lem-pc-affine-sheafification-tor-amplitude).
-/

@[expose] public section

universe u w wR

open CategoryTheory

namespace AlgebraicGeometry.Scheme

/-- A module complex representing the restriction of a finite-Tor-dimensional object
has finite Tor amplitude over the ring of the affine open. No pseudo-coherence or
boundedness of the representative is assumed.
Source: Stacks Project, Tag 08CG (locality), Tag 08E9(1), and Tag 08DX(2).
(blueprint: lem-pc-affine-sheafification-tor-amplitude).

Proof: Choose the global interval [a,b] in the hypothesis. For any module sheaf G on U,
test the global vanishing on its direct image under the open immersion. Restriction of
that tensor product is the tensor of the restricted object with G, since restriction is
exact, commutes with tensor, and the restriction of the direct image is G. Thus the same
interval works on U. Transport to Spec Gamma(U,O) through isoSpec and overEquiv; these
exact equivalences preserve tensor and cohomology. The given representing isomorphism
identifies the transported object with the termwise tilde complex of P. Apply the affine
Tor-amplitude criterion (Tag 08E9): test with tilde N for each ring module N, compute with
a K-flat resolution of P, and use the affine tensor comparison. Exact faithful tilde
detects the zero cohomology modules outside [a,b]. This gives the asserted module Tor
amplitude, with the original bounds. The argument includes empty affine opens, zero
rings, zero complexes and unbounded representatives. -/
theorem finiteTorAmplitude_of_affine_sheafification (S : Scheme.{u})
    [HasDerivedCategory.{w} (SheafOfModules.{u} (moduleRings S.toRingedSpace))]
    [∀ V : S.Opens,
      HasDerivedCategory.{w} (SheafOfModules.{u} ((moduleRings S.toRingedSpace).over V))]
    (U : S.Opens) (hU : IsAffineOpen U)
    [HasDerivedCategory.{wR} (ModuleCat.{u} (S.presheaf.obj (.op U)))]
    (K : schemeDerivedCategory S)
    (P : CochainComplex (ModuleCat.{u} (S.presheaf.obj (.op U))) ℤ)
    (hP : Nonempty ((SheafOfModules.overFunctor.{u}
      (moduleRings S.toRingedSpace) U).mapDerivedCategory.obj K ≅
        DerivedCategory.Q.obj
          (((affinePerfectSheafification S U hU).mapHomologicalComplex (.up ℤ)).obj P)))
    (hTor : HasFiniteTorDimension S K) :
    ∃ a b : ℤ, a ≤ b ∧ DerivedCategory.torAmplitudeIn
      (ModuleCat.{u} (S.presheaf.obj (.op U))) a b (DerivedCategory.Q.obj P) := by
  let : HasDerivedCategory.{u + 1} (SheafOfModules.{u}
      (moduleRings (Spec (S.presheaf.obj (.op U))).toRingedSpace)) :=
    HasDerivedCategory.standard _
  obtain ⟨a, b, hab, hvan⟩ := hTor
  refine ⟨a, b, hab, (affine_torAmplitude_iff (S.presheaf.obj (.op U)) P a b hab).mp ?_⟩
  intro G i hi
  exact affine_sheafification_tensor_vanishing_test S U hU K P hP G i
    (hvan ((Modules.pushforward (hU.isoSpec.inv ≫ U.ι)).obj G) i hi)

end AlgebraicGeometry.Scheme

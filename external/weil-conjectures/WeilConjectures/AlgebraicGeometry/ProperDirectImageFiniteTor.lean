/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.FiniteTorDimensionOver
public import WeilConjectures.AlgebraicGeometry.FiniteTorDimension
public import WeilConjectures.AlgebraicGeometry.ClosedSubsetProperOverBase
public import WeilConjectures.AlgebraicGeometry.Coherent
public import WeilConjectures.AlgebraicGeometry.SchemeDerivedDirectImage
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Noetherian
import WeilConjectures.AlgebraicGeometry.CoherentFiniteTypeLocallyNoetherian
import WeilConjectures.AlgebraicGeometry.DerivedTensorUpperBound
import WeilConjectures.AlgebraicGeometry.DirectImageBoundedCoherent
import WeilConjectures.AlgebraicGeometry.ProperDirectImageTensorLowerBound
import WeilConjectures.AlgebraicGeometry.TorAmplitudeQCohTest

/-! # Proper-support direct image of a finite-Tor complex

Source: Stacks Project, Derived Categories of Schemes, Lemma 36.27.1 (Tag 08EV),
proof from “Hence it suffices to show that Rf_*E has finite tor dimension” to the end
(blueprint: lem-pc-proper-direct-image-finite-tor).
-/

@[expose] public section

universe u₁ v₁
universe w₁

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme

/-- A bounded coherent complex with proper cohomological support and finite Tor dimension
over the inverse-image structure sheaf has a derived direct image of finite Tor dimension.
Source: Stacks Project, Tag 08EV, finite-Tor paragraph.
(blueprint: lem-pc-proper-direct-image-finite-tor)

Proof:
1. Proper-support direct image preserves bounded coherent cohomology. Coherence on the
   Noetherian base implies quasi-coherence of each cohomology sheaf.
2. The projection-formula lower-bound argument gives a uniform lower tensor bound a
   for all quasi-coherent modules; this argument is split into its own statement.
3. If b bounds the cohomology of the direct image above, a bounded-above flat replacement
   proves that tensor with any module in degree zero has no cohomology above b.
4. Use [a,max a b] to ensure an ordered interval, combine the two bounds, and apply the
   quasi-coherent test criterion to extend the interval to every module sheaf.
-/
theorem hasFiniteTorDimension_schemeDerivedDirectImage_of_bounded_coherent_support
    (S : Scheme.{u₁}) [IsNoetherian S]
    (X : Scheme.{u₁}) (f : X ⟶ S) [LocallyOfFiniteType f]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings X.toRingedSpace))]
    [HasDerivedCategory.{w₁} (SheafOfModules.{u₁} (moduleRings S.toRingedSpace))]
    (E : schemeDerivedCategory X)
    (hbounded : ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hcoherent : ∀ i : ℤ,
      RingedSpace.IsCoherent X.toRingedSpace
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hsupport : ∀ i : ℤ,
      Scheme.Modules.HasSupportProperOver f
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E))
    (hTor : HasFiniteTorDimensionOver f E) :
    HasFiniteTorDimension S ((schemeDerivedDirectImage f).obj E) := by
  have hb : ∃ a b : ℤ, ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor
        (SheafOfModules.{u₁} (moduleRings X.toRingedSpace)) i).obj E) := by
    obtain ⟨a, b, _, h⟩ := hbounded
    exact ⟨a, b, h⟩
  obtain ⟨himage, hcoh⟩ := directImage_isBounded_coherent f E hb hcoherent hsupport
  obtain ⟨a, ha⟩ := exists_schemeDerivedDirectImage_tensor_lower_bound
    S X f E hb hcoherent hsupport hTor
  obtain ⟨_, b, hupper⟩ := himage
  have hqc : schemeDerivedQCohProperty S ((schemeDerivedDirectImage f).obj E) := by
    intro i
    exact ((Modules.isCoherent_iff_isQuasicoherent_and_isFiniteType S _).1 (hcoh i)).1
  refine ⟨a, max a b, le_max_left _ _, ?_⟩
  apply torAmplitude_of_quasiCoherent_tests S _ hqc a (max a b) (le_max_left _ _)
  intro F hF i hi
  rcases hi with hi | hi
  · exact ha F hF i hi
  · apply schemeDerivedTensorCohomologyVanishes_of_upper_bound S _ b
      (fun j hj ↦ hupper j (Or.inr hj)) F i
    exact lt_of_le_of_lt (le_max_right a b) hi

end AlgebraicGeometry.Scheme

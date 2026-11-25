/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentCoproduct
import WeilConjectures.AlgebraicGeometry.SigmaDescRestrictIsIso

@[expose] public section
universe u
open CategoryTheory
namespace AlgebraicGeometry

/-- Dense-open component modification gluing for a nonempty finite family.
The proof follows the componentwise construction in the parent theorem: remove all
other components, restrict each dense isomorphism, and glue the resulting local
isomorphisms.
(blueprint: lem-weil-pbc-dense-open-component-modifications-nonempty) -/
theorem exists_dense_open_isIso_component_modifications_of_pos
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (hn : 0 < n) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin n → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i) ∣_ U) := by
  classical
  let : NeZero n := ⟨Nat.ne_of_gt hn⟩
  choose V hV hνV using hν
  obtain ⟨U, hU, hιU, hUV⟩ :=
    exists_dense_open_component_coproduct X n C ι hC hinj hcover V hV
  refine ⟨U, hU, isIso_sigmaDesc_comp_restrict X n C Y ι ν U hιU ?_⟩
  intro i
  have h := IsZariskiLocalAtTarget.restrict (P := MorphismProperty.isomorphisms Scheme)
    (hνV i) ((V i).ι ⁻¹ᵁ (ι i ⁻¹ᵁ U))
  have h' := (MorphismProperty.arrow_mk_iso_iff (MorphismProperty.isomorphisms Scheme)
    (morphismRestrictRestrict (ν i) (V i) ((V i).ι ⁻¹ᵁ (ι i ⁻¹ᵁ U)))).mp h
  change IsIso (ν i ∣_ (V i).ι ''ᵁ ((V i).ι ⁻¹ᵁ (ι i ⁻¹ᵁ U))) at h'
  rwa [Scheme.Hom.image_preimage_eq_opensRange_inf,
    Scheme.Opens.opensRange_ι, inf_eq_right.mpr (hUV i)] at h'

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import Mathlib.AlgebraicGeometry.Limits
public import Mathlib.AlgebraicGeometry.Properties
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModificationsEmpty
import WeilConjectures.AlgebraicGeometry.DenseOpenComponentModificationsNonempty

/-!
# Dense-open gluing of component modifications

Source: Stacks Project, Morphisms 0BAJ and Etale Cohomology 0A3Q.
(blueprint: theorem-cohomology-curves)
-/

@[expose] public section

universe u

open CategoryTheory

namespace AlgebraicGeometry

/-- The coproduct of modifications of distinct integral components is an isomorphism
on a dense open of the reduced target.
Source: Stacks Project, Morphisms 0BAJ and the proof of Etale Cohomology 0A3Q.
(blueprint: theorem-cohomology-curves)

Proof: Write Z i for the image of ι i. Remove every Z j with j different from i,
obtaining an open W i contained in Z i and containing its generic point. The image
in W i of the intersection of U i with the inverse image of W i is open in X.
Indeed, the restriction of ι i to W i is a surjective closed immersion into a
reduced scheme, hence an isomorphism: on affines its ideal has zero locus the whole
spectrum, and therefore lies in the nilradical, which is zero. Each resulting
open V i contains the generic point of Z i because U i is dense and the component
is irreducible. The V i are pairwise disjoint, and their union U is dense since
its closure contains every component's generic point. Over V i all other summands
have empty preimage, while the i-th summand map is an isomorphism by restriction
from U i and the preceding isomorphism for ι i. Isomorphism is local on the target,
so these inverses glue over U. For an empty family the component-cover hypothesis
forces X empty and the empty open is dense, with the empty-to-empty map an isomorphism.
-/
theorem exists_dense_open_isIso_component_modifications
    (X : Scheme.{u}) [IsReduced X]
    (n : ℕ) (C : Fin n → Scheme.{u}) (ι : ∀ i, C i ⟶ X)
    (hC : ∀ i, IsIntegral (C i) ∧ IsClosedImmersion (ι i) ∧
      Set.range (ι i) ∈ irreducibleComponents X)
    (hinj : Function.Injective (fun i => Set.range (ι i)))
    (hcover : ∀ Z ∈ irreducibleComponents X, ∃ i, Set.range (ι i) = Z)
    (Y : Fin n → Scheme.{u}) (ν : ∀ i, Y i ⟶ C i)
    (hν : ∀ i, ∃ U : (C i).Opens, Dense (U : Set (C i)) ∧ IsIso (ν i ∣_ U)) :
    ∃ U : X.Opens, Dense (U : Set X) ∧
      IsIso (CategoryTheory.Limits.Sigma.desc (fun i => ν i ≫ ι i) ∣_ U) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact exists_dense_open_isIso_component_modifications_of_zero X C ι hC hinj hcover Y ν hν
  · exact exists_dense_open_isIso_component_modifications_of_pos X n hn C ι hC hinj hcover Y ν hν

end AlgebraicGeometry

/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.AlgebraicGeometry.Curve.Assertions
import WeilConjectures.ConstructibleSheaf.Monoidal
import WeilConjectures.AlgebraicGeometry.Curve.PrimeBiproductUnconditional
import WeilConjectures.AlgebraicGeometry.Curve.PrimeBiproductPrimary
import WeilConjectures.AlgebraicGeometry.Curve.PrimeBiproductInvertible
import WeilConjectures.AlgebraicGeometry.EtaleCohomologyPullbackFunctorial
import WeilConjectures.AlgebraicGeometry.IsConstructibleEtaleModuleSheaf
import WeilConjectures.Mathlib.AlgebraicGeometry.Sites.EtalePoint
import WeilConjectures.SixFunctors.Etale.Derived.LowerShriek

/-!
# The curve assertions for finite sums with a common prime annihilator

Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-prime-biproduct-assertions).
-/

@[expose] public section

universe u

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Abelian.hasFiniteBiproducts

namespace AlgebraicGeometry.IsCurve

/-- The eight conditional assertions are componentwise for a finite biproduct of
constructible sheaves killed by one fixed prime. The ambient sheaf may be any object
isomorphic to the biproduct; there is no open immersion in this statement.
Source: Stacks Project, Theorem 03SC, proof, fourth paragraph; Lemma 0A5C
(blueprint: lem-pbc-t2-prime-biproduct-assertions).

Proof: Forgetting the module structure, inverse image, and cohomology are additive;
they preserve finite biproducts and isomorphisms. Naturality in the coefficient
sheaf identifies every field-extension and open-restriction comparison with the
finite sum of its component comparisons. Zero and finite cohomology groups are
equivalent to zero and finite component groups, respectively. A finite sum of
maps is bijective, respectively surjective, exactly when each component map is.
This proves C1, C2, C5, C7 and C8 in both directions, since the affine and proper
hypotheses depend only on the fixed morphism f. All summands, and their finite
sum, are constructible. For C3, let p be the positive characteristic. If p = r,
all stalks are p-primary and the vanishing condition is componentwise. If p ≠ r,
a stalk killed by r that is also p-primary is zero, by Bezout for r and p^m;
thus any summand satisfying the C3 hypothesis is zero. Likewise, if the whole
sum satisfies it then the whole sum is zero. These exceptional assertions are
automatic. For C4 and C6, if r is invertible in k (including characteristic zero),
all the sheaves have invertible-order torsion. If char k = r, any of these
sheaves with invertible-order torsion is zero: each stalk element is killed both
by r and by an integer coprime to r. Again the exceptional assertions are
automatic. Transport along the given isomorphism preserves constructibility,
torsion hypotheses and all comparison maps. When the index is empty the
biproduct is zero and all eight assertions hold, agreeing with the vacuous
right side. -/
theorem assertions_iff_of_prime_biproduct_iso (Λ : Type (u + 1)) [CommRing Λ]
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (r : ℕ) [Fact r.Prime] {ι : Type} [Finite ι]
    (G : ι → Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ))
    (hGc : ∀ a, Scheme.IsConstructibleSheaf (G a)) (hGr : ∀ a, r • 𝟙 (G a) = 0)
    {H : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)} (e : H ≅ ⨁ G) :
    Assertions Λ f H ↔ ∀ a, Assertions Λ f (G a) := by
  let : ∀ a, Scheme.IsConstructibleSheaf (G a) := hGc
  let : Scheme.IsConstructibleSheaf (⨁ G) := Scheme.IsConstructibleSheaf.biproduct G
  have hHc : Scheme.IsConstructibleSheaf H := Scheme.IsConstructibleSheaf.of_iso e.symm
  have hsum : r • 𝟙 (⨁ G) = 0 := by
    apply biproduct.hom_ext'
    intro a
    rw [Preadditive.comp_nsmul, Category.comp_id, ← Category.id_comp (biproduct.ι G a),
      ← Preadditive.nsmul_comp, hGr a, zero_comp, comp_zero]
  have hHr : r • 𝟙 H = 0 := by
    apply (cancel_mono e.hom).mp
    rw [Preadditive.nsmul_comp, Category.id_comp, ← Category.comp_id e.hom,
      ← Preadditive.comp_nsmul, hsum, comp_zero, zero_comp]
  have hu := prime_biproduct_unconditional_iff Λ f G hGc e hHc
  have hp := prime_biproduct_primary_iff Λ f r G hGr e hHr
  have hi := prime_biproduct_invertible_iff Λ f r G hGc hGr e hHr hHc
  constructor
  · intro h
    rcases (assertions_iff Λ f H).mp h with ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    have hg := hu.mp ⟨h1, h2, h5, h7, h8⟩
    have hgp := hp.mp h3
    have hgi := hi.mp ⟨h4, h6⟩
    intro a
    rcases hg a with ⟨g1, g2, g5, g7, g8⟩
    exact (assertions_iff Λ f (G a)).mpr
      ⟨g1, g2, hgp a, (hgi a).1, g5, (hgi a).2, g7, g8⟩
  · intro h
    have hg (a : ι) := (assertions_iff Λ f (G a)).mp (h a)
    have hu' := hu.mpr (fun a ↦
      ⟨(hg a).1, (hg a).2.1, (hg a).2.2.2.2.1,
        (hg a).2.2.2.2.2.2.1, (hg a).2.2.2.2.2.2.2⟩)
    have hp' := hp.mpr (fun a ↦ (hg a).2.2.1)
    have hi' := hi.mpr (fun a ↦ ⟨(hg a).2.2.2.1, (hg a).2.2.2.2.2.1⟩)
    rcases hu' with ⟨h1, h2, h5, h7, h8⟩
    exact (assertions_iff Λ f H).mpr ⟨h1, h2, hp', hi'.1, h5, hi'.2, h7, h8⟩

end AlgebraicGeometry.IsCurve

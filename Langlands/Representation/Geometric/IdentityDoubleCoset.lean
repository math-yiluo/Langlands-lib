import Mathlib.GroupTheory.DoubleCoset
import Langlands.Representation.Exponents.ArbitraryParabolicInduction

/-! # The identity double coset in an enumeration of `P(F) \ G(F) / P(F)`

The geometric lemma (Renard VI.5.1) for `Q = P` enumerates the double cosets
`P(F) \ G(F) / P(F)` by `c : Fin m ≃ DoubleCoset.Quotient` with representatives `z i`. Exactly
one index, the index of the double coset of `1`, has its representative in `P(F)`; every
other representative, and its inverse, lies outside `P(F)` and hence outside the Levi image
`M(F)`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Aubert.General.RepresentedParabolic

section DoubleCosets

variable {H : Type*} [Group H]

/-- An element lies in the double coset `K 1 K = K` exactly when it lies in `K`. -/
theorem doubleCoset_mk_eq_mk_one_iff (K : Subgroup H) (x : H) :
    DoubleCoset.mk K K x = DoubleCoset.mk K K 1 ↔ x ∈ K := by
  rw [DoubleCoset.eq]
  constructor
  · rintro ⟨a, ha, b, hb, h⟩
    have hx : x = a⁻¹ * b⁻¹ := by
      calc x = a⁻¹ * (a * x * b) * b⁻¹ := by group
        _ = a⁻¹ * b⁻¹ := by rw [← h]; group
    rw [hx]
    exact K.mul_mem (K.inv_mem ha) (K.inv_mem hb)
  · intro hx
    exact ⟨x⁻¹, K.inv_mem hx, 1, K.one_mem, by group⟩

/-- The index of the identity double coset `K 1 K` in an enumeration `c` of `K \ H / K`. -/
def identityDoubleCosetIndex {m : ℕ} (K : Subgroup H)
    (c : Fin m ≃ DoubleCoset.Quotient (K : Set H) K) : Fin m :=
  c.symm (DoubleCoset.mk K K 1)

variable {m : ℕ} (K : Subgroup H) (c : Fin m ≃ DoubleCoset.Quotient (K : Set H) K)
  (z : Fin m → H) (hz : ∀ i, DoubleCoset.mk K K (z i) = c i)
include hz

/-- A representative `z i` lies in `K` exactly at the identity index. -/
theorem mem_iff_eq_identityDoubleCosetIndex (i : Fin m) :
    z i ∈ K ↔ i = identityDoubleCosetIndex K c := by
  rw [← doubleCoset_mk_eq_mk_one_iff, hz, identityDoubleCosetIndex, Equiv.eq_symm_apply]

/-- The representative at the identity index lies in `K`. -/
theorem mem_identityDoubleCosetIndex : z (identityDoubleCosetIndex K c) ∈ K :=
  (mem_iff_eq_identityDoubleCosetIndex K c z hz _).2 rfl

/-- Off the identity index, a representative and its inverse lie outside `K`. -/
theorem not_mem_of_ne_identityDoubleCosetIndex {i : Fin m}
    (hi : i ≠ identityDoubleCosetIndex K c) : z i ∉ K ∧ (z i)⁻¹ ∉ K := by
  have h : z i ∉ K := fun h => hi ((mem_iff_eq_identityDoubleCosetIndex K c z hz i).1 h)
  exact ⟨h, fun h' => h (inv_mem_iff.1 h')⟩

end DoubleCosets

open GroupScheme

variable {k : Type u} [Field k] {G P M : GroupScheme (Spec (CommRingCat.of k))}

/-- For an enumeration `c` of `P(F) \ G(F) / P(F)` with representatives `z i`, every
representative off the identity index, and its inverse, lies outside the Levi image
`(l ≫ p)(M(F))`. -/
theorem not_mem_pointImage_levi_of_ne_identityDoubleCosetIndex (p : P ⟶ G) (l : M ⟶ P)
    {m : ℕ} (c : Fin m ≃ DoubleCoset.Quotient (pointImage p : Set (rationalPoints G))
      (pointImage p : Set (rationalPoints G)))
    (z : Fin m → rationalPoints G)
    (hz : ∀ i, DoubleCoset.mk (pointImage p) (pointImage p) (z i) = c i)
    {i : Fin m} (hi : i ≠ identityDoubleCosetIndex (pointImage p) c) :
    z i ∉ pointImage (l ≫ p) ∧ (z i)⁻¹ ∉ pointImage (l ≫ p) := by
  obtain ⟨h, h'⟩ := not_mem_of_ne_identityDoubleCosetIndex (pointImage p) c z hz hi
  exact ⟨fun hl => h (pointImage_comp_le p l hl), fun hl => h' (pointImage_comp_le p l hl)⟩

end Langlands.Aubert.General.RepresentedParabolic

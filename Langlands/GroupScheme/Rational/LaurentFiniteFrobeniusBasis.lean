import Langlands.GroupScheme.Rational.LaurentFiniteCoordinates

/-! # Finite Frobenius generators in pointed Laurent coordinates -/

noncomputable section

universe u v

namespace Langlands.GroupScheme.LaurentAugmentation

open MvPolynomial

variable (k : Type u) [CommRing k] (p : ℕ) [Fact p.Prime] (I : Type v)

/-- An iterated power of a function vanishing at the identity. -/
def frobPower (f : space k (I → ℤ)) (r : ℕ) : space k (I → ℤ) :=
  ⟨f.val ^ p ^ r, pow_mem_space p f.property r⟩

/-- The linear span of all iterated Frobenius powers of a family. -/
def frobSpan (S : Set (space k (I → ℤ))) : Submodule k (space k (I → ℤ)) :=
  Submodule.span k {f | ∃ g ∈ S, ∃ r : ℕ, f = frobPower k p I g r}

variable {k p I}

@[simp] theorem frobPower_zero (f : space k (I → ℤ)) :
    frobPower k p I f 0 = f := by
  apply Subtype.ext
  simp [frobPower]

section Characteristic

variable [CharP k p]

@[simp] theorem frobPower_succ (f : space k (I → ℤ)) (r : ℕ) :
    frobPower k p I f (r + 1) =
      frobeniusMap (k := k) (p := p) (I := I) (frobPower k p I f r) := by
  apply Subtype.ext
  simp only [frobPower, frobeniusMap_val, pow_succ, pow_mul]

theorem frobPower_mem {N : Submodule k (space k (I → ℤ))}
    (hN : ∀ f ∈ N, frobeniusMap (k := k) (p := p) (I := I) f ∈ N)
    {f : space k (I → ℤ)} (hf : f ∈ N) (r : ℕ) :
    frobPower k p I f r ∈ N := by
  induction r with
  | zero => simpa using hf
  | succ r ih => rw [frobPower_succ]; exact hN _ ih

theorem frobSpan_le {N : Submodule k (space k (I → ℤ))}
    (hN : ∀ f ∈ N, frobeniusMap (k := k) (p := p) (I := I) f ∈ N)
    {S : Set (space k (I → ℤ))} (hS : S ⊆ N) :
    frobSpan k p I S ≤ N := by
  rw [frobSpan, Submodule.span_le]
  rintro _ ⟨g, hg, r, rfl⟩
  exact frobPower_mem hN (hS hg) r

theorem finiteEncoding_frobPower
    (s : Finset {m : I → ℤ // IsPrimitive p m}) (f : space k (I → ℤ)) (r : ℕ) :
    finiteEncoding k p I s (frobPower k p I f r) =
      finiteEncoding k p I s f ^ p ^ r := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [frobPower_succ, finiteEncoding_frobenius, ih, pow_succ, pow_mul]

theorem map_frobSpan (s : Finset {m : I → ℤ // IsPrimitive p m})
    (S : Set (space k (I → ℤ))) :
    (frobSpan k p I S).map (finiteEncoding k p I s) =
      TorusLinearization.frobSpan k p 0 (finiteEncoding k p I s '' S) := by
  rw [frobSpan, Submodule.map_span, TorusLinearization.frobSpan]
  congr 1
  ext q
  constructor
  · rintro ⟨f, ⟨g, hg, r, rfl⟩, rfl⟩
    exact ⟨finiteEncoding k p I s g, ⟨g, hg, rfl⟩, r, Nat.zero_le _,
      finiteEncoding_frobPower s g r⟩
  · rintro ⟨q, ⟨g, hg, rfl⟩, r, _, rfl⟩
    exact ⟨frobPower k p I g r, ⟨g, hg, r, rfl⟩, finiteEncoding_frobPower s g r⟩

end Characteristic

section Field

variable {K : Type u} [Field K] [CharP K p]

open Classical in
/-- A Frobenius-stable subspace supported on finitely many primitive orbits has
a finite generating family whose finite encodings are Frobenius-independent. -/
theorem exists_finiteFrobBasis
    (s : Finset {m : I → ℤ // IsPrimitive p m})
    (N : Submodule K (space K (I → ℤ))) (hle : N ≤ finiteOrbitSpace K p I s)
    (hN : ∀ f ∈ N, frobeniusMap (k := K) (p := p) (I := I) f ∈ N) :
    ∃ G : Finset (space K (I → ℤ)),
      (G : Set (space K (I → ℤ))) ⊆ N ∧
      N = frobSpan K p I (G : Set (space K (I → ℤ))) ∧
      TorusLinearization.FrobIndep (G.image (finiteEncoding K p I s)) := by
  classical
  let e := finiteEncoding K p I s
  let P := N.map e
  have hadd : ∀ q ∈ P, TorusLinearization.IsAddPoly q := by
    rintro q ⟨f, _, rfl⟩
    exact finiteEncoding_isAddPoly s f
  have hfrob : ∀ q ∈ P, q ^ p ∈ P := by
    rintro q ⟨f, hf, rfl⟩
    refine ⟨frobeniusMap (k := K) (p := p) (I := I) f, hN f hf, ?_⟩
    exact finiteEncoding_frobenius s f
  obtain ⟨G', hG', hPG', hind⟩ :=
    TorusLinearization.exists_frobBasis Finset.univ P hadd hfrob
      (fun q _ j hj => absurd (Finset.mem_univ j) hj)
  obtain ⟨G, hGN, hGG'⟩ : ∃ G : Finset (space K (I → ℤ)),
      (G : Set (space K (I → ℤ))) ⊆ N ∧ G.image e = G' := by
    apply Finset.subset_set_image_iff.mp
    exact hG'
  refine ⟨G, hGN, le_antisymm ?_ (frobSpan_le hN hGN), ?_⟩
  · intro f hf
    have hq : e f ∈ TorusLinearization.frobSpan K p 0
        (e '' (G : Set (space K (I → ℤ)))) := by
      rw [← Finset.coe_image, hGG']
      exact hPG' ⟨f, hf, rfl⟩
    rw [← map_frobSpan] at hq
    obtain ⟨g, hg, heq⟩ := hq
    have hgN := frobSpan_le hN hGN hg
    have hgf : g = f := finiteEncoding_injOn s (hle hgN) (hle hf) heq
    simpa [hgf] using hg
  · change TorusLinearization.FrobIndep (G.image e)
    rw [hGG']
    exact hind

end Field

end Langlands.GroupScheme.LaurentAugmentation

import Langlands.GroupScheme.SimplyConnected.LocalRankOneTitsIndexNormalization
import Langlands.GroupScheme.Reductive.TitsIndexRankOneOrbit
import Langlands.LinearAlgebra.RootDatumPathUniqueness

/-! # Full star actions and distinguished orbits for type A

The actual full star action on a numbered type-A diagram is trivial or has
image exactly the identity and chain reversal. At split rank one this also
determines the actual distinguished set as a singleton or a reversal orbit.
No local arithmetic restrictions on the rank or the marked positions are
asserted here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

namespace TypeACartan

/-- A function preserving every type-A Cartan entry is injective. -/
theorem injective_of_preserves {n : ℕ} (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.A n (f i) (f j) = CartanMatrix.A n i j) :
    Function.Injective f := by
  intro i j hij
  have h := hf i j
  rw [hij] at h
  simp only [CartanMatrix.A, Matrix.of_apply, ite_true] at h
  split_ifs at h with heq <;> first | exact heq | norm_num at h

/-- The only symmetries of the full type-A Cartan matrix are identity and
chain reversal, including the empty and one-vertex cases. -/
theorem eq_id_or_rev_of_preserves {n : ℕ} (f : Fin n → Fin n)
    (hf : ∀ i j, CartanMatrix.A n (f i) (f j) = CartanMatrix.A n i j) :
    (∀ i, f i = i) ∨ (∀ i, f i = Fin.revPerm i) := by
  have hinj := injective_of_preserves f hf
  have hstep : ∀ (j : ℕ) (hj : j + 1 < n),
      (f ⟨j, by omega⟩).val + 1 = (f ⟨j + 1, hj⟩).val ∨
        (f ⟨j + 1, hj⟩).val + 1 = (f ⟨j, by omega⟩).val := by
    intro j hj
    have h := hf ⟨j, by omega⟩ ⟨j + 1, hj⟩
    have hne : (⟨j, by omega⟩ : Fin n) ≠ ⟨j + 1, hj⟩ := by
      intro h
      have : j = j + 1 := congrArg Fin.val h
      omega
    have hentry : CartanMatrix.A n ⟨j, by omega⟩ ⟨j + 1, hj⟩ = -1 := by
      simp [CartanMatrix.A, Matrix.of_apply, hne]
    rw [hentry] at h
    by_contra hnadj
    have hne' := hinj.ne hne
    simp [CartanMatrix.A, Matrix.of_apply, hne', hnadj] at h
  rcases Langlands.LinearAlgebra.RootDatumPathWeights.walk_eq_id_or_rev f hinj hstep
      with hid | hrev
  · exact Or.inl (fun i => Fin.ext (hid i))
  · right
    intro i
    apply Fin.ext
    simp only [Fin.revPerm_apply, Fin.val_rev]
    have := hrev i
    omega

end TypeACartan

namespace TitsIndexData

variable {K : Type u} [Field K]
  {G : GroupScheme (Spec (CommRingCat.of K))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  (d : TitsIndexData G)

/-- The full absolute Galois action as a permutation-valued homomorphism,
transported along one actual numbering. -/
def numberedStarHom {n : ℕ} (e : d.Vertex ≃ Fin n) :
    (SeparableClosure K ≃ₐ[K] SeparableClosure K) →* Equiv.Perm (Fin n) where
  toFun := d.numberedStar e
  map_one' := by
    apply Equiv.ext
    intro i
    simp
  map_mul' σ τ := by
    apply Equiv.ext
    intro i
    simp only [numberedStar_apply, Equiv.Perm.mul_apply, d.star_mul,
      Equiv.symm_apply_apply]

@[simp] theorem numberedStarHom_apply {n : ℕ} (e : d.Vertex ≃ Fin n)
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) (i : Fin n) :
    d.numberedStarHom e σ i = e (d.star σ (e.symm i)) := rfl

/-- For a type-A Cartan numbering, every full Galois element acts globally
by the identity or globally by chain reversal. -/
theorem star_cases_of_A {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (σ : SeparableClosure K ≃ₐ[K] SeparableClosure K) :
    (∀ a, e (d.star σ a) = e a) ∨
      (∀ a, e (d.star σ a) = Fin.revPerm (e a)) := by
  let f : Equiv.Perm (Fin n) := d.numberedStarHom e σ
  have hf : ∀ i j, CartanMatrix.A n (f i) (f j) = CartanMatrix.A n i j := by
    intro i j
    calc
      CartanMatrix.A n (f i) (f j) =
          d.cartan (d.star σ (e.symm i)) (d.star σ (e.symm j)) := (hA _ _).symm
      _ = d.cartan (e.symm i) (e.symm j) := cartan_star σ _ _
      _ = CartanMatrix.A n i j := by simpa using hA (e.symm i) (e.symm j)
  rcases TypeACartan.eq_id_or_rev_of_preserves f hf with hid | hrev
  · left
    intro a
    simpa [f] using hid (e a)
  · right
    intro a
    simpa [f] using hrev (e a)

/-- A nontrivial full star action on any type-A diagram has exactly the
identity and chain reversal as its image under the same numbering. -/
theorem starImagePair_of_A {n : ℕ} (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b))
    (hnot : ¬ d.StarIsTrivial) : d.StarImagePair e Fin.revPerm := by
  have hne : (Fin.revPerm : Equiv.Perm (Fin n)) ≠ 1 := by
    intro hrev
    apply hnot
    intro σ a
    apply e.injective
    rcases d.star_cases_of_A e hA σ with hid | hrev'
    · exact hid a
    · simpa only [hrev, Equiv.Perm.one_apply] using hrev' a
  exact starImagePair_of_cartan_symmetry e Fin.revPerm hA hne
    TypeACartan.eq_id_or_rev_of_preserves hnot

/-- A full two-permutation image and split rank one identify every actual
marked vertex with one of the two images of the chosen actual vertex. -/
theorem mem_distinguishedVertices_iff_of_rank_one_starImagePair {n : ℕ}
    (hrank : splitRank G = 1) (e : d.Vertex ≃ Fin n) (τ : Equiv.Perm (Fin n))
    (hpair : d.StarImagePair e τ) (a : d.Vertex) :
    a ∈ d.distinguishedVertices ↔
      e a = e (d.rankOneDistinguishedVertex hrank).val ∨
        e a = τ (e (d.rankOneDistinguishedVertex hrank).val) := by
  rw [d.mem_distinguishedVertices_iff_rankOne_orbit hrank]
  constructor
  · rintro ⟨σ, hσ⟩
    rcases hpair.2.1 σ with hid | hτ
    · exact Or.inl ((congrArg e hσ).symm.trans (hid _))
    · exact Or.inr ((congrArg e hσ).symm.trans (hτ _))
  · rintro (hid | hτ)
    · exact ⟨1, by simpa using e.injective hid.symm⟩
    · obtain ⟨σ, hσ⟩ := hpair.2.2
      exact ⟨σ, e.injective ((hσ _).trans hτ.symm)⟩

/-- At split rank one a type-A diagram has exactly a single marked vertex
with trivial full star action, or a reversal orbit of marked vertices with
full image exactly identity and reversal. The two displayed vertices in the
outer case may coincide. -/
theorem rank_one_type_A_orbit_alternatives {n : ℕ} (hrank : splitRank G = 1)
    (e : d.Vertex ≃ Fin n)
    (hA : ∀ a b, d.cartan a b = CartanMatrix.A n (e a) (e b)) :
    (∃ j : Fin n, (∀ a, a ∈ d.distinguishedVertices ↔ e a = j) ∧ d.StarIsTrivial) ∨
      ∃ j : Fin n,
        (∀ a, a ∈ d.distinguishedVertices ↔ e a = j ∨ e a = Fin.revPerm j) ∧
          d.StarImagePair e Fin.revPerm := by
  classical
  let j := e (d.rankOneDistinguishedVertex hrank).val
  by_cases hstar : d.StarIsTrivial
  · left
    refine ⟨j, ?_, hstar⟩
    intro a
    rw [d.distinguishedVertices_eq_singleton_of_star_trivial hrank hstar]
    exact ⟨fun ha => congrArg e ha, fun ha => e.injective ha⟩
  · right
    have hpair := d.starImagePair_of_A e hA hstar
    exact ⟨j, d.mem_distinguishedVertices_iff_of_rank_one_starImagePair
      hrank e Fin.revPerm hpair, hpair⟩

end TitsIndexData

end Langlands.GroupScheme

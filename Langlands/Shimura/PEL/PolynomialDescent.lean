import Mathlib.RingTheory.MvPolynomial.Homogeneous

/-! # Descent of a multivariate polynomial along a coefficient embedding -/

noncomputable section

universe u v w t

namespace Langlands.Shimura.PolynomialDescent

open MvPolynomial

variable {R : Type u} {S : Type v} {T : Type w}
    [CommRing R] [CommRing S] [CommRing T]
    {ι : Type t}

private theorem exists_preimage (f : R →+* S) (p : MvPolynomial ι S)
    (hp : ∀ d, p.coeff d ∈ Set.range f) :
    ∃ q : MvPolynomial ι R, MvPolynomial.map f q = p := by
  apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
  intro c hc
  obtain ⟨d, _, rfl⟩ := MvPolynomial.mem_coeffs_iff.mp hc
  exact hp d

/-- Lift a polynomial whose coefficients lie in the range of the given map. -/
def descend (f : R →+* S) (p : MvPolynomial ι S)
    (hp : ∀ d, p.coeff d ∈ Set.range f) : MvPolynomial ι R :=
  (exists_preimage f p hp).choose

@[simp] theorem map_descend (f : R →+* S) (p : MvPolynomial ι S)
    (hp : ∀ d, p.coeff d ∈ Set.range f) :
    MvPolynomial.map f (descend f p hp) = p :=
  (exists_preimage f p hp).choose_spec

@[simp] theorem map_coeff_descend (f : R →+* S) (p : MvPolynomial ι S)
    (hp : ∀ d, p.coeff d ∈ Set.range f) (d : ι →₀ ℕ) :
    f ((descend f p hp).coeff d) = p.coeff d := by
  simpa only [MvPolynomial.coeff_map] using
    congrArg (fun q => q.coeff d) (map_descend f p hp)

/-- An injective coefficient map makes the lift unique. -/
theorem unique (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial ι S) (hp : ∀ d, p.coeff d ∈ Set.range f)
    (q : MvPolynomial ι R) (hq : MvPolynomial.map f q = p) :
    q = descend f p hp := by
  apply MvPolynomial.map_injective f hf
  exact hq.trans (map_descend f p hp).symm

theorem descend_isHomogeneous (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial ι S) (hp : ∀ d, p.coeff d ∈ Set.range f)
    {n : ℕ} (h : p.IsHomogeneous n) :
    (descend f p hp).IsHomogeneous n := by
  apply MvPolynomial.IsHomogeneous.of_map hf
  simpa only [map_descend] using h

theorem support_descend (f : R →+* S) (hf : Function.Injective f)
    (p : MvPolynomial ι S) (hp : ∀ d, p.coeff d ∈ Set.range f) :
    (descend f p hp).support = p.support := by
  simpa only [map_descend] using
    (MvPolynomial.support_map_of_injective (descend f p hp) hf).symm

/-- Evaluation commutes with descent through any further coefficient map. -/
theorem eval₂_descend (f : R →+* S) (p : MvPolynomial ι S)
    (hp : ∀ d, p.coeff d ∈ Set.range f) (g : S →+* T) (x : ι → T) :
    MvPolynomial.eval₂ (g.comp f) x (descend f p hp) =
      MvPolynomial.eval₂ g x p := by
  rw [← MvPolynomial.eval₂_map, map_descend]

end Langlands.Shimura.PolynomialDescent

import Langlands.Representation.Smooth.Factorization.RestrictedTensorStatement

/-!
# Independence of the restricted tensor representation from the reference vectors

Proof of `RestrictedTensorReferenceIndependenceStatement` (Flath 1979, §2, Example 2): if at
almost every index the vectors of `ρ i` fixed by `H i` form a line, the restricted tensor
representations built from two families of nonzero fixed reference vectors are equivalent.

At almost every index both reference vectors lie on the fixed line, so the second is a nonzero
multiple `c i` of the first. Multiplication by `c i` (and by `1` at the finitely many other
indices) is an equivariant linear automorphism of each factor carrying the first family of
references to the second almost everywhere; the Library's `RestrictedTensor.congr` and
`RestrictedTensor.map_intertwines` turn it into an equivalence of the restricted tensor
representations. Admissibility, the topology and local irreducibility are not used.
-/

namespace Langlands

open RestrictedTensor

universe uI uG uV

/-- At an index outside both exceptional sets where the fixed space is a line, the second
reference vector is a nonzero multiple of the first. -/
theorem RestrictedTensor.exists_reference_smul {ι : Type uI} {G : ι → Type uG}
    [∀ i, Group (G i)] {H : ∀ i, Subgroup (G i)} {V : ι → Type uV}
    [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)] {ρ : ∀ i, Representation ℂ (G i) (V i)}
    {E E' : Finset ι} (r : ReferenceVectors V E) (r' : ReferenceVectors V E')
    (hr : ∀ i (hi : i ∉ E), ∀ g ∈ H i, ρ i g (r.vector i hi) = r.vector i hi)
    (hr' : ∀ i (hi : i ∉ E'), ∀ g ∈ H i, ρ i g (r'.vector i hi) = r'.vector i hi)
    (i : ι) :
    ∃ c : ℂ, c ≠ 0 ∧ (Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1 →
      ∀ (hi : i ∉ E) (hi' : i ∉ E'), r'.vector i hi' = c • r.vector i hi) := by
  by_cases h : i ∉ E ∧ i ∉ E' ∧ Module.finrank ℂ (fixedVectors (ρ i) (H i)) = 1
  · obtain ⟨hi, hi', h1⟩ := h
    have hmem : r.vector i hi ∈ fixedVectors (ρ i) (H i) := fun g => hr i hi g g.2
    have hmem' : r'.vector i hi' ∈ fixedVectors (ρ i) (H i) := fun g => hr' i hi' g g.2
    have hne : (⟨r.vector i hi, hmem⟩ : fixedVectors (ρ i) (H i)) ≠ 0 := fun h0 =>
      r.nonzero i hi (congrArg Subtype.val h0)
    obtain ⟨c, hc⟩ := (finrank_eq_one_iff_of_nonzero' _ hne).mp h1 ⟨r'.vector i hi', hmem'⟩
    have hc' : c • r.vector i hi = r'.vector i hi' := congrArg Subtype.val hc
    refine ⟨c, fun h0 => r'.nonzero i hi' ?_, fun _ _ _ => hc'.symm⟩
    rw [← hc', h0, zero_smul]
  · refine ⟨1, one_ne_zero, fun h1 hi hi' => absurd ⟨hi, hi', h1⟩ h⟩

/-- **Reference independence** (Flath 1979, §2, Example 2). -/
theorem restrictedTensorReferenceIndependence :
    RestrictedTensorReferenceIndependenceStatement.{uI, uG, uV} := by
  intro ι G _ _ _ _ _ _ H V _ _ ρ E E' r r' hr hr' _ _ hfin
  choose c hc0 hc using RestrictedTensor.exists_reference_smul r r' hr hr'
  let f : ∀ i, V i ≃ₗ[ℂ] V i := fun i => LinearEquiv.smulOfNeZero ℂ (V i) (c i) (hc0 i)
  have hf : ∀ᶠ i in Filter.cofinite, f i (r.family i) = r'.family i := by
    filter_upwards [hfin, E.eventually_cofinite_notMem, E'.eventually_cofinite_notMem] with
      i h1 hi hi'
    rw [ReferenceVectors.family_of_not_mem r hi, ReferenceVectors.family_of_not_mem r' hi']
    exact (hc i h1 hi hi').symm
  have hint : ∀ i (g : G i), (f i).toLinearMap.comp (ρ i g) = (ρ i g).comp (f i).toLinearMap :=
    fun i g => LinearMap.ext fun x => (map_smul (ρ i g) (c i) x).symm
  refine ⟨Representation.Equiv.mk (RestrictedTensor.congr E E' r.family r'.family f hf)
    fun g => ?_⟩
  exact map_intertwines H ρ ρ E E' r.family r'.family _ _ (fun i => (f i).toLinearMap) hf hint g

end Langlands

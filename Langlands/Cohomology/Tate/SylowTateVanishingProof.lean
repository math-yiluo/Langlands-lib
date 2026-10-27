import Langlands.Cohomology.Tate.CohomologicalTrivialityStatement
import Langlands.Cohomology.Tate.TransferLawsProof

/-!
# Sylow detection of Tate vanishing

Corestriction after restriction to a Sylow `p`-subgroup is multiplication by its
index, which is prime to `p`.
-/

open CategoryTheory CategoryTheory.Limits

universe u

namespace Langlands.Tate

/-- Vanishing of actual Tate cohomology in one degree is detected on Sylow subgroups. -/
theorem sylowTateVanishing : SylowTateVanishing.{u} := by
  intro R G _ _ _ C n h
  classical
  have hdvd : ∀ x : tateCohomology C n, ∀ (p : ℕ), p.Prime → ∀ P : Sylow p G,
      addOrderOf x ∣ (P : Subgroup G).index := by
    intro x p hp P
    let _ : Fintype P.1 := Fintype.ofFinite _
    let _ : Fintype (G ⧸ P.1) := Fintype.ofFinite _
    apply addOrderOf_dvd_of_nsmul_eq_zero
    have hres : restriction P.1 C n x = 0 :=
      (ModuleCat.isZero_iff_subsingleton.mp (h p hp P)).elim _ 0
    rw [← corestriction_restriction P.1 C n x, hres, map_zero]
  have hall : ∀ x : tateCohomology C n, x = 0 := by
    intro x
    rw [← AddMonoid.addOrderOf_eq_one_iff]
    by_contra hne
    have hq := Nat.minFac_prime hne
    have : Fact (addOrderOf x).minFac.Prime := ⟨hq⟩
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow (addOrderOf x).minFac G))
    exact P.not_dvd_index ((Nat.minFac_dvd _).trans (hdvd x _ hq P))
  have : Subsingleton (tateCohomology C n) := ⟨fun a b => (hall a).trans (hall b).symm⟩
  exact ModuleCat.isZero_of_subsingleton _

end Langlands.Tate

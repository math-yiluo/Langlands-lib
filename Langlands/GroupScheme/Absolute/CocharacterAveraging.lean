import Langlands.GroupScheme.Torus.LatticeGalois
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-! # Galois orbit sums of cocharacters -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped BigOperators CategoryTheory.MonObj

namespace Langlands.GroupScheme

section Pairing

variable {B : Scheme.{u}} {K : Type u} [CommRing K] [IsDomain K]
  (b : Spec (CommRingCat.of K) ⟶ B)
  (a : Spec (CommRingCat.of K) ⟶ Spec (CommRingCat.of K))
  (ha : a ≫ b = b) (T : CommGroupScheme B)

/-- Simultaneous transport of a character and a cocharacter preserves their pairing. -/
theorem latticePairing_transport
    (χ : characterLattice ((CommGroupScheme.baseChange b).obj T))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange b).obj T)) :
    latticePairing ((CommGroupScheme.baseChange b).obj T)
        (characterLattice.transport b a ha T χ) (cocharacterLattice.transport b a ha T ν) =
      latticePairing ((CommGroupScheme.baseChange b).obj T) χ ν := by
  rw [latticePairing_apply, latticePairing_apply]
  apply congrArg (gmEndEquiv K)
  apply CommGroupScheme.hom_ext_points
  intro U x
  apply (Gm.pointsEquiv _ U).injective
  rw [comp_groupHom_comp, characterLattice.transport_points,
    cocharacterLattice.descentPoint_transport, ← comp_groupHom_comp]
  rw [eq_gmEndEquiv_zsmul K (ν ≫ χ), Gm.comp_zsmul_id, Gm.comp_zsmul_id,
    map_zpow, map_zpow, MulEquiv.apply_symm_apply]

end Pairing

section GaloisPairing

variable (k K : Type u) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K]
  (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The published Galois actions on both lattices preserve their pairing. -/
theorem latticePairing_galoisRepresentation (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (characterLattice.galoisRepresentation k K T σ χ)
        (cocharacterLattice.galoisRepresentation k K T σ ν) =
      latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν :=
  latticePairing_transport _ _ _ T χ ν

/-- Transport can be moved from the cocharacter to the inverse transport of the character. -/
theorem latticePairing_galoisRepresentation_right (σ : K ≃ₐ[k] K)
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ
        (cocharacterLattice.galoisRepresentation k K T σ ν) =
      latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        (characterLattice.galoisRepresentation k K T σ⁻¹ χ) ν := by
  have h := latticePairing_galoisRepresentation k K T σ
    (characterLattice.galoisRepresentation k K T σ⁻¹ χ) ν
  simpa only [Representation.self_inv_apply] using h

end GaloisPairing

namespace CocharacterAveraging

section OrbitSum

variable {Γ M : Type*} [Group Γ] [Fintype Γ] [AddCommGroup M] [Module ℤ M]

/-- The integral orbit sum, with no division by the group order. -/
def orbitSum (ρ : Representation ℤ Γ M) (ν : M) : M := ∑ σ : Γ, ρ σ ν

/-- An integral orbit sum is fixed by the entire finite group. -/
theorem orbitSum_fixed (ρ : Representation ℤ Γ M) (ν : M) (τ : Γ) :
    ρ τ (orbitSum ρ ν) = orbitSum ρ ν := by
  classical
  simp only [orbitSum, map_sum]
  calc
    ∑ σ : Γ, ρ τ (ρ σ ν) = ∑ σ : Γ, ρ (τ * σ) ν := by
      apply Finset.sum_congr rfl
      intro σ _
      exact (congrArg (fun f : Module.End ℤ M => f ν) (ρ.map_mul τ σ)).symm
    _ = ∑ σ : Γ, ρ σ ν :=
      Fintype.sum_equiv (Equiv.mulLeft τ) _ _ (fun _ => rfl)

/-- A stable nonnegative half-space has the same membership before and after orbit summing. -/
theorem nonneg_orbitSum_iff (ρ : Representation ℤ Γ M) (ν : M) (f : M →+ ℤ)
    (hstable : ∀ σ : Γ, 0 ≤ f (ρ σ ν) ↔ 0 ≤ f ν) :
    0 ≤ f (orbitSum ρ ν) ↔ 0 ≤ f ν := by
  rw [orbitSum, map_sum]
  constructor
  · intro h
    by_contra hn
    have hneg : ∀ σ : Γ, f (ρ σ ν) < 0 := fun σ =>
      lt_of_not_ge (fun hσ => hn ((hstable σ).mp hσ))
    have hs : ∑ σ : Γ, f (ρ σ ν) < 0 := by
      simpa only [Finset.sum_const_zero] using
        (Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty (fun σ _ => hneg σ))
    exact (not_lt_of_ge h) hs
  · intro h
    exact Finset.sum_nonneg fun σ _ => (hstable σ).mpr h

end OrbitSum

section Cocharacters

variable (k K : Type u) [CommRing k] [CommRing K] [IsDomain K] [Algebra k K]
  [Fintype (K ≃ₐ[k] K)] (T : CommGroupScheme (Spec (CommRingCat.of k)))

/-- The sum of all Galois translates of a cocharacter of `T_K`. -/
def galoisOrbitSum
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)) :
    cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) :=
  orbitSum (cocharacterLattice.galoisRepresentation k K T) ν

omit [IsDomain K] in
theorem galoisOrbitSum_fixed
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (σ : K ≃ₐ[k] K) :
    cocharacterLattice.galoisRepresentation k K T σ (galoisOrbitSum k K T ν) =
      galoisOrbitSum k K T ν :=
  orbitSum_fixed _ _ _

/-- On a Galois-stable family of characters, a Galois-stable nonnegative subset is
unchanged by taking the integral orbit sum of the cocharacter. -/
theorem galoisOrbitSum_nonneg_iff
    (ν : cocharacterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (Φ : Set (characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)))
    (hΦ : ∀ (σ : K ≃ₐ[k] K) χ,
      characterLattice.galoisRepresentation k K T σ χ ∈ Φ ↔ χ ∈ Φ)
    (hcone : ∀ (σ : K ≃ₐ[k] K) χ,
      (characterLattice.galoisRepresentation k K T σ χ ∈ Φ ∧
        0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
          (characterLattice.galoisRepresentation k K T σ χ) ν) ↔
      (χ ∈ Φ ∧ 0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        χ ν))
    (χ : characterLattice ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T))
    (hχ : χ ∈ Φ) :
    0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
        χ (galoisOrbitSum k K T ν) ↔
      0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν := by
  refine nonneg_orbitSum_iff (cocharacterLattice.galoisRepresentation k K T) ν
    (latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ).toAddMonoidHom ?_
  intro σ
  change 0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T)
      χ (cocharacterLattice.galoisRepresentation k K T σ ν) ↔
    0 ≤ latticePairing ((CommGroupScheme.baseChange (algebraBaseMap k K)).obj T) χ ν
  rw [latticePairing_galoisRepresentation_right]
  constructor
  · intro h
    exact ((hcone σ⁻¹ χ).mp ⟨(hΦ σ⁻¹ χ).mpr hχ, h⟩).2
  · intro h
    exact ((hcone σ⁻¹ χ).mpr ⟨hχ, h⟩).2

end Cocharacters

end CocharacterAveraging

end Langlands.GroupScheme

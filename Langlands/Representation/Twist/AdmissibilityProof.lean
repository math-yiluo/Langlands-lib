import Langlands.Representation.Twist.AdmissibilityStatement
import Langlands.Representation.Twist.SmoothProof
import Langlands.Representation.Smooth.Admissibility.CofinalProof

namespace Langlands

universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [AddCommGroup V] [Module R V]

/-- A character twist does not change fixed vectors for a subgroup on which
the character is trivial. -/
theorem fixedVectors_twist_eq_of_le_ker (chi : G →* Rˣ)
    (rho : Representation R G V) (H : Subgroup G) (hH : H ≤ chi.ker) :
    fixedVectors (twist chi rho) H = fixedVectors rho H := by
  ext v
  change (∀ g : H, (chi (g : G) : R) • rho (g : G) v = v) ↔
    ∀ g : H, rho (g : G) v = v
  constructor
  · intro hv g
    have hg : chi (g : G) = 1 := hH g.property
    simpa [hg] using hv g
  · intro hv g
    have hg : chi (g : G) = 1 := hH g.property
    simpa [hg] using hv g

/-- An open-kernel character twist preserves admissibility over Noetherian
coefficients, using the cofinal family of open subgroups in the kernel. -/
theorem isAdmissible_twist_iff [TopologicalSpace G] [IsNoetherianRing R]
    (chi : G →* Rˣ) (rho : Representation R G V)
    (hchi : IsOpen (chi.ker : Set G)) :
    IsAdmissible (twist chi rho) ↔ IsAdmissible rho := by
  let L : OpenSubgroup G := ⟨chi.ker, hchi⟩
  let S : Set (OpenSubgroup G) := {K | K.toSubgroup ≤ chi.ker}
  have hS : ∀ K : OpenSubgroup G, ∃ J ∈ S, J ≤ K := by
    intro K
    refine ⟨K ⊓ L, ?_, inf_le_left⟩
    intro g hg
    exact hg.2
  rw [isAdmissible_iff_of_cofinal S hS, isAdmissible_iff_of_cofinal S hS,
    isSmooth_twist_iff chi rho hchi]
  have hfixed : ∀ K ∈ S,
      fixedVectors (twist chi rho) K.toSubgroup = fixedVectors rho K.toSubgroup :=
    fun K hK => fixedVectors_twist_eq_of_le_ker chi rho K.toSubgroup hK
  constructor
  · rintro ⟨hs, hf⟩
    refine ⟨hs, fun K hK => ?_⟩
    exact (Module.Finite.equiv_iff (LinearEquiv.ofEq _ _ (hfixed K hK))).mp (hf K hK)
  · rintro ⟨hs, hf⟩
    refine ⟨hs, fun K hK => ?_⟩
    exact (Module.Finite.equiv_iff (LinearEquiv.ofEq _ _ (hfixed K hK))).mpr (hf K hK)

theorem twistAdmissibilityCompatibility :
    TwistAdmissibilityCompatibility (R := R) (G := G) (V := V) := by
  refine ⟨fixedVectors_twist_eq_of_le_ker, ?_⟩
  intro _ _ chi rho hchi
  exact isAdmissible_twist_iff chi rho hchi

end Langlands

import Langlands.Representation.Compact.ProjectionStatement

namespace Langlands.Compact

open scoped BigOperators

universe uG uV uW

section Algebra

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

theorem orbitMean_invariant (ρ : Representation ℂ G V) (v : V)
    [Finite (orbit ρ v)] (g : G) :
    ρ g (orbitMean ρ v) = orbitMean ρ v := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  rw [orbitMean_eq_finiteMean]
  unfold finiteMean
  rw [map_smul, map_sum]
  congr 1
  exact Equiv.sum_comp (MulAction.toPerm (β := orbit ρ v) g) (fun x => x.val)

theorem orbitMean_id (ρ : Representation ℂ G V) (v : V)
    [Finite (orbit ρ v)] (hv : ∀ g, ρ g v = v) :
    orbitMean ρ v = v := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  have hval (x : orbit ρ v) : x.val = v := by
    obtain ⟨g, hg⟩ := x.property
    exact hg.symm.trans (hv g)
  have hcard : (Fintype.card (orbit ρ v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [orbitMean_eq_finiteMean]
  simp only [finiteMean, hval, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hcard, one_smul]

end Algebra

section Topology

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

theorem averageMap_mem_fixedVectors (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V) :
    averageMap ρ hρ K hK v ∈ fixedVectors ρ K.toSubgroup := by
  let := finite_orbit_of_smooth ρ hρ K hK v
  exact orbitMean_invariant (ρ.comp K.toSubgroup.subtype) v

theorem averageMap_id (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (v : V)
    (hv : v ∈ fixedVectors ρ K.toSubgroup) :
    averageMap ρ hρ K hK v = v := by
  let := finite_orbit_of_smooth ρ hρ K hK v
  exact orbitMean_id (ρ.comp K.toSubgroup.subtype) v hv

theorem averageMap_isProj (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    LinearMap.IsProj (fixedVectors ρ K.toSubgroup) (averageMap ρ hρ K hK) :=
  ⟨averageMap_mem_fixedVectors ρ hρ K hK, averageMap_id ρ hρ K hK⟩

theorem averageMap_commute (ρ : Representation ℂ G V) (σ : Representation ℂ G W)
    (hρ : IsSmooth ρ) (hσ : IsSmooth σ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (f : ρ.IntertwiningMap σ) :
    f.toLinearMap.comp (averageMap ρ hρ K hK) =
      (averageMap σ hσ K hK).comp f.toLinearMap := by
  ext v
  let := finite_orbit_of_smooth ρ hρ K hK v
  let := finite_orbit_of_smooth σ hσ K hK (f v)
  exact orbitMean_map (ρ.comp K.toSubgroup.subtype) (σ.comp K.toSubgroup.subtype)
    f.toLinearMap (fun k x => f.isIntertwining ρ σ k.val x) v

end Topology

theorem projectionAndNaturality : ProjectionAndNaturality.{uG, uV, uW} := by
  intro G _ _ _ V _ _ W _ _ ρ σ hρ hσ K hK
  exact ⟨averageMap_isProj ρ hρ K hK, averageMap_commute ρ σ hρ hσ K hK⟩

end Langlands.Compact

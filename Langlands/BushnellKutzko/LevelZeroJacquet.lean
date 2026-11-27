import Langlands.BushnellKutzko.LevelZeroCoarse

/-! # Nonzero Jacquet modules for non-maximal level-zero types (standard coordinates) -/

open Matrix ValuativeRel Langlands.Jacquet

noncomputable section

namespace Langlands.BushnellKutzko.LevelZero

universe uF uV uW

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {e f : ℕ}

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
  (π : Representation ℂ (GL (Fin f × Fin e) F) V) (hπ : IsSmooth π)
  (K : OpenSubgroup (GL (Fin f × Fin e) F)) (hK : IsCompact (K : Set (GL (Fin f × Fin e) F)))

variable [Fintype 𝓀[F]]

include hπ hK in
/-- **Jacquet nonvanishing in standard coordinates.** Let `ρ` be a finite-dimensional
representation of the standard `U(𝔄)` (period `e`, blocks of size `f`), trivial on
`U^1(𝔄) = K` and cuspidal on the first block in the form of vanishing sums over lifted unipotent
radicals. If a smooth representation `π` admits a nonzero intertwining map from `ρ`, then the
Jacquet module of `π` along the unipotent radical of the coarse parabolic (first block against
the others) is nonzero. -/
theorem not_subsingleton_coinvariants_coarseN {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ) (he : 0 < e)
    (hKJ : K.toSubgroup = J1 F e f)
    {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (ρ : Representation ℂ (J0 F e f) W)
    (hρ1 : ∀ x : J0 F e f, (x : GL (Fin f × Fin e) F) ∈ J1 F e f → ρ x = 1)
    (hcusp : ∀ (m : Fin e) (hm : (⟨0, he⟩ : Fin e) < m) (r : ℕ), 0 < r → r < f →
      ∑ Z : Matrix (Fin f) (Fin f) 𝓀[F],
        ρ ⟨pairGL hm.ne (diagU (unipLift r Z) 1),
          diagU_mem_J0 hm (isIntGL_unipLift r Z) isIntGL_one⟩ = 0)
    (φ : W →ₗ[ℂ] V) (hφ : ∀ (x : J0 F e f) (w : W), φ (ρ x w) = π x (φ w)) (hφ0 : φ ≠ 0) :
    ¬ Subsingleton (Coinvariants π (coarseN F f he)) := by
  have hJK : ∀ x, x ∈ K ↔ x ∈ J1 F e f := fun x => by
    change x ∈ K.toSubgroup ↔ _; rw [hKJ]
  have hnorm : ∀ x ∈ J0 F e f, ∀ y, y ∈ K ↔ x⁻¹ * y * x ∈ K := by
    intro x hx y
    rw [hJK, hJK]
    exact mem_J1_iff_conj hx y
  let P : (W →ₗ[ℂ] V) → Prop := fun g => ∀ (x : J0 F e f) (w : W), g (ρ x w) = π x (g w)
  have hrange : ∀ g, P g → ∀ w, g w ∈ fixedVectors π K.toSubgroup := by
    intro g hg w k
    have hk : (k : GL (Fin f × Fin e) F) ∈ J1 F e f := (hJK k.val).mp k.property
    change π k (g w) = g w
    rw [← hg ⟨k, J1_le_J0 hk⟩, hρ1 _ hk]
    rfl
  refine not_subsingleton_coinvariants_of_compression π hπ hK
    (coarse_isWeakIwahoriContraction hϖ he K hKJ) (coarse_J1_factor he K hKJ)
    (coarse_exhaust hϖ he K hKJ) (coarseM_le_normalizer he) P hrange ?_ ?_ φ hφ hφ0
  · intro g hg x w
    obtain ⟨l, ⟨hl1, _⟩, m, ⟨hm0, hm2⟩, u, ⟨hu1, _⟩, hx⟩ := coarse_factor he x.2
    have hρx : ρ x = ρ ⟨m, hm0⟩ := by
      have hx' : x = ⟨l, J1_le_J0 hl1⟩ * ⟨m, hm0⟩ * ⟨u, J1_le_J0 hu1⟩ := Subtype.ext hx
      rw [hx', map_mul, map_mul, hρ1 ⟨l, J1_le_J0 hl1⟩ hl1, hρ1 ⟨u, J1_le_J0 hu1⟩ hu1, one_mul,
        mul_one]
    have hcomm : (aElt hϖ he) * m = m * aElt hϖ he := by
      have := aElt_inv_conj_levi hϖ he hm2
      calc aElt hϖ he * m = aElt hϖ he * ((aElt hϖ he)⁻¹ * m * aElt hϖ he) := by rw [this]
        _ = m * aElt hϖ he := by group
    set z := compressionMap π hπ K hK (aElt hϖ he) (g w) with hz
    have hzfix : z ∈ fixedVectors π K.toSubgroup :=
      Compact.averageMap_mem_fixedVectors π hπ K hK _
    have hmz : π m z ∈ fixedVectors π K.toSubgroup := by
      intro k
      change π k (π m z) = π m z
      have hk : m⁻¹ * k * m ∈ K := (hnorm m hm0 k).mp k.property
      calc π k (π m z) = π m (π (m⁻¹ * k * m) z) := by
            simp only [← Module.End.mul_apply, ← map_mul]; congr 2; group
        _ = π m z := by
            have : π (m⁻¹ * k * m) z = z := hzfix ⟨_, hk⟩
            rw [this]
    change compressionMap π hπ K hK (aElt hϖ he) (g (ρ x w)) =
      π x (compressionMap π hπ K hK (aElt hϖ he) (g w))
    rw [hρx, hg, compressionMap_apply]
    have e1 : π (aElt hϖ he) (π m (g w)) = π m (π (aElt hϖ he) (g w)) := by
      rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply]
    rw [show ((⟨m, hm0⟩ : J0 F e f) : GL (Fin f × Fin e) F) = m from rfl, e1,
      averageMap_apply_normalizing π hπ K hK m (hnorm m hm0), ← compressionMap_apply, ← hz]
    rw [show (x : GL (Fin f × Fin e) F) = l * m * u from hx, map_mul, map_mul,
      Module.End.mul_apply, Module.End.mul_apply]
    have hu : π u z = z := hzfix ⟨u, (hJK u).mpr hu1⟩
    have hl : π l (π m z) = π m z := hmz ⟨l, (hJK l).mpr hl1⟩
    rw [hu, hl]
  · intro g hg h0
    exact compressionMap_aElt_comp_eq_zero π hπ K hK hϖ he hKJ ρ hρ1 hcusp g hg h0

end Langlands.BushnellKutzko.LevelZero

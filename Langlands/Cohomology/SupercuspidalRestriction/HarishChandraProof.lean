import Langlands.Cohomology.SupercuspidalRestriction.Statement
import Langlands.Representation.GodementJacquet.SupercuspidalMatrixSupport

/-!
# Harish-Chandra's theorem for supercuspidal representations of `GL_n(F)`

Proof of `GLHarishChandraStatement` (Bernstein–Zelevinsky 1976, 3.21,
(1) ⇒ (3)): every supercuspidal smooth representation of `GL_n(F)` has
smooth matrix coefficients that are compactly supported modulo the center.
Irreducibility is not assumed; admissibility replaces a central character.
-/

noncomputable section

namespace Langlands.Cohomology.SupercuspidalRestriction

section General

universe uG uV

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Let `H` be a normal subgroup such that `H ⊔ Z(G)` has finite index, and let
`ℓ` be a linear form whose coefficients `h ↦ ℓ (ρ h w)` on `H` are compactly
supported for every vector `w`. If all central translates `ρ z v` of `v` lie in
one finite-dimensional subspace, then the support of `g ↦ ℓ (ρ g v)` lies in
the inverse image of a compact subset of `G ⧸ Z(G)`. -/
theorem exists_isCompact_mk_of_central_orbit_finiteDimensional
    (ρ : Representation ℂ G V) (H : Subgroup G) [H.Normal]
    [(H ⊔ Subgroup.center G).FiniteIndex] (ℓ : Module.Dual ℂ V)
    (hH : ∀ w : V, HasCompactSupport (fun h : H => ℓ (ρ h w)))
    (v : V) (W : Submodule ℂ V) [FiniteDimensional ℂ W]
    (hW : ∀ z ∈ Subgroup.center G, ρ z v ∈ W) :
    ∃ C : Set (G ⧸ Subgroup.center G), IsCompact C ∧
      ∀ g : G, ℓ (ρ g v) ≠ 0 → (QuotientGroup.mk g : G ⧸ Subgroup.center G) ∈ C := by
  let N := H ⊔ Subgroup.center G
  let b := Module.finBasis ℂ W
  let r : G ⧸ N → G := fun j => j.out
  let S : G ⧸ N → Fin (Module.finrank ℂ W) → Set H := fun j i =>
    tsupport (fun h : H => ℓ (ρ h (ρ (r j) (b i : V))))
  let K : Set G := ⋃ j, ⋃ i, (fun h : H => (h : G) * r j) '' S j i
  have hK : IsCompact K := by
    apply isCompact_iUnion
    intro j
    apply isCompact_iUnion
    intro i
    exact (hH _).image (continuous_subtype_val.mul continuous_const)
  refine ⟨QuotientGroup.mk '' K, hK.image QuotientGroup.continuous_mk, ?_⟩
  intro g hg
  let j : G ⧸ N := QuotientGroup.mk g
  obtain ⟨n0, hn0⟩ := QuotientGroup.mk_out_eq_mul N g
  have hn0' : r j = g * n0 := hn0
  have hmem : (n0 : G)⁻¹ ∈ N := N.inv_mem n0.2
  obtain ⟨h, hh, z, hz, hhz⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  let h' : G := r j * h * (r j)⁻¹
  have hh' : h' ∈ H := Subgroup.Normal.conj_mem inferInstance h hh (r j)
  have hg' : g = h' * r j * z := by
    have : g = r j * (n0 : G)⁻¹ := by rw [hn0']; group
    rw [this, ← hhz]
    simp only [h']
    group
  -- Expand the central translate `ρ z v` in the chosen basis of `W`.
  obtain ⟨c, hc⟩ : ∃ c : Fin (Module.finrank ℂ W) → ℂ,
      ρ z v = ∑ i, c i • (b i : V) := by
    refine ⟨b.repr ⟨ρ z v, hW z hz⟩, ?_⟩
    have h1 := congrArg (Subtype.val : W → V) (b.sum_repr ⟨ρ z v, hW z hz⟩)
    rw [Submodule.coe_sum] at h1
    simp only [Submodule.coe_smul] at h1
    exact h1.symm
  have he : ℓ (ρ g v) = ∑ i, c i * ℓ (ρ (⟨h', hh'⟩ : H) (ρ (r j) (b i : V))) := by
    rw [hg', map_mul, Module.End.mul_apply, hc, map_sum, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_smul, map_smul, map_mul, Module.End.mul_apply]
    rfl
  obtain ⟨i, _, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero (he ▸ hg)
  have hs : (⟨h', hh'⟩ : H) ∈ S j i := by
    apply subset_tsupport
    exact right_ne_zero_of_mul hi
  refine ⟨h' * r j, Set.mem_iUnion.mpr ⟨j, Set.mem_iUnion.mpr ⟨i, ⟨⟨h', hh'⟩, hs, rfl⟩⟩⟩, ?_⟩
  rw [hg', QuotientGroup.mk_mul_of_mem _ hz]

end General

section GeneralLinearGroup

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{0} p)

local instance : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance (n : ℕ) : TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

local instance (n : ℕ) : IsTopologicalGroup (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopologicalGroup n

/-- Bernstein–Zelevinsky 1976, 3.21, (1) ⇒ (3): every supercuspidal smooth
complex representation of `GL_n(F)` has smooth matrix coefficients compactly
supported modulo the center. -/
theorem glHarishChandraStatement_proof (n : ℕ) : GLHarishChandraStatement F n := by
  intro π hπ ℓ v
  cases n with
  | zero =>
    refine ⟨{QuotientGroup.mk 1}, isCompact_singleton, fun g _ => ?_⟩
    have hg : g ∈ Subgroup.center (GeneralLinear 0 F.Carrier) :=
      Subgroup.mem_center_iff.mpr fun h => Units.ext (Matrix.ext fun i => i.elim0)
    rw [Set.mem_singleton_iff, ← one_mul g, QuotientGroup.mk_mul_of_mem _ hg]
  | succ d =>
    let T := F.canonicalTopologicalData
    have := GodementJacquet.determinantNorm_ker_sup_center_finiteIndex T (n := d)
    obtain ⟨K, hK⟩ := π.isSmooth v
    let W := fixedVectors π.representation K.toSubgroup
    have : FiniteDimensional ℂ W := hπ.1.2 K
    have hW : ∀ z ∈ Subgroup.center (GeneralLinear (d + 1) F.Carrier),
        π.representation z v ∈ W := by
      intro z hz
      have hK' : ∀ k : K.toSubgroup,
          π.representation (k : GeneralLinear (d + 1) F.Carrier) v = v := hK
      show ∀ k : K.toSubgroup, π.representation (k : GeneralLinear (d + 1) F.Carrier)
        (π.representation z v) = π.representation z v
      intro k
      rw [← Module.End.mul_apply, ← map_mul, Subgroup.mem_center_iff.mp hz,
        map_mul, Module.End.mul_apply, hK' k]
    exact exists_isCompact_mk_of_central_orbit_finiteDimensional π.representation
      (T.determinantNorm (d + 1)).ker (smoothDualPairing π.representation ℓ)
      (fun w => GodementJacquet.hasCompactSupport_determinantUnit_coefficient T
        (Nat.zero_lt_succ d) π.representation hπ w ℓ.val ℓ.property) v W hW

end GeneralLinearGroup

end Langlands.Cohomology.SupercuspidalRestriction

import Langlands.Representation.Compact.Definitions
import Langlands.Representation.CuspidalSupport.DeterminantUnit
import Langlands.Representation.Geometric.WeylDefinitions
import Langlands.Group.GL.BlockIwahoriBasis

/-!
# Averaging against smooth functionals, and compact open bases of product Levis

A functional that is smooth for the dual action is unchanged by first averaging
over any compact open subgroup fixing it. Product Levis and their determinant-unit
subgroups have neighbourhood bases of compact open subgroups.
-/

noncomputable section

open Filter Topology

namespace Langlands

universe uG uV uF

namespace Compact

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A functional fixed by a compact open subgroup under the dual action is
unchanged by first averaging over that subgroup. -/
theorem dual_averageMap_eq_of_mem_fixedVectors (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (ℓ : Module.Dual ℂ V)
    (hℓ : ℓ ∈ fixedVectors ρ.dual K.toSubgroup) (w : V) :
    ℓ (averageMap ρ hρ K hK w) = ℓ w := by
  classical
  let τ := ρ.comp K.toSubgroup.subtype
  let := finite_orbit_of_smooth ρ hρ K hK w
  let := Fintype.ofFinite (orbit τ w)
  have hx (x : orbit τ w) : ℓ x.val = ℓ w := by
    obtain ⟨k, hk⟩ := x.property
    rw [← hk]
    have h := LinearMap.congr_fun (hℓ k⁻¹) w
    simpa [τ, Representation.dual_apply, Module.Dual.transpose_apply] using h
  have hc : (Fintype.card (orbit τ w) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  change ℓ (orbitMean τ w) = ℓ w
  rw [orbitMean_eq_finiteMean]
  change ℓ ((Fintype.card (orbit τ w) : ℂ)⁻¹ • ∑ x : orbit τ w, x.val) = ℓ w
  rw [map_smul, map_sum]
  simp only [hx, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul,
    ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

/-- If compact open subgroups form a neighbourhood basis of `1`, every functional
that is smooth for the dual action is unchanged by averaging over some compact open
subgroup, which may be chosen inside any given neighbourhood of `1`. -/
theorem exists_dual_averageMap_eq (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (hbasis : ∀ U ∈ 𝓝 (1 : G), ∃ K : OpenSubgroup G, IsCompact (K : Set G) ∧ (K : Set G) ⊆ U)
    (ℓ : Module.Dual ℂ V) (hℓ : IsSmoothVector ρ.dual ℓ) {U : Set G} (hU : U ∈ 𝓝 (1 : G)) :
    ∃ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)), (K : Set G) ⊆ U ∧
      ∀ w, ℓ (averageMap ρ hρ K hK w) = ℓ w := by
  obtain ⟨H, hH⟩ := hℓ
  obtain ⟨K, hK, hKU⟩ := hbasis (U ∩ H) (Filter.inter_mem hU H.mem_nhds_one)
  refine ⟨K, hK, fun x hx => (hKU hx).1, fun w =>
    dual_averageMap_eq_of_mem_fixedVectors ρ hρ K hK ℓ ?_ w⟩
  intro k
  exact hH ⟨k.val, (hKU k.property).2⟩

end Compact

namespace CuspidalSupport

open GeneralLinear Geometric

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : BlockShape n)

/-- The product of open subgroups of the Levi factors, as an open subgroup. -/
def leviPiOpenSubgroup :
    letI := T.topology
    (∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)) → OpenSubgroup (B.Levi F.Carrier) := by
  letI := T.topology
  exact fun K =>
    { toSubgroup := Subgroup.pi Set.univ fun j => (K j).toSubgroup
      isOpen' := by
        change IsOpen ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
          Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
        rw [Subgroup.coe_pi]
        exact isOpen_set_pi Set.finite_univ fun j _ => (K j).isOpen }

theorem mem_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)) (g : B.Levi F.Carrier),
      g ∈ leviPiOpenSubgroup T B K ↔ ∀ j, g j ∈ K j := by
  let := T.topology
  intro K g
  change g ∈ Subgroup.pi Set.univ (fun j => (K j).toSubgroup) ↔ _
  rw [Subgroup.mem_pi]
  simp

theorem isCompact_leviPiOpenSubgroup :
    letI := T.topology
    ∀ (K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier)),
      (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F.Carrier))) →
      IsCompact (leviPiOpenSubgroup T B K : Set (B.Levi F.Carrier)) := by
  let := T.topology
  intro K hK
  change IsCompact ((Subgroup.pi Set.univ fun j => (K j).toSubgroup :
    Subgroup (B.Levi F.Carrier)) : Set (B.Levi F.Carrier))
  rw [Subgroup.coe_pi]
  exact isCompact_univ_pi hK

/-- Every identity neighbourhood of the product Levi contains a product of compact
open subgroups, each with a block Iwahori factorization for the given refinement. -/
theorem exists_leviPiOpenSubgroup_subset (S : BlockRefinement B) :
    letI := T.topology
    ∀ {U : Set (B.Levi F.Carrier)}, U ∈ 𝓝 (1 : B.Levi F.Carrier) →
      ∃ K : ∀ j, OpenSubgroup (GeneralLinear (B.size j) F.Carrier),
        (∀ j, IsCompact (K j : Set (GeneralLinear (B.size j) F.Carrier))) ∧
        (∀ j, (S j).HasBlockIwahoriFactorization T (K j)) ∧
        (leviPiOpenSubgroup T B K : Set (B.Levi F.Carrier)) ⊆ U := by
  let := T.topology
  intro U hU
  rw [nhds_pi, Filter.mem_pi'] at hU
  obtain ⟨I, O, hO, hOU⟩ := hU
  choose K hKc hKO hfac using fun j => (S j).blockIwahoriBasis T (O j) (hO j)
  refine ⟨K, hKc, hfac, ?_⟩
  intro g hg
  apply hOU
  intro j _
  exact hKO j ((mem_leviPiOpenSubgroup T B K g).mp hg j)

/-- Compact open subgroups form a neighbourhood basis of `1` in the product Levi. -/
theorem levi_exists_compact_openSubgroup_subset :
    letI := T.topology
    ∀ U ∈ 𝓝 (1 : B.Levi F.Carrier), ∃ K : OpenSubgroup (B.Levi F.Carrier),
      IsCompact (K : Set (B.Levi F.Carrier)) ∧ (K : Set (B.Levi F.Carrier)) ⊆ U := by
  let := T.topology
  intro U hU
  let S : BlockRefinement B := fun j =>
    { length := 1
      size := fun _ => B.size j
      positive := fun _ => B.positive j
      sum_eq := by simp }
  obtain ⟨K, hKc, -, hKU⟩ := exists_leviPiOpenSubgroup_subset T B S hU
  exact ⟨leviPiOpenSubgroup T B K, isCompact_leviPiOpenSubgroup T B K hKc, hKU⟩

/-- Compact open subgroups form a neighbourhood basis of `1` in `G°`. -/
theorem determinantUnit_exists_compact_openSubgroup_subset :
    letI := T.topology
    letI := T.leviTopologicalGroup B
    ∀ U ∈ 𝓝 (1 : determinantUnitSubgroup T B), ∃ K : OpenSubgroup (determinantUnitSubgroup T B),
      IsCompact (K : Set (determinantUnitSubgroup T B)) ∧
        (K : Set (determinantUnitSubgroup T B)) ⊆ U := by
  let := T.topology
  let := T.leviTopologicalGroup B
  intro U hU
  rw [mem_nhds_subtype] at hU
  obtain ⟨u, hu, huU⟩ := hU
  obtain ⟨N, hNc, hNu⟩ := levi_exists_compact_openSubgroup_subset T B u hu
  refine ⟨N.comap (determinantUnitInclusion T B) (continuous_determinantUnitInclusion T B),
    ?_, fun x hx => huU (hNu hx)⟩
  have hcl : IsClosed (determinantUnitSubgroup T B : Set (B.Levi F.Carrier)) :=
    (determinantUnitOpenSubgroup T B).isClosed
  exact hcl.isClosedEmbedding_subtypeVal.isCompact_preimage hNc

end CuspidalSupport

end Langlands

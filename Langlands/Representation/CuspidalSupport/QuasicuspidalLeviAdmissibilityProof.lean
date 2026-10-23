import Langlands.Representation.CuspidalSupport.QuasicuspidalPrerequisitesStatement
import Langlands.Representation.CuspidalSupport.LeviGapVanishing
import Langlands.Representation.Jacquet.ExactProof
import Langlands.Group.GL.IntegralSubgroup
import Langlands.Group.GL.CartanProof
import Langlands.Representation.Schur.CountableDimensionProof

/-!
# Admissibility of irreducible quasicuspidal product-Levi representations
-/

noncomputable section

open Filter Topology

namespace Langlands.CuspidalSupport.LeviAdmissibility

open GeneralLinear Geometric

universe uF uV

/-! ### Generic facts about irreducible and compact groups -/

section Generic

variable {G : Type*} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- An irreducible representation has a nonzero vector. -/
theorem exists_ne_zero_of_isIrreducible (ρ : Representation ℂ G V)
    (hirr : ρ.IsIrreducible) : ∃ v : V, v ≠ 0 := by
  by_contra! h
  have := hirr
  apply (bot_ne_top : (⊥ : Subrepresentation ρ) ≠ ⊤)
  apply Subrepresentation.toSubmodule_injective
  ext v
  rw [h v]
  exact ⟨fun _ => Submodule.zero_mem _, fun _ => Submodule.zero_mem _⟩

/-- The orbit of a nonzero vector of an irreducible representation spans it. -/
theorem span_orbit_eq_top (ρ : Representation ℂ G V) (hirr : ρ.IsIrreducible)
    {v : V} (hv : v ≠ 0) : Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ := by
  let S : Subrepresentation ρ :=
    { toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g v)
      apply_mem_toSubmodule := fun g x hx => by
        induction hx using Submodule.span_induction with
        | mem y hy =>
          obtain ⟨h, rfl⟩ := hy
          exact Submodule.subset_span ⟨g * h, by
            show ρ (g * h) v = ρ g (ρ h v)
            rw [map_mul, Module.End.mul_apply]⟩
        | zero => rw [map_zero]; exact Submodule.zero_mem _
        | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
        | smul r y _ hy => rw [map_smul]; exact Submodule.smul_mem _ r hy }
  rcases hirr.eq_bot_or_eq_top S with h | h
  · exfalso
    have hmem : v ∈ S.toSubmodule := Submodule.subset_span ⟨1, by
      show ρ 1 v = v
      rw [map_one]
      rfl⟩
    rw [h] at hmem
    exact hv hmem
  · exact congrArg Subrepresentation.toSubmodule h

/-- Finitely many right cosets of an open subgroup cover a compact set. -/
theorem exists_finset_mul_inv_mem [TopologicalSpace G] [IsTopologicalGroup G]
    {S : Set G} (hS : IsCompact S) (H : OpenSubgroup G) :
    ∃ C : Finset G, ∀ k ∈ S, ∃ c ∈ C, k * c⁻¹ ∈ H := by
  obtain ⟨t, ht⟩ := hS.elim_finite_subcover (fun c : G => (· * c⁻¹) ⁻¹' (H : Set G))
    (fun c => H.isOpen.preimage (continuous_id.mul continuous_const))
    (fun k _ => Set.mem_iUnion.mpr ⟨k, by
      change k * k⁻¹ ∈ H
      rw [mul_inv_cancel]
      exact H.one_mem⟩)
  refine ⟨t, fun k hk => ?_⟩
  obtain ⟨c, hc, hkc⟩ := Set.mem_iUnion₂.mp (ht hk)
  exact ⟨c, hc, hkc⟩

/-- An irreducible smooth representation has countable dimension when the group is
covered by countably many double cosets of a compact open subgroup. -/
theorem rank_le_aleph0_of_doubleCoset_cover [TopologicalSpace G] [IsTopologicalGroup G]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (S : Set G) (hS : S.Countable)
    (hcover : ∀ g : G, ∃ k₁ ∈ K, ∃ s ∈ S, ∃ k₂ ∈ K, g = k₁ * s * k₂) :
    Module.rank ℂ V ≤ Cardinal.aleph0 := by
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible ρ hirr
  let orb : V → Set V := fun v => Compact.orbit (ρ.comp K.toSubgroup.subtype) v
  have hfin : ∀ v, (orb v).Countable := fun v =>
    haveI := Compact.finite_orbit_of_smooth ρ hρ K hK v
    (Set.toFinite (orb v)).countable
  let T : Set V := ⋃ s ∈ S, ⋃ w ∈ orb v₀, orb (ρ s w)
  have hT : T.Countable := hS.biUnion fun s _ => (hfin v₀).biUnion fun w _ => hfin _
  have hsub : Set.range (fun g => ρ g v₀) ⊆ T := by
    rintro _ ⟨g, rfl⟩
    obtain ⟨k₁, hk₁, s, hs, k₂, hk₂, rfl⟩ := hcover g
    simp only [T, Set.mem_iUnion]
    refine ⟨s, hs, ρ k₂ v₀, ⟨⟨k₂, hk₂⟩, rfl⟩, ⟨k₁, hk₁⟩, ?_⟩
    change ρ k₁ (ρ s (ρ k₂ v₀)) = ρ (k₁ * s * k₂) v₀
    rw [map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
  calc Module.rank ℂ V = Module.rank ℂ (⊤ : Submodule ℂ V) := (rank_top ℂ V).symm
    _ = Module.rank ℂ (Submodule.span ℂ (Set.range fun g => ρ g v₀)) := by
      rw [span_orbit_eq_top ρ hirr hv₀]
    _ ≤ Cardinal.mk (Set.range fun g => ρ g v₀) := rank_span_le _
    _ ≤ Cardinal.aleph0 := Cardinal.mk_le_aleph0_iff.mpr (hT.mono hsub).to_subtype

/-- A central element acts by a scalar on an irreducible representation of countable
dimension. -/
theorem exists_scalar_of_central (ρ : Representation ℂ G V)
    (hrank : Module.rank ℂ V ≤ Cardinal.aleph0) (hirr : ρ.IsIrreducible) (z : G)
    (hz : ∀ g, g * z = z * g) : ∃ s : ℂ, ∀ v, ρ z v = s • v := by
  let f : ρ.IntertwiningMap ρ :=
    { toLinearMap := ρ z
      isIntertwining' := fun g => by
        ext v
        change ρ z (ρ g v) = ρ g (ρ z v)
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, hz] }
  obtain ⟨s, hs, -⟩ := countableDimensionalSchur ρ hrank hirr f
  refine ⟨s, fun v => ?_⟩
  have h := congrArg (fun φ : ρ.IntertwiningMap ρ => φ v) hs
  simpa [f, Representation.IntertwiningMap.smul_apply] using h

end Generic

/-! ### The product Levi over a local field -/

section Levi

variable {K : Type uF} [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]

variable {n : ℕ} (B : BlockShape n)

/-- The Cartan decomposition of the Levi, block by block. -/
theorem exists_levi_cartan {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ) (g : B.Levi K) :
    ∃ k₁ ∈ integralLevi B, ∃ lam : ∀ j : Fin B.length, Fin (B.size j) → ℤ,
      (∀ j, Antitone (lam j)) ∧ ∃ k₂ ∈ integralLevi B, g = k₁ * leviTorus B ϖ lam * k₂ := by
  have h := fun j => (Cartan.cartanDecomposition K (ValuativeRel.ValueGroupWithZero K)
    (ValuativeRel.valuation K) ϖ hϖ (B.size j) (g j)).exists
  choose lam hlam k₁ hk₁ k₂ hk₂ hg using h
  exact ⟨k₁, (mem_integralLevi B).mpr hk₁, lam, hlam, k₂, (mem_integralLevi B).mpr hk₂,
    funext hg⟩

variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Assembly: the fixed vectors of every open subgroup lie in the span of finitely
many averaged translates of one nonzero vector. -/
theorem finite_fixedVectors
    (ρ : Representation ℂ (B.Levi K) V) (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible)
    (hq : IsLeviQuasicuspidal B ρ) {ϖ : Kˣ}
    (hϖ : Iwasawa.IsUniformizingElement (ValuativeRel.valuation K) ϖ)
    (hscalar : ∀ c : Fin B.length → ℤ, ∃ s : ℂ, ∀ v,
      ρ (leviTorus B ϖ fun j _ => c j) v = s • v)
    (hbox : ∀ N : ℤ, BoundedGapReps B N)
    (H : OpenSubgroup (B.Levi K)) :
    Module.Finite ℂ (fixedVectors ρ H.toSubgroup) := by
  classical
  let K₀ := integralLevi (K := K) B
  have hK₀ : IsCompact (K₀ : Set (B.Levi K)) := isCompact_integralLevi B
  let Kc : OpenSubgroup (B.Levi K) := H ⊓ K₀
  have hKc : IsCompact (Kc : Set (B.Levi K)) :=
    hK₀.of_isClosed_subset Kc.isClosed fun x hx => (OpenSubgroup.mem_inf.mp hx).2
  obtain ⟨v₀, hv₀⟩ := exists_ne_zero_of_isIrreducible ρ hirr
  let W := Compact.orbit (ρ.comp K₀.toSubgroup.subtype) v₀
  have : Finite W := Compact.finite_orbit_of_smooth ρ hρ K₀ hK₀ v₀
  obtain ⟨C, hC⟩ := exists_finset_mul_inv_mem hK₀ Kc
  obtain ⟨N, hN⟩ := exists_uniform_gap_bound B ρ hρ hq hϖ Kc hKc (ι := C × W)
    (fun x => x.1.1) (fun x => x.2.1)
  obtain ⟨Λ₀, hΛ₀, hrep⟩ := hbox N
  let avg := Compact.averageMap ρ hρ Kc hKc
  let Φ : Set V := (fun x : B.Levi K × (∀ j : Fin B.length, Fin (B.size j) → ℤ) × V =>
      avg (ρ (x.1 * leviTorus B ϖ x.2.1) x.2.2)) '' ((C : Set (B.Levi K)) ×ˢ Λ₀ ×ˢ W)
  have hΦ : Φ.Finite := (C.finite_toSet.prod (hΛ₀.prod (Set.toFinite W))).image _
  have hgen : ∀ g : B.Levi K, avg (ρ g v₀) ∈ Submodule.span ℂ Φ := by
    intro g
    obtain ⟨k₁, hk₁, lam, hlam, k₂, hk₂, rfl⟩ := exists_levi_cartan B hϖ g
    obtain ⟨c, hc, hkc⟩ := hC k₁ hk₁
    have hw : ρ k₂ v₀ ∈ W := ⟨⟨k₂, hk₂⟩, rfl⟩
    have heq : avg (ρ (k₁ * leviTorus B ϖ lam * k₂) v₀) =
        avg (ρ (c * leviTorus B ϖ lam) (ρ k₂ v₀)) := by
      have hk : k₁ * leviTorus B ϖ lam * k₂ =
          (k₁ * c⁻¹) * (c * leviTorus B ϖ lam) * k₂ := by
        group
      rw [hk, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
      exact Compact.orbitMean_apply (ρ.comp Kc.toSubgroup.subtype) ⟨_, hkc⟩ _
    rw [heq]
    by_cases hdeep : ∃ (i : Fin B.length) (a : ℕ) (ha : a + 1 < B.size i),
        N ≤ lam i ⟨a, by omega⟩ - lam i ⟨a + 1, ha⟩
    · obtain ⟨i, a, ha, hgap⟩ := hdeep
      rw [hN (⟨c, hc⟩, ⟨_, hw⟩) lam hlam i a ha hgap]
      exact Submodule.zero_mem _
    · push Not at hdeep
      obtain ⟨μ, hμ, s, hs⟩ := hrep lam hlam fun j b h => hdeep j b.val h
      obtain ⟨z, hz⟩ := hscalar s
      have hlam' : lam = fun j b => μ j b + s j := funext fun j => funext fun b => hs j b
      rw [hlam', leviTorus_add_const, ← mul_assoc, map_mul, Module.End.mul_apply, hz,
        map_smul, map_smul]
      exact Submodule.smul_mem _ z
        (Submodule.subset_span ⟨(c, μ, ρ k₂ v₀), ⟨hc, hμ, hw⟩, rfl⟩)
  have hspan : Submodule.span ℂ (Set.range fun g => ρ g v₀) ≤
      (Submodule.span ℂ Φ).comap avg := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hgen g
  have hle : fixedVectors ρ H.toSubgroup ≤ Submodule.span ℂ Φ := by
    intro x hx
    have hxKc : x ∈ fixedVectors ρ Kc.toSubgroup := by
      rw [fixedVectors, Representation.mem_invariants] at hx ⊢
      intro k
      exact hx ⟨k.1, (OpenSubgroup.mem_inf.mp k.2).1⟩
    have hx' : x ∈ (Submodule.span ℂ Φ).comap avg := by
      apply hspan
      rw [span_orbit_eq_top ρ hirr hv₀]
      exact Submodule.mem_top
    rw [Submodule.mem_comap, Compact.averageMap_id ρ hρ Kc hKc x hxKc] at hx'
    exact hx'
  have : FiniteDimensional ℂ (Submodule.span ℂ Φ) := FiniteDimensional.span_of_finite ℂ hΦ
  exact Submodule.finiteDimensional_of_le hle

/-- Irreducible smooth quasicuspidal representations of a product Levi over a
nonarchimedean local field are admissible. -/
theorem isAdmissible_of_isLeviQuasicuspidal
    (ρ : Representation ℂ (B.Levi K) V)
    (hρ : IsSmooth ρ) (hirr : ρ.IsIrreducible) (hq : IsLeviQuasicuspidal B ρ) :
    IsAdmissible ρ := by
  obtain ⟨ϖ, hϖ⟩ := Iwasawa.exists_isUniformizingElement K
  have hrank : Module.rank ℂ V ≤ Cardinal.aleph0 :=
    rank_le_aleph0_of_doubleCoset_cover ρ hρ hirr (integralLevi B) (isCompact_integralLevi B)
      (Set.range (leviTorus B ϖ)) (Set.countable_range _) fun g => by
        obtain ⟨k₁, hk₁, lam, -, k₂, hk₂, hg⟩ := exists_levi_cartan B hϖ g
        exact ⟨k₁, hk₁, _, ⟨lam, rfl⟩, k₂, hk₂, hg⟩
  have hscalar : ∀ c : Fin B.length → ℤ, ∃ s : ℂ, ∀ v,
      ρ (leviTorus B ϖ fun j _ => c j) v = s • v := fun c =>
    exists_scalar_of_central ρ hrank hirr _ (leviTorus_const_comm B ϖ c)
  exact ⟨hρ, fun H =>
    finite_fixedVectors B ρ hρ hirr hq hϖ hscalar (boundedGapReps B) H⟩

end Levi

/-- The published proposition family, from the published Cartan decomposition
`Langlands.GeneralLinear.Cartan.cartanDecomposition` and Schur's lemma in countable
dimension `Langlands.countableDimensionalSchur`. -/
theorem irreducibleQuasicuspidalLeviAdmissibility
    {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p) (T : F.TopologicalData)
    {n : ℕ} (B : BlockShape n) :
    IrreducibleQuasicuspidalLeviAdmissibilityTheorem.{uF, uV} F T B := by
  let := T.topology
  let := T.valuativeRel
  have := T.localField
  intro σ hirr hq
  exact isAdmissible_of_isLeviQuasicuspidal B σ.representation σ.isSmooth hirr hq

end Langlands.CuspidalSupport.LeviAdmissibility

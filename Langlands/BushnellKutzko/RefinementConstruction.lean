import Langlands.BushnellKutzko.RefinementCentralizer
import Langlands.BushnellKutzko.RefinementInvariants

/-! # Construction of the refined element

This file assembles the abstract construction behind BK93 (2.2.8). A field `L` acts on `V`,
normalizing the chain, and contains (the actions of) `β` and `c`. Given a corestriction-like
additive map `s` with the exactness inputs used by `refinement_core`, and a perturbation
`b ∈ 𝔓^{-r}` with `s(b) ≡ c (mod 𝔓^{1-r})`, we construct `γ ≡ β + b (mod 𝔓^{1-r})` such that
`F[γ]` consists of normalizing units, `F[γ]` and `L` approximate each other, elements of
`𝔄` commuting with `L` are congruent modulo `𝔓` to elements commuting with `γ`, and
`F[γ] = F` when `L = F`.

The element is `γ = g⁻¹ (β + σ(b)) g`, where `σ(b) = Σ_j ε_{j l₀} b ε_{l₀ j}` is the
diagonal part of `b` with respect to a relative splitting basis and `g ∈ U^1(𝔄)` corrects the
difference `b - σ(b)` as in BK93 (2.2.1).
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uL

section Blocks

variable {F : Type uF} [Field F] {V : Type uV} [AddCommGroup V] [Module F V]
  {L : Type uL} [Field L] [Algebra F L] [Module L V] [IsScalarTower F L V]

/-- A block of an `L`-linear endomorphism is an `L`-multiple of a matrix unit. -/
theorem block_eq_of_commute {n : ℕ} (w : Module.Basis (Fin n) L V) {z : Module.End F V}
    (hz : ∀ a : L, z * subfieldEmbedding F L V a = subfieldEmbedding F L V a * z) (j l : Fin n) :
    matUnit F w j j * z * matUnit F w l l =
      subfieldEmbedding F L V (w.repr (z (w l)) j) * matUnit F w j l := by
  have hza : ∀ (a : L) (x : V), z (a • x) = a • z x := fun a x => by
    have := LinearMap.congr_fun (hz a) x
    simpa only [Module.End.mul_apply, subfieldEmbedding_apply] using this
  ext v
  change matUnit F w j j (z (matUnit F w l l v)) =
    (w.repr (z (w l)) j) • (matUnit F w j l v)
  simp only [matUnit_apply]
  rw [hza, LinearEquiv.map_smul, Finsupp.smul_apply, smul_eq_mul, smul_smul,
    mul_comm (w.repr v l)]

end Blocks

section Construction

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V] [FiniteDimensional F V]
  {L : Type uL} [Field L] [Algebra F L] [Module L V] [IsScalarTower F L V]
  (𝓛 : LatticeChain 𝒪[F] F V)
  (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer)

local notation "P" => 𝓛.endFiltration

include hnormal in
/-- **Construction of the refined element** (BK93 (2.2.8), with (2.2.1)). -/
theorem exists_refined_element {β c : Module.End F V} {r : ℤ}
    (hβL : ∃ a : L, subfieldEmbedding F L V a = β)
    (hcL : ∃ a : L, subfieldEmbedding F L V a = c)
    (hgen : ∀ γ : Module.End F V, Commute γ β → Commute γ c →
      ∀ a : L, γ * subfieldEmbedding F L V a = subfieldEmbedding F L V a * γ)
    (s : Module.End F V →+ Module.End F V)
    (hs_mem : ∀ (m : ℤ) (z : Module.End F V), z ∈ P m → s z ∈ P m)
    (hs_adj : ∀ X, s (β * X - X * β) = 0)
    (hs_left : ∀ Y z, Commute Y β → s (Y * z) = Y * s z)
    (hs_right : ∀ Y z, Commute Y β → s (z * Y) = s z * Y)
    (hU1 : ∀ (t : ℤ) (X : Module.End F V), X ∈ P t → β * X - X * β ∈ P (t - r) →
      ∃ x ∈ P (t + 1), Commute (X - x) β)
    (hV1 : ∀ (t : ℤ) (γ : Module.End F V), Commute γ β → γ ∈ P t →
      c * γ - γ * c ∈ P (t + 1 - r) → ∃ γ₁, Commute γ₁ β ∧ Commute γ₁ c ∧ γ - γ₁ ∈ P (t + 1))
    (hU2 : ∀ z ∈ P (-r), s z ∈ P (1 - r) → ∃ y ∈ P 1, z - (β * y - y * β) ∈ P (1 - r))
    {b : Module.End F V} (hb : b ∈ P (-r)) (hsb : s b - c ∈ P (1 - r)) :
    ∃ γ : Module.End F V,
      γ - (β + b) ∈ P (1 - r) ∧
      NormalizingUnits 𝓛 (elementAlgebra γ) ∧
      Approx 𝓛 (elementAlgebra γ : Set (Module.End F V)) (Set.range (subfieldEmbedding F L V)) ∧
      Approx 𝓛 (Set.range (subfieldEmbedding F L V)) (elementAlgebra γ : Set (Module.End F V)) ∧
      (∀ y ∈ P 0, Commute y β → Commute y c → ∃ z ∈ P 0, Commute z γ ∧ y - z ∈ P 1) ∧
      (Module.finrank F L = 1 → elementAlgebra γ = ⊥) := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨n, w, hw⟩ := exists_relSplits_basis 𝓛 hϖ hnormal
  have := 𝓛.nontrivial_space
  obtain ⟨l₀⟩ := w.index_nonempty
  have hεβ : ∀ j k, Commute (matUnit F w j k) β := by
    obtain ⟨a, rfl⟩ := hβL
    exact fun j k => (subfieldEmbedding_commute_matUnit w a j k).symm
  have hεc : ∀ j k, Commute (matUnit F w j k) c := by
    obtain ⟨a, rfl⟩ := hcL
    exact fun j k => (subfieldEmbedding_commute_matUnit w a j k).symm
  -- the diagonal part `b₁ = σ(b)` and the element `β₁ = β + b₁`
  obtain ⟨b₁, hb₁def⟩ : ∃ x, x = diagonal F w (compress F w l₀ b) := ⟨_, rfl⟩
  obtain ⟨β₁, hβ₁def⟩ : ∃ x, x = β + b₁ := ⟨_, rfl⟩
  have hb₁ : b₁ ∈ P (-r) := by
    rw [hb₁def]
    exact diagonal_compress_mem 𝓛 hϖ hnormal hw hb l₀
  have hb₁ε : ∀ j k, b₁ * matUnit F w j k = matUnit F w j k * b₁ := by
    intro j k
    rw [hb₁def]
    exact diagonal_commute_matUnit w _ j k
  have hβ₁ε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁ := by
    intro j k
    rw [hβ₁def, add_mul, mul_add, hb₁ε, (hεβ j k).eq]
  have hsσ : ∀ z, s (diagonal F w (compress F w l₀ z)) =
      diagonal F w (compress F w l₀ (s z)) := by
    intro z
    rw [diagonal_compress, diagonal_compress, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hs_right _ _ (hεβ l₀ j), hs_left _ _ (hεβ j l₀)]
  have hσc : diagonal F w (compress F w l₀ c) = c :=
    diagonal_compress_of_commute w l₀ (fun j k => (hεc j k).eq.symm)
  have hsb₁ : s b₁ - c ∈ P (1 - r) := by
    have h := diagonal_compress_mem 𝓛 hϖ hnormal hw hsb l₀
    rw [compress_sub, map_sub, hσc, ← hsσ, ← hb₁def] at h
    exact h
  -- the core property for `β₁`
  have hcore₁ : ∀ (t : ℤ) (X : Module.End F V), X ∈ P t → Commute X β₁ →
      ∃ γ, (∀ a : L, γ * subfieldEmbedding F L V a = subfieldEmbedding F L V a * γ) ∧
        X - γ ∈ P (t + 1) := by
    intro t X hX hXβ
    have hXc : (β + b₁) * X - X * (β + b₁) ∈ P (t + 1 - r) := by
      rw [← hβ₁def, sub_eq_zero.mpr hXβ.eq.symm]
      exact zero_mem _
    obtain ⟨γ₁, hγβ, hγc, hγ⟩ :=
      refinement_core 𝓛 s hs_mem hs_adj hs_left hs_right hU1 hV1 hb₁ hsb₁ hX hXc
    exact ⟨γ₁, hgen γ₁ hγβ hγc, hγ⟩
  have hN₁ := normalizingUnits_elementAlgebra 𝓛 hϖ hnormal hw l₀ hcore₁ hβ₁ε
  have hA₁ := approx_elementAlgebra_range 𝓛 hϖ hnormal hw l₀ hcore₁ hβ₁ε
  have hA₂ := approx_range_elementAlgebra 𝓛 hϖ hnormal hw l₀ hcore₁ hβ₁ε
  -- the correction `g ∈ U^1` of (2.2.1)
  have hz : b - b₁ ∈ P (-r) := sub_mem hb hb₁
  have hsz : s (b - b₁) ∈ P (1 - r) := by
    rw [map_sub, show s b - s b₁ = (s b - c) - (s b₁ - c) by abel]
    exact sub_mem hsb hsb₁
  obtain ⟨y, hy, hzy⟩ := hU2 _ hz hsz
  obtain ⟨g, hg, hgy⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl (by simpa using hy)
  obtain ⟨hg0, hginv, hg1⟩ := (𝓛.mem_unitFiltration).mp hg
  have hg0' : (g : Module.End F V) ∈ P 0 := hg0
  have hginv' : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) ∈ P 0 := hginv
  have hg1' : (g : Module.End F V) - 1 ∈ P 1 := by simpa using hg1
  have hgs := mem_stabilizer_of_mem_unitFiltration 𝓛 hg
  have hgi : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * g = 1 := Units.inv_mul g
  refine ⟨((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- `γ ≡ β + b (mod 𝔓^{1-r})`
    obtain ⟨W, hWdef⟩ : ∃ x, x = β₁ * y - y * β₁ := ⟨_, rfl⟩
    have heq1 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g - β₁ =
        ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * W := by
      calc ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g - β₁
          = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g -
              (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * g) * β₁ := by
            rw [hgi, one_mul]
        _ = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * (β₁ * g - g * β₁) := by
            noncomm_ring
        _ = ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * W := by
            rw [hgy, hWdef]
            noncomm_ring
    have hWz : W - (b - b₁) ∈ P (1 - r) := by
      have hc := commutator_mem_endFiltration 𝓛 hb₁ hy
      rw [show -r + 1 = 1 - r by ring] at hc
      have heq : W - (b - b₁) = (b₁ * y - y * b₁) - ((b - b₁) - (β * y - y * β)) := by
        rw [hWdef, hβ₁def]
        noncomm_ring
      rw [heq]
      exact sub_mem hc hzy
    have hW : W ∈ P (-r) := by
      have := add_mem hz (𝓛.endFiltration_antitone (by omega) hWz)
      rwa [add_sub_cancel] at this
    have hginv1 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - 1 ∈ P 1 := by
      have h := 𝓛.mul_mem_endFiltration hginv' hg1'
      rw [zero_add, mul_sub, hgi, mul_one] at h
      have := neg_mem h
      rwa [neg_sub] at this
    have key : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g - (β + b) =
        (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) - 1) * W + (W - (b - b₁)) := by
      have h1 : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g =
          β₁ + ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * W := by
        rw [← heq1]
        abel
      rw [h1, hβ₁def]
      noncomm_ring
    rw [key]
    refine add_mem ?_ hWz
    have := 𝓛.mul_mem_endFiltration hginv1 hW
    rwa [show 1 + -r = 1 - r by ring] at this
  · exact normalizingUnits_conj 𝓛 hN₁ hgs
  · exact approx_conj_left 𝓛 hA₁ hg1' hg0' hginv' (fun X hX => conj_mem_elementAlgebra' g hX)
  · exact approx_conj_right 𝓛 hA₂ hg1' hginv' (fun X hX => conj_mem_elementAlgebra g hX)
  · -- elements commuting with `L` are approximated by elements commuting with `γ`
    intro y' hy' hyβ hyc
    have hyL := hgen y' hyβ hyc
    have hblock : ∀ j l, ∃ X ∈ elementAlgebra β₁,
        matUnit F w j j * y' * matUnit F w l l - X * matUnit F w j l ∈ P 1 := by
      intro j l
      have hb0 := block_mem 𝓛 hw hy' j l
      rw [block_eq_of_commute w hyL j l] at hb0 ⊢
      by_cases ha : w.repr (y' (w l)) j = 0
      · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
        rw [ha, map_zero, zero_mul, sub_zero]
        exact zero_mem _
      set a := w.repr (y' (w l)) j with hadef
      let u : Lˣ := Units.mk0 a ha
      have hau : subfieldEmbedding F L V a ∈ P (𝓛.fieldShift L hnormal u).toAdd :=
        (subfieldEmbedding_unit_mem_iff 𝓛 hnormal u _).mpr le_rfl
      obtain ⟨X, hX, hXa⟩ := hA₂ _ ⟨a, rfl⟩ _ hau
      have hinv : subfieldEmbedding F L V a⁻¹ ∈ P (-(𝓛.fieldShift L hnormal u).toAdd) := by
        have := (subfieldEmbedding_unit_mem_iff 𝓛 hnormal u⁻¹
          (-(𝓛.fieldShift L hnormal u).toAdd)).mpr (by simp)
        simpa [u] using this
      have hε : matUnit F w j l ∈ P (-(𝓛.fieldShift L hnormal u).toAdd) := by
        have := 𝓛.mul_mem_endFiltration hinv hb0
        rwa [← mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, one_mul, add_zero] at this
      refine ⟨X, hX, ?_⟩
      rw [← sub_mul]
      have := 𝓛.mul_mem_endFiltration hXa hε
      rwa [show (𝓛.fieldShift L hnormal u).toAdd + 1 + -(𝓛.fieldShift L hnormal u).toAdd = 1 by
        ring] at this
    choose X hX hXmem using hblock
    obtain ⟨z', hz'def⟩ : ∃ x, x = ∑ j, ∑ l, X j l * matUnit F w j l := ⟨_, rfl⟩
    have hyz' : y' - z' ∈ P 1 := by
      have heq : y' - z' = ∑ j, ∑ l,
          (matUnit F w j j * y' * matUnit F w l l - X j l * matUnit F w j l) := by
        simp only [Finset.sum_sub_distrib, hz'def, sum_blocks]
      rw [heq]
      exact sum_mem fun j _ => sum_mem fun l _ => hXmem j l
    have hz'β : Commute z' β₁ := by
      rw [hz'def]
      refine Commute.sum_left _ _ _ fun j _ => Commute.sum_left _ _ _ fun l _ => ?_
      exact (Algebra.commute_of_mem_adjoin_self (hX j l)).symm.mul_left
        (show Commute β₁ (matUnit F w j l) from hβ₁ε j l).symm
    have hz'0 : z' ∈ P 0 := by
      have := sub_mem hy' (𝓛.endFiltration_antitone (by omega) hyz')
      rwa [sub_sub_cancel] at this
    refine ⟨((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z' * g,
      conj_mem 𝓛 hg0' hginv' hz'0, ?_, ?_⟩
    · change ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z' * g *
          (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g) =
        ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g *
          (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z' * g)
      simp only [mul_assoc, Units.mul_inv_cancel_left]
      rw [← mul_assoc z' β₁ g, hz'β.eq, mul_assoc]
    · have h2 := conj_sub_mem 𝓛 hg1' hginv' hz'0
      rw [zero_add] at h2
      have heq : y' - ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z' * g =
          (y' - z') - (((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * z' * g - z') := by abel
      rw [heq]
      exact sub_mem hyz' h2
  · -- the scalar case
    intro hL1
    have := 𝓛.finiteDimensional_subfield L
    have : FiniteDimensional F (elementAlgebra β₁) :=
      Module.Finite.of_injective (elementAlgebra β₁).val.toLinearMap Subtype.val_injective
    let ev : elementAlgebra β₁ →ₗ[F] L :=
      ((Finsupp.lapply (R := L) (M := L) l₀).restrictScalars F ∘ₗ (w.repr.toLinearMap.restrictScalars F)) ∘ₗ
        (LinearMap.applyₗ (w l₀) ∘ₗ (elementAlgebra β₁).val.toLinearMap)
    have hinj : Function.Injective ev := by
      refine (injective_iff_map_eq_zero ev).mpr fun X hX0 => ?_
      by_contra hne
      have hXne : (X : Module.End F V) ≠ 0 := fun h => hne (Subtype.ext h)
      obtain ⟨s', hs', hs'1⟩ := exists_depth 𝓛 hϖ hXne
      have h := sub_entry_mem 𝓛 hϖ hnormal hw l₀ hcore₁ hs'
        (commute_matUnit_of_mem_elementAlgebra hβ₁ε X.2)
        (Algebra.commute_of_mem_adjoin_self X.2).symm
      have hev : w.repr ((X : Module.End F V) (w l₀)) l₀ = 0 := hX0
      rw [hev, map_zero, sub_zero] at h
      exact hs'1 h
    have hle := LinearMap.finrank_le_finrank_of_injective hinj
    rw [hL1] at hle
    have hbot : elementAlgebra β₁ = ⊥ := by
      apply Subalgebra.eq_bot_of_finrank_one
      have hpos : 0 < Module.finrank F (elementAlgebra β₁) := Module.finrank_pos
      omega
    have hβ₁bot : β₁ ∈ (⊥ : Subalgebra F (Module.End F V)) :=
      hbot ▸ Algebra.self_mem_adjoin_singleton F β₁
    obtain ⟨x, hx⟩ := Algebra.mem_bot.mp hβ₁bot
    have hγ : ((g⁻¹ : (Module.End F V)ˣ) : Module.End F V) * β₁ * g =
        algebraMap F (Module.End F V) x := by
      rw [← hx, ← Algebra.commutes, mul_assoc, Units.inv_mul, mul_one]
    rw [hγ]
    exact le_bot_iff.mp (Algebra.adjoin_le
      (Set.singleton_subset_iff.mpr (Subalgebra.algebraMap_mem _ x)))

end Construction

end Langlands.BushnellKutzko

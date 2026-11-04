import Mathlib.RingTheory.Ideal.KrullsHeightTheorem
import Mathlib.RingTheory.Ideal.GoingDown

/-! # A height inequality for special fibres of flat families -/

noncomputable section

namespace Langlands.GroupScheme.BorelFieldExtension

open Ideal

/-- If `f` is strictly monotone and every value of `f` lies strictly above `⊥`, then `f` raises
heights by at least one. -/
theorem height_add_one_le_of_strictMono {α β : Type*} [Preorder α] [Preorder β] [OrderBot β]
    (f : α → β) (hf : StrictMono f) (hbot : ∀ y, ⊥ < f y) (x : α) :
    Order.height x + 1 ≤ Order.height (f x) := by
  let g : WithBot α → β := fun w => WithBot.recBotCoe ⊥ f w
  have hg : StrictMono g := by
    intro a b hab
    induction a using WithBot.recBotCoe with
    | bot =>
      induction b using WithBot.recBotCoe with
      | bot => exact absurd hab (lt_irrefl _)
      | coe b => exact hbot b
    | coe a =>
      induction b using WithBot.recBotCoe with
      | bot => exact absurd hab (WithBot.not_lt_bot _)
      | coe b => exact hf (WithBot.coe_lt_coe.mp hab)
  have h := Order.height_le_height_apply_of_strictMono g hg (x : WithBot α)
  rw [Order.height_coe_withBot] at h
  exact h

/-- If `Q < P ≤ M` with `Q` and `M` prime, then the image of `M` in `D ⧸ Q` has height at
least one more than its image in `D ⧸ P`. -/
theorem height_map_quotient_add_one_le {D : Type*} [CommRing D] {Q P M : Ideal D}
    [Q.IsPrime] [M.IsPrime] (hQP : Q < P) (hPM : P ≤ M)
    [(M.map (Ideal.Quotient.mk P)).IsPrime] [(M.map (Ideal.Quotient.mk Q)).IsPrime] :
    (M.map (Ideal.Quotient.mk P)).height + 1 ≤ (M.map (Ideal.Quotient.mk Q)).height := by
  have hφ : Function.Surjective (Ideal.Quotient.factor hQP.le) :=
    Ideal.Quotient.factor_surjective hQP.le
  have hf : StrictMono (PrimeSpectrum.comap (Ideal.Quotient.factor hQP.le)) :=
    RingHom.strictMono_comap_of_surjective hφ
  have hfx : PrimeSpectrum.comap (Ideal.Quotient.factor hQP.le)
      ⟨M.map (Ideal.Quotient.mk P), inferInstance⟩ =
      ⟨M.map (Ideal.Quotient.mk Q), inferInstance⟩ := by
    ext y
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective y
    change Ideal.Quotient.factor hQP.le (Ideal.Quotient.mk Q y) ∈ M.map (Ideal.Quotient.mk P) ↔
      Ideal.Quotient.mk Q y ∈ M.map (Ideal.Quotient.mk Q)
    rw [Ideal.Quotient.factor_mk, Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective,
      Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective]
    constructor
    · rintro ⟨z, hz, hzy⟩
      refine ⟨y, ?_, rfl⟩
      have h : y - z ∈ P := by
        rw [← Ideal.Quotient.eq]
        exact hzy.symm
      have := M.add_mem (hPM h) hz
      simpa using this
    · rintro ⟨z, hz, hzy⟩
      refine ⟨y, ?_, rfl⟩
      have h : y - z ∈ Q := by
        rw [← Ideal.Quotient.eq]
        exact hzy.symm
      have := M.add_mem (hPM (hQP.le h)) hz
      simpa using this
  have hbot : ∀ y : PrimeSpectrum (D ⧸ P),
      (⊥ : PrimeSpectrum (D ⧸ Q)) < PrimeSpectrum.comap (Ideal.Quotient.factor hQP.le) y := by
    intro y
    refine lt_of_le_of_ne bot_le fun h => ?_
    obtain ⟨p, hp, hpQ⟩ := SetLike.exists_of_lt hQP
    have hmem : Ideal.Quotient.mk Q p ∈
        (PrimeSpectrum.comap (Ideal.Quotient.factor hQP.le) y).asIdeal := by
      change Ideal.Quotient.factor hQP.le (Ideal.Quotient.mk Q p) ∈ y.asIdeal
      rw [Ideal.Quotient.factor_mk, Ideal.Quotient.eq_zero_iff_mem.mpr hp]
      exact y.asIdeal.zero_mem
    rw [← h, PrimeSpectrum.asIdeal_bot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem] at hmem
    exact hpQ hmem
  have h := height_add_one_le_of_strictMono _ hf hbot ⟨M.map (Ideal.Quotient.mk P), inferInstance⟩
  rw [hfx, ← PrimeSpectrum.height_eq_orderHeight, ← PrimeSpectrum.height_eq_orderHeight] at h
  exact h

/-- Let `D` be a Noetherian algebra over a Noetherian ring `A`, let `Q < P ≤ M` be ideals of `D`
with `Q` and `M` prime, `M` lying over the prime `𝔪` of `A`, and `D ⧸ P` flat over `A`. Then
`M` is not minimal over `Q + 𝔪 D`. -/
theorem exists_isPrime_lt_of_flat {A D : Type*} [CommRing A] [CommRing D] [Algebra A D]
    [IsNoetherianRing A] [IsNoetherianRing D] (𝔪 : Ideal A) [𝔪.IsPrime]
    {Q P M : Ideal D} [Q.IsPrime] [M.IsPrime] (hQP : Q < P) (hPM : P ≤ M)
    (hM : M.comap (algebraMap A D) = 𝔪) [Module.Flat A (D ⧸ P)] :
    ∃ q : Ideal D, q.IsPrime ∧ Q ⊔ 𝔪.map (algebraMap A D) ≤ q ∧ q < M := by
  by_contra hcon
  have hQM : Q ≤ M := hQP.le.trans hPM
  -- the image of `M` in `D ⧸ Q`
  have hMQ : (M.map (Ideal.Quotient.mk Q)).IsPrime :=
    map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have hMP : (M.map (Ideal.Quotient.mk P)).IsPrime :=
    map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  set Mb := M.map (Ideal.Quotient.mk Q) with hMb
  have hcomapMb : Mb.comap (Ideal.Quotient.mk Q) = M := by
    rw [hMb, Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hQM]
  have hcomapMP : (M.map (Ideal.Quotient.mk P)).comap (Ideal.Quotient.mk P) = M := by
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hPM]
  -- lying over
  have hlo : Mb.LiesOver 𝔪 := by
    refine ⟨?_⟩
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq A D (D ⧸ Q), ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, hcomapMb, hM]
  have hloP : (M.map (Ideal.Quotient.mk P)).LiesOver 𝔪 := by
    refine ⟨?_⟩
    rw [Ideal.under_def, IsScalarTower.algebraMap_eq A D (D ⧸ P), ← Ideal.comap_comap,
      Ideal.Quotient.algebraMap_eq, hcomapMP, hM]
  -- Step 1: Krull's height theorem relative to `A`.
  have h1 := Ideal.height_le_height_add_of_liesOver 𝔪 Mb
  -- Step 2: the image of `Mb` in the fibre is a minimal prime.
  set 𝔪S := 𝔪.map (algebraMap A (D ⧸ Q)) with h𝔪S
  have h𝔪S_le : 𝔪S ≤ Mb := by
    rw [h𝔪S, Ideal.map_le_iff_le_comap, ← Ideal.under_def, ← Ideal.over_def Mb 𝔪]
  have hfib : (Mb.map (Ideal.Quotient.mk 𝔪S)).IsPrime :=
    map_isPrime_of_surjective Ideal.Quotient.mk_surjective (by rwa [Ideal.mk_ker])
  have h2 : (Mb.map (Ideal.Quotient.mk 𝔪S)).height = 0 := by
    rw [Ideal.height_eq_zero_iff]
    refine ⟨⟨hfib, bot_le⟩, fun J hJ hJle => ?_⟩
    have hJp : J.IsPrime := hJ.1
    let q : Ideal D := (J.comap (Ideal.Quotient.mk 𝔪S)).comap (Ideal.Quotient.mk Q)
    have hqp : q.IsPrime := by
      have : (J.comap (Ideal.Quotient.mk 𝔪S)).IsPrime := Ideal.comap_isPrime _ _
      exact Ideal.comap_isPrime _ _
    have hQq : Q ⊔ 𝔪.map (algebraMap A D) ≤ q := by
      refine sup_le ?_ ?_
      · intro y hy
        change Ideal.Quotient.mk 𝔪S (Ideal.Quotient.mk Q y) ∈ J
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr hy, map_zero]
        exact J.zero_mem
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change Ideal.Quotient.mk 𝔪S (Ideal.Quotient.mk Q (algebraMap A D a)) ∈ J
        have : Ideal.Quotient.mk Q (algebraMap A D a) ∈ 𝔪S := by
          rw [← Ideal.Quotient.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
          exact Ideal.mem_map_of_mem _ ha
        rw [Ideal.Quotient.eq_zero_iff_mem.mpr this]
        exact J.zero_mem
    have hqM : q ≤ M := by
      intro y hy
      have hy' : Ideal.Quotient.mk 𝔪S (Ideal.Quotient.mk Q y) ∈
          Mb.map (Ideal.Quotient.mk 𝔪S) := hJle hy
      rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hy'
      obtain ⟨z, hz, hzy⟩ := hy'
      have hd : Ideal.Quotient.mk Q y - z ∈ 𝔪S := by
        rw [← Ideal.Quotient.eq]
        exact hzy.symm
      have hmem : Ideal.Quotient.mk Q y ∈ Mb := by
        have := Mb.add_mem (h𝔪S_le hd) hz
        simpa using this
      rw [← hcomapMb]
      exact hmem
    have hqeq : q = M := by
      by_contra hne
      exact hcon ⟨q, hqp, hQq, lt_of_le_of_ne hqM hne⟩
    -- conclude `Mb.map (mk 𝔪S) ≤ J`
    intro w hw
    rw [Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective] at hw
    obtain ⟨v, hv, rfl⟩ := hw
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective v
    have hyM : y ∈ M := by
      rw [← hcomapMb]
      exact hv
    rw [← hqeq] at hyM
    exact hyM
  -- Step 3: going down for the flat quotient `D ⧸ P`.
  have h3 : 𝔪.height ≤ (M.map (Ideal.Quotient.mk P)).height := by
    rw [Ideal.height_eq_height_add_of_liesOver_of_hasGoingDown 𝔪 (M.map (Ideal.Quotient.mk P))]
    exact le_self_add
  -- Step 4: the chain inequality.
  have h4 := height_map_quotient_add_one_le (Q := Q) (P := P) (M := M) hQP hPM
  have hfin : 𝔪.height ≠ ⊤ := Ideal.height_ne_top_of_isPrime
  rw [h2, add_zero] at h1
  have : 𝔪.height + 1 ≤ 𝔪.height :=
    (by gcongr : 𝔪.height + 1 ≤ (M.map (Ideal.Quotient.mk P)).height + 1).trans (h4.trans h1)
  exact (ENat.add_one_le_iff hfin).mp this |>.ne rfl

end Langlands.GroupScheme.BorelFieldExtension

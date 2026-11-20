import Langlands.BushnellKutzko.RefinementCore

/-! # Elements commuting with a block-diagonal element

Let `L` be a field acting on `V` whose units normalize the chain, `w` a relative splitting basis
and `β₁` an element commuting with all matrix units `ε_{jk}` of `w`. Assume the core
approximation property: every `X ∈ 𝔓^t` commuting with `β₁` is congruent modulo `𝔓^{t+1}` to an
`L`-linear endomorphism. Then the generated algebra `F[β₁]` consists of normalizing units, the
`(l₀,l₀)` entry map `F[β₁] → L` is onto, and `F[β₁]` and `L` approximate each other.
-/

open ValuativeRel

noncomputable section

namespace Langlands.BushnellKutzko

universe uF uV uL

section Centralizer

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {V : Type uV} [AddCommGroup V] [Module F V]
  {L : Type uL} [Field L] [Algebra F L] [Module L V] [IsScalarTower F L V]
  (𝓛 : LatticeChain 𝒪[F] F V) {ϖ : 𝒪[F]} (hϖ : Irreducible ϖ)
  (hnormal : ∀ u : Lˣ, subfieldUnits F L V u ∈ 𝓛.stabilizer)
  {n : ℕ} {w : Module.Basis (Fin n) L V} (hw : RelSplits (L := L) 𝓛 w) (l₀ : Fin n)
  {β₁ : Module.End F V}
  (hcore : ∀ (t : ℤ) (X : Module.End F V), X ∈ 𝓛.endFiltration t → Commute X β₁ →
    ∃ γ, (∀ a : L, γ * subfieldEmbedding F L V a = subfieldEmbedding F L V a * γ) ∧
      X - γ ∈ 𝓛.endFiltration (t + 1))

local notation "P" => 𝓛.endFiltration
local notation "Lat" => 𝓛.lattice

include hϖ hnormal hw in
/-- The `(l,l)` entry of an element of `𝔓^s`, acting through `L`, lies in `𝔓^s`. -/
theorem entry_mem {s : ℤ} {X : Module.End F V} (hX : X ∈ P s) (l : Fin n) :
    subfieldEmbedding F L V (w.repr (X (w l)) l) ∈ P s := by
  have hl : w l ≠ 0 := w.ne_zero l
  rw [subfieldEmbedding_mem_iff 𝓛 hϖ hnormal hl]
  exact repr_smul_mem 𝓛 hw (hX _ _ (𝓛.mem_lattice_index hϖ hl)) l

include hϖ hnormal hw l₀ hcore in
/-- An element of `𝔓^s` commuting with the matrix units and with `β₁` is congruent modulo
`𝔓^{s+1}` to the action of its `(l₀,l₀)` entry. -/
theorem sub_entry_mem {s : ℤ} {X : Module.End F V} (hX : X ∈ P s)
    (hXε : ∀ j k, X * matUnit F w j k = matUnit F w j k * X) (hXβ : Commute X β₁) :
    X - subfieldEmbedding F L V (w.repr (X (w l₀)) l₀) ∈ P (s + 1) := by
  obtain ⟨γ, hγ, hXγ⟩ := hcore s X hX hXβ
  have h1 := diagonal_compress_mem 𝓛 hϖ hnormal hw hXγ l₀
  rw [compress_sub, map_sub, diagonal_compress_of_commute w l₀ hXε,
    compress_of_commute w l₀ hγ, diagonal_mulLeft] at h1
  have h2 := entry_mem 𝓛 hϖ hnormal hw hXγ l₀
  have heq : X - subfieldEmbedding F L V (w.repr (X (w l₀)) l₀) =
      (X - subfieldEmbedding F L V (w.repr (γ (w l₀)) l₀)) -
        subfieldEmbedding F L V (w.repr ((X - γ) (w l₀)) l₀) := by
    simp only [LinearMap.sub_apply, map_sub, Finsupp.sub_apply]
    abel
  rw [heq]
  exact sub_mem h1 h2

/-- If `X` has depth exactly `s` and `X ≡ Y (mod 𝔓^{s+1})`, then `Y ∈ 𝔓^t` forces `t ≤ s`. -/
theorem le_depth_of_sub_mem {s t : ℤ} {X Y : Module.End F V} (hs1 : X ∉ P (s + 1))
    (hXY : X - Y ∈ P (s + 1)) (hY : Y ∈ P t) : t ≤ s := by
  by_contra hts
  apply hs1
  have := add_mem hXY (𝓛.endFiltration_antitone (by omega) hY)
  rwa [sub_add_cancel] at this

include hϖ hnormal hw l₀ hcore in
/-- A nonzero element commuting with the matrix units and with `β₁` is a unit normalizing the
chain. -/
theorem exists_unit_of_commute {X : Module.End F V} (hX0 : X ≠ 0)
    (hXε : ∀ j k, X * matUnit F w j k = matUnit F w j k * X) (hXβ : Commute X β₁) :
    ∃ g : (Module.End F V)ˣ, (g : Module.End F V) = X ∧ g ∈ 𝓛.stabilizer := by
  obtain ⟨s, hs, hs1⟩ := exists_depth 𝓛 hϖ hX0
  obtain ⟨e, hXe⟩ : ∃ e : L, X - subfieldEmbedding F L V e ∈ P (s + 1) :=
    ⟨_, sub_entry_mem 𝓛 hϖ hnormal hw l₀ hcore hs hXε hXβ⟩
  have he0 : e ≠ 0 := by
    intro h0
    apply hs1
    rwa [h0, map_zero, sub_zero] at hXe
  obtain ⟨d, hd⟩ := refinement_scalar_lattice_shift 𝓛 hnormal he0
  have hes1 : subfieldEmbedding F L V e ∉ P (s + 1) := by
    intro h
    apply hs1
    have := add_mem hXe h
    rwa [sub_add_cancel] at this
  have hes : subfieldEmbedding F L V e ∈ P s := by
    have := sub_mem hs (𝓛.endFiltration_antitone (by omega) hXe)
    rwa [sub_sub_cancel] at this
  have hsd : s ≤ d := (subfieldEmbedding_mem_iff_le 𝓛 hd s).mp hes
  have hds : ¬ (s + 1 ≤ d) := fun h => hes1 ((subfieldEmbedding_mem_iff_le 𝓛 hd (s + 1)).mpr h)
  have hd' := inv_smul_lattice_shift 𝓛 he0 hd
  have hinv : subfieldEmbedding F L V e⁻¹ ∈ P (-s) :=
    (subfieldEmbedding_mem_iff_le 𝓛 hd' (-s)).mpr (by omega)
  have h1 : subfieldEmbedding F L V e⁻¹ * X - 1 ∈ P ((1 : ℕ) : ℤ) := by
    have heq : subfieldEmbedding F L V e⁻¹ * X - 1 =
        subfieldEmbedding F L V e⁻¹ * (X - subfieldEmbedding F L V e) := by
      rw [mul_sub, ← map_mul, inv_mul_cancel₀ he0, map_one]
    rw [heq]
    have := 𝓛.mul_mem_endFiltration hinv hXe
    rwa [show -s + (s + 1) = ((1 : ℕ) : ℤ) by push_cast; ring] at this
  obtain ⟨h, hh, hhv⟩ := 𝓛.exists_mem_unitFiltration le_rfl h1
  refine ⟨subfieldUnits F L V (Units.mk0 e he0) * h, ?_,
    𝓛.stabilizer.mul_mem (hnormal _) (mem_stabilizer_of_mem_unitFiltration 𝓛 hh)⟩
  rw [Units.val_mul, coe_subfieldUnits, hhv, Units.val_mk0, add_sub_cancel, ← mul_assoc,
    ← map_mul, mul_inv_cancel₀ he0, map_one, one_mul]

include hϖ hnormal hw l₀ hcore in
/-- Every nonzero element of `F[β₁]` is a unit normalizing the chain. -/
theorem normalizingUnits_elementAlgebra
    (hβε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁) :
    NormalizingUnits 𝓛 (elementAlgebra β₁) := by
  intro X hX hX0
  refine exists_unit_of_commute 𝓛 hϖ hnormal hw l₀ hcore hX0 (fun j k => ?_)
    (Algebra.commute_of_mem_adjoin_self hX).symm
  have hc : Commute (matUnit F w j k) β₁ := (hβε j k).symm
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hX hc).eq.symm

theorem commute_matUnit_of_mem_elementAlgebra
    (hβε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁) {X : Module.End F V}
    (hX : X ∈ elementAlgebra β₁) (j k : Fin n) :
    X * matUnit F w j k = matUnit F w j k * X := by
  have hc : Commute (matUnit F w j k) β₁ := (hβε j k).symm
  exact (Algebra.commute_of_mem_adjoin_singleton_of_commute hX hc).eq.symm

include hϖ hnormal hw l₀ hcore in
/-- The `(l₀,l₀)` entry map `F[β₁] → L` is onto. -/
theorem exists_mem_elementAlgebra_entry_eq
    (hβε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁) (a : L) :
    ∃ X ∈ elementAlgebra β₁, w.repr (X (w l₀)) l₀ = a := by
  classical
  haveI := 𝓛.finiteDimensional
  let x : Module.End F L := compress F w l₀ β₁
  have hΔx : diagonal F w x = β₁ := diagonal_compress_of_commute w l₀ hβε
  -- Every nonzero endomorphism of `L` commuting with `x` is injective.
  have hinj : ∀ p : Module.End F L, p ≠ 0 → Commute p x → Function.Injective p := by
    intro p hp hpx
    have hΔp0 : diagonal F w p ≠ 0 := fun h =>
      hp (diagonal_injective w l₀ (by rw [h, map_zero]))
    have hΔpβ : Commute (diagonal F w p) β₁ := by
      rw [← hΔx]
      exact hpx.map (diagonal F w)
    obtain ⟨g, hg, -⟩ := exists_unit_of_commute 𝓛 hϖ hnormal hw l₀ hcore hΔp0
      (fun j k => diagonal_commute_matUnit w p j k) hΔpβ
    have hu : IsUnit (diagonal F w p) := hg ▸ g.isUnit
    have hΔinj := ((Module.End.isUnit_iff _).mp hu).1
    rw [injective_iff_map_eq_zero]
    intro b hb
    have h1 : diagonal F w p (b • w l₀) = diagonal F w p 0 := by
      rw [diagonal_smul_basis, hb, zero_smul, map_zero]
    exact (smul_eq_zero.mp (hΔinj h1)).resolve_right (w.ne_zero l₀)
  haveI : FiniteDimensional F L :=
    Module.Finite.of_injective (lineIncl F w l₀) (fun b b' h => by
      simp only [lineIncl_apply] at h
      exact smul_left_injective L (w.ne_zero l₀) h)
  let K : Subalgebra F (Module.End F L) := Algebra.adjoin F {x}
  have hKcomm : ∀ q ∈ K, Commute q x := fun q hq =>
    (Algebra.commute_of_mem_adjoin_self hq).symm
  have hKfield : IsField K := isField_of_forall_ne_zero_isUnit K
    (fun q hq q' hq' => (Algebra.commute_of_mem_adjoin_singleton_of_commute hq'
      (hKcomm q hq)).eq)
    (fun q hq hq0 => (LinearMap.isUnit_iff_ker_eq_bot q).mpr
      (LinearMap.ker_eq_bot.mpr (hinj q hq0 (hKcomm q hq))))
  letI : Field K := hKfield.toField
  have hspan : Submodule.span K {(1 : L)} = ⊤ := by
    by_contra hne
    obtain ⟨f, hf0, hfle⟩ :=
      Submodule.exists_le_ker_of_lt_top _ (lt_top_iff_ne_top.mpr hne)
    let p : Module.End F L :=
      (LinearMap.applyₗ (1 : L)) ∘ₗ K.val.toLinearMap ∘ₗ f.restrictScalars F
    have hp_apply : ∀ b : L, p b = ((f b : K) : Module.End F L) 1 := fun b => rfl
    have hp1 : p 1 = 0 := by
      rw [hp_apply, hfle (Submodule.subset_span rfl)]
      rfl
    have hpx : Commute p x := by
      ext b
      rw [Module.End.mul_apply, Module.End.mul_apply, hp_apply, hp_apply]
      have hxb : x b = (⟨x, Algebra.self_mem_adjoin_singleton F x⟩ : K) • b := rfl
      rw [hxb, map_smul, smul_eq_mul, Subalgebra.coe_mul, Module.End.mul_apply]
    have hp0 : p ≠ 0 := by
      intro hp
      apply hf0
      refine LinearMap.ext fun b => ?_
      rw [LinearMap.zero_apply]
      by_contra hfb
      have hq := hinj _ (fun h => hfb (Subtype.ext h)) (hKcomm _ (f b).2)
      apply one_ne_zero (α := L)
      apply hq
      rw [map_zero]
      change p b = 0
      rw [hp]
      rfl
    exact one_ne_zero (α := L) (hinj p hp0 hpx (by rw [hp1, map_zero]))
  obtain ⟨q, hq⟩ := Submodule.mem_span_singleton.mp (hspan ▸ Submodule.mem_top : a ∈ _)
  refine ⟨diagonal F w q, ?_, ?_⟩
  · have hmem : diagonal F w q ∈ K.map (diagonal F w) := Subalgebra.mem_map.mpr ⟨q, q.2, rfl⟩
    rwa [AlgHom.map_adjoin_singleton, hΔx] at hmem
  · rw [← one_smul L (w l₀), diagonal_smul_basis, repr_smul_basis]
    simp only [↓reduceIte]
    exact hq

include hϖ hnormal hw l₀ hcore in
/-- `F[β₁]` is approximated by `L` at every level. -/
theorem approx_elementAlgebra_range
    (hβε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁) :
    Approx 𝓛 (elementAlgebra β₁ : Set (Module.End F V))
      (Set.range (subfieldEmbedding F L V)) := by
  intro X hX t hXt
  exact ⟨_, Set.mem_range_self _, sub_entry_mem 𝓛 hϖ hnormal hw l₀ hcore hXt
    (commute_matUnit_of_mem_elementAlgebra hβε hX) (Algebra.commute_of_mem_adjoin_self hX).symm⟩

include hϖ hnormal hw l₀ hcore in
/-- `L` is approximated by `F[β₁]` at every level. -/
theorem approx_range_elementAlgebra
    (hβε : ∀ j k, β₁ * matUnit F w j k = matUnit F w j k * β₁) :
    Approx 𝓛 (Set.range (subfieldEmbedding F L V))
      (elementAlgebra β₁ : Set (Module.End F V)) := by
  rintro _ ⟨e, rfl⟩ t het
  by_cases he : e = 0
  · refine ⟨0, Subalgebra.zero_mem _, ?_⟩
    rw [he, map_zero, sub_zero]
    exact zero_mem _
  obtain ⟨X, hX, hXe⟩ := exists_mem_elementAlgebra_entry_eq 𝓛 hϖ hnormal hw l₀ hcore hβε e
  have hX0 : X ≠ 0 := by
    rintro rfl
    apply he
    rw [← hXe]
    simp
  obtain ⟨s, hs, hs1⟩ := exists_depth 𝓛 hϖ hX0
  have h1 := sub_entry_mem 𝓛 hϖ hnormal hw l₀ hcore hs
    (commute_matUnit_of_mem_elementAlgebra hβε hX) (Algebra.commute_of_mem_adjoin_self hX).symm
  rw [hXe] at h1
  have hts := le_depth_of_sub_mem 𝓛 hs1 h1 het
  refine ⟨X, hX, ?_⟩
  rw [← neg_sub]
  exact neg_mem (𝓛.endFiltration_antitone (by omega) h1)

end Centralizer

end Langlands.BushnellKutzko

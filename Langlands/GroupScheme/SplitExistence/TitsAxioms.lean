import Langlands.GroupScheme.SplitExistence.SimpleDecomp
import Langlands.GroupScheme.SplitExistence.TitsTransfer

/-! # The Tits axioms for the Chevalley group over a field

For a reduced root datum, `(B, N, (n_i))` satisfies `IsConcreteTits` in `GL_n(K)`. The main
step is the axiom `n B m ⊆ B m B ∪ B n m B` (Steinberg, *Lectures on Chevalley groups*, §3,
Lemma 25), proved by cases on whether `m⁻¹ U_i m` is a positive or a negative root group; in
the negative case the rank-one identity rewrites `n_i x_i(a)` through `x_i(a⁻¹) T n_i`. -/

noncomputable section

universe u

open Matrix

namespace Langlands.GroupScheme.SplitExistence

namespace ChevalleyData

variable {J X Y : Type u} [AddCommGroup X] [AddCommGroup Y] {P : RootDatum J X Y} {b : P.Base}
  (D : ChevalleyData P b) {K : Type u} [Field K]

theorem posMinusSub_le_posSub (i : J) : D.posMinusSub K i ≤ D.posSub K :=
  rootsSub_mono fun _ hj => hj.1

theorem posSub_le_borelSub : D.posSub K ≤ D.borelSub K := le_sup_right

theorem torusSub_le_borelSub : D.torusSub K ≤ D.borelSub K := le_sup_left

theorem x_mem_borelSub {j : J} (hj : b.IsPos j) (s : K) : D.x j s ∈ D.borelSub K :=
  D.posSub_le_borelSub (rootSub_le_rootsSub (S := {j | b.IsPos j}) hj (x_mem_rootSub j s))

theorem wn_inv_conj_x (i : b.support) (j : J) : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ∀ s : K,
    (D.wn i)⁻¹ * D.x j s * D.wn i = D.x (P.reflectionPerm i j) ((ε : K) * s) := by
  obtain ⟨ε, hε, h⟩ := D.wn_conj_x (K := K) i (P.reflectionPerm i j)
  rw [RootPairing.reflectionPerm_self] at h
  have hεε : (ε : K) * ε = 1 := by
    rcases hε with rfl | rfl <;> norm_num
  refine ⟨ε, hε, fun s => ?_⟩
  have h' := h (ε * s)
  rw [← mul_assoc, hεε, one_mul] at h'
  rw [← h']
  group

variable [Finite J] [P.IsReduced]

omit [Finite J] [P.IsReduced] in
theorem ℓ_reflectionPerm_self (i : J) : D.ℓ (P.root (P.reflectionPerm i i)) = -D.ℓ (P.root i) := by
  rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg]

theorem reflectionPerm_mem_posMinus (i : b.support) {j : J} (hj : j ∈ posMinus (b := b) i) :
    P.reflectionPerm i j ∈ posMinus (b := b) i := by
  refine ⟨hj.1.reflectionPerm i.2 hj.2, fun h => ?_⟩
  have h' : j = P.reflectionPerm i i := by
    have := congrArg (P.reflectionPerm i) h
    rwa [RootPairing.reflectionPerm_self] at this
  have hpos' : b.IsPos (P.reflectionPerm i i) := h' ▸ hj.1
  let _ := P.indexNeg
  have hneg := (RootPairing.Base.IsPos.neg_iff_not (b := b) (i : J)).1 hpos'
  exact hneg (RootPairing.Base.isPos_of_mem_support i.2)

theorem wn_conj_mem_posMinusSub (i : b.support) {g : GL (Fin D.n) K}
    (hg : g ∈ D.posMinusSub K i) : D.wn i * g * (D.wn i)⁻¹ ∈ D.posMinusSub K i := by
  refine D.conj_mem_rootsSub (fun j hj => ⟨P.reflectionPerm i j, reflectionPerm_mem_posMinus i hj,
    fun s => ?_⟩) hg
  obtain ⟨ε, -, h⟩ := D.wn_conj_x (K := K) i j
  exact ⟨_, h s⟩

omit [Finite J] [P.IsReduced] in
theorem torus_conj_mem_posMinusSub (i : J) {t g : GL (Fin D.n) K} (ht : t ∈ D.torusSub K)
    (hg : g ∈ D.posMinusSub K i) : t * g * t⁻¹ ∈ D.posMinusSub K i :=
  (Subgroup.mem_normalizer_iff.1 (D.torusSub_le_normalizer _ ht) g).1 hg

/-- **Axiom T3.** For a representative `n = n_i t` of `s_i`, `m ∈ N` and `g ∈ B`,
`n g m ∈ B m B ∪ B (n m) B`. -/
theorem tits_mul_mem (i : b.support) {n : GL (Fin D.n) K} (hn : n ∈ D.weylSub K)
    (hn' : (D.wn i)⁻¹ * n ∈ D.borelSub K) {m : GL (Fin D.n) K} (hm : m ∈ D.weylSub K)
    {g : GL (Fin D.n) K} (hg : g ∈ D.borelSub K) :
    ∃ b₁ ∈ D.borelSub K, ∃ b₂ ∈ D.borelSub K,
      n * g * m = b₁ * m * b₂ ∨ n * g * m = b₁ * (n * m) * b₂ := by
  have hiPos : b.IsPos (i : J) := RootPairing.Base.isPos_of_mem_support i.2
  -- `n = n_i t` with `t` in the torus
  have htT : (D.wn i)⁻¹ * n ∈ D.torusSub K := by
    rw [← D.borelSub_inf_weylSub]
    exact ⟨hn', (D.weylSub K).mul_mem ((D.weylSub K).inv_mem (wn_mem_weylSub i)) hn⟩
  obtain ⟨χ, hχ⟩ := htT
  have hn_eq : n = D.wn i * D.torusHom χ := by rw [hχ]; group
  -- `g = u' t' x_i(a)`
  obtain ⟨u', hu', t', ht', a, rfl⟩ := D.exists_borel_decomp hiPos hg
  set β := n * u' * n⁻¹ * (n * t' * n⁻¹) with hβdef
  have hβ : β ∈ D.borelSub K := by
    refine (D.borelSub K).mul_mem ?_ (D.torusSub_le_borelSub
      (D.conj_mem_torusSub_of_mem_weylSub hn ht'))
    have h1 : D.torusHom χ * u' * (D.torusHom χ)⁻¹ ∈ D.posMinusSub K i :=
      D.torus_conj_mem_posMinusSub i (torusHom_mem_torusSub χ) hu'
    have h2 := D.wn_conj_mem_posMinusSub i h1
    have : n * u' * n⁻¹ = D.wn i * (D.torusHom χ * u' * (D.torusHom χ)⁻¹) * (D.wn i)⁻¹ := by
      rw [hn_eq]; group
    rw [this]
    exact D.posSub_le_borelSub (D.posMinusSub_le_posSub i h2)
  have key : n * (u' * t' * D.x i a) * m = β * (n * D.x i a * m) := by
    rw [hβdef]; group
  -- the root permutation of `m⁻¹`
  obtain ⟨w, hw⟩ := D.isRootPerm_of_mem_weylSub ((D.weylSub K).inv_mem hm)
  obtain ⟨j₁, hj₁, hs₁⟩ := hw i
  obtain ⟨j₂, hj₂, hs₂⟩ := hw (P.reflectionPerm i i)
  have hℓ₂ : D.ℓ (P.root j₂) = -D.ℓ (P.root j₁) := by
    rw [hj₂, hj₁, RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self, map_neg,
      map_neg]
  rw [key]
  rcases lt_or_gt_of_ne (D.ℓ_root_ne_zero j₁) with hneg | hpos
  · -- `m⁻¹ U_{-i} m` is a positive root group
    have hj₂pos : b.IsPos j₂ := (D.isPos_iff_ℓ_pos j₂).2 (by linarith)
    by_cases ha : a = 0
    · refine ⟨β, hβ, 1, (D.borelSub K).one_mem, Or.inr ?_⟩
      rw [ha, x_zero]
      group
    · obtain ⟨ε, hε, h1⟩ := D.wn_conj_x (K := K) i i
      have hεne : (ε : K) ≠ 0 := by rcases hε with rfl | rfl <;> norm_num
      set a' : K := ((χ (Multiplicative.ofAdd (P.root i)) : Kˣ) : K) * a with ha'
      have h7 : D.torusHom χ * D.x i a * (D.torusHom χ)⁻¹ = D.x i a' := D.torusHom_conj_x χ i a
      have ha'ne : a' ≠ 0 := mul_ne_zero (Units.ne_zero _) ha
      set U : Kˣ := Units.mk0 ((ε : K) * a') (mul_ne_zero hεne ha'ne) with hU
      have h2 := D.x_reflectionPerm_self i U
      have h3 := h1 ((U⁻¹ : Kˣ) : K)
      have h4 := D.wn_mul_self (K := K) i
      set τ := D.torusHom (corootChar (P := P) (i : J) (-U⁻¹)) with hτ
      set ψ := corootChar (P := P) (i : J) (-1 : Kˣ) * χ with hψ
      have hρ : D.torusHom (corootChar (P := P) (i : J) (-1)) * D.torusHom χ = D.torusHom ψ := by
        rw [hψ, map_mul]
      have h5 := D.torusHom_conj_x ψ⁻¹ (P.reflectionPerm i i) ((ε : K) * ((U⁻¹ : Kˣ) : K))
      have hinv : D.torusHom ψ⁻¹ = (D.torusHom ψ)⁻¹ := map_inv D.torusHom ψ
      rw [hinv, inv_inv] at h5
      obtain ⟨c'', hc''⟩ := hs₂ (((ψ⁻¹ (Multiplicative.ofAdd (P.root (P.reflectionPerm i i))) :
        Kˣ) : K) * ((ε : K) * ((U⁻¹ : Kˣ) : K)))
      rw [inv_inv] at hc''
      refine ⟨β * (D.x i ((U⁻¹ : Kˣ) : K) * τ * D.torusHom ψ), ?_, D.x j₂ c'',
        D.x_mem_borelSub hj₂pos c'', Or.inl ?_⟩
      · refine (D.borelSub K).mul_mem hβ ((D.borelSub K).mul_mem ((D.borelSub K).mul_mem
          (D.x_mem_borelSub hiPos _) (D.torusSub_le_borelSub (torusHom_mem_torusSub _)))
          (D.torusSub_le_borelSub (torusHom_mem_torusSub _)))
      · have hU' : ((U : Kˣ) : K) = (ε : K) * a' := rfl
        calc β * (n * D.x i a * m)
            = β * (D.wn i * (D.torusHom χ * D.x i a * (D.torusHom χ)⁻¹) * D.torusHom χ * m) := by
              rw [hn_eq]; group
          _ = β * ((D.wn i * D.x i a' * (D.wn i)⁻¹) * D.wn i * D.torusHom χ * m) := by
              rw [h7]; group
          _ = β * (D.x (P.reflectionPerm i i) (U : K) * D.wn i * D.torusHom χ * m) := by
              rw [h1 a', ← hU']
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ * D.wn i * D.x i ((U⁻¹ : Kˣ) : K) * D.wn i *
                D.torusHom χ * m) := by
              rw [h2]
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ *
                (D.wn i * D.x i ((U⁻¹ : Kˣ) : K) * (D.wn i)⁻¹) * (D.wn i * D.wn i) *
                D.torusHom χ * m) := by
              group
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ *
                D.x (P.reflectionPerm i i) ((ε : K) * ((U⁻¹ : Kˣ) : K)) *
                (D.torusHom (corootChar (P := P) (i : J) (-1)) * D.torusHom χ) * m) := by
              rw [h3, h4]; group
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ * D.torusHom ψ *
                ((D.torusHom ψ)⁻¹ * D.x (P.reflectionPerm i i) ((ε : K) * ((U⁻¹ : Kˣ) : K)) *
                  D.torusHom ψ) * m) := by
              rw [hρ]; group
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ * D.torusHom ψ) * m *
                (m⁻¹ * D.x (P.reflectionPerm i i) (((ψ⁻¹ (Multiplicative.ofAdd
                  (P.root (P.reflectionPerm i i))) : Kˣ) : K) * ((ε : K) * ((U⁻¹ : Kˣ) : K))) *
                  m) := by
              rw [h5]; group
          _ = β * (D.x i ((U⁻¹ : Kˣ) : K) * τ * D.torusHom ψ) * m * D.x j₂ c'' := by
              rw [hc'']
  · -- `m⁻¹ U_i m` is a positive root group
    have hj₁pos : b.IsPos j₁ := (D.isPos_iff_ℓ_pos j₁).2 hpos
    obtain ⟨s', hs'⟩ := hs₁ a
    rw [inv_inv] at hs'
    refine ⟨β, hβ, D.x j₁ s', D.x_mem_borelSub hj₁pos s', Or.inr ?_⟩
    rw [← hs']
    group

end ChevalleyData

end Langlands.GroupScheme.SplitExistence

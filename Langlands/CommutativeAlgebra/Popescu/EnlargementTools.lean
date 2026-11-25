import Langlands.Algebra.LocalFlatnessCriterion
import Langlands.MathlibBase

/-! # Tools for the unit enlargement of flat Artinian approximations -/

namespace Langlands.CommutativeAlgebra.Popescu

open TensorProduct IsLocalRing

namespace Enlargement

set_option linter.deprecated false in
/-- Let `D → D' → L` be local homomorphisms of Noetherian local rings with `𝔪_D D' = 𝔪_{D'}`.
If `L` is flat over `D`, then `L` is flat over `D'`. -/
theorem flat_of_map_maximalIdeal {D D' L : Type*} [CommRing D] [CommRing D'] [CommRing L]
    [IsLocalRing D] [IsLocalRing D'] [IsLocalRing L] [IsNoetherianRing D'] [IsNoetherianRing L]
    [Algebra D D'] [Algebra D' L] [Algebra D L] [IsScalarTower D D' L]
    [IsLocalHom (algebraMap D' L)] [Module.Flat D L]
    (hm : (maximalIdeal D).map (algebraMap D D') = maximalIdeal D') : Module.Flat D' L := by
  apply Langlands.Algebra.localFlatnessCriterion D' L L
  set I := maximalIdeal D
  set I' := maximalIdeal D'
  have hmem : ∀ i ∈ I, algebraMap D D' i ∈ I' := fun i hi => hm ▸ Ideal.mem_map_of_mem _ hi
  -- the comparison map `I ⊗_D L → I' ⊗_{D'} L`
  let β₀ : I →ₗ[D] L →ₗ[D] I' ⊗[D'] L :=
    { toFun := fun i =>
        { toFun := fun l => (⟨algebraMap D D' i, hmem i i.2⟩ : I') ⊗ₜ[D'] l
          map_add' := fun l l' => tmul_add _ _ _
          map_smul' := fun d l => by
            rw [RingHom.id_apply, ← IsScalarTower.algebraMap_smul D' d l, tmul_smul,
              algebraMap_smul] }
      map_add' := fun i i' => by
        ext l
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.add_apply, ← add_tmul]
        congr 1
        exact Subtype.ext (map_add _ _ _)
      map_smul' := fun d i => by
        ext l
        simp only [LinearMap.coe_mk, AddHom.coe_mk, LinearMap.smul_apply, RingHom.id_apply]
        rw [show (⟨algebraMap D D' ((d • i : I) : D), hmem _ (d • i).2⟩ : I') =
            algebraMap D D' d • (⟨algebraMap D D' i, hmem i i.2⟩ : I') from
            Subtype.ext (by simp [Algebra.smul_def]), smul_tmul', algebraMap_smul] }
  let β : I ⊗[D] L →ₗ[D] I' ⊗[D'] L := TensorProduct.lift β₀
  have hβ : ∀ (i : I) (l : L), β (i ⊗ₜ l) = (⟨algebraMap D D' i, hmem i i.2⟩ : I') ⊗ₜ[D'] l :=
    fun i l => TensorProduct.lift.tmul _ _
  -- `β` is surjective
  have hβs : Function.Surjective β := by
    intro x
    induction x using TensorProduct.induction_on with
    | zero => exact ⟨0, map_zero _⟩
    | tmul j l =>
      obtain ⟨j, hj⟩ := j
      have key : ∀ (j : D') (hj : j ∈ I'), ∀ l : L,
          (⟨j, hj⟩ : I') ⊗ₜ[D'] l ∈ LinearMap.range β := by
        intro j hj
        rw [← hm] at hj
        induction hj using Submodule.span_induction with
        | mem z hz =>
          obtain ⟨i, hi, rfl⟩ := hz
          intro l
          exact ⟨(⟨i, hi⟩ : I) ⊗ₜ l, hβ _ _⟩
        | zero =>
          intro l
          refine ⟨0, ?_⟩
          rw [map_zero]
          symm
          convert zero_tmul (R := D') I' l
        | add a b ha hb iha ihb =>
          intro l
          obtain ⟨u, hu⟩ := iha (hm ▸ ha) l
          obtain ⟨v, hv⟩ := ihb (hm ▸ hb) l
          refine ⟨u + v, ?_⟩
          rw [map_add, hu, hv, ← add_tmul]
          rfl
        | smul c a ha iha =>
          intro l
          obtain ⟨u, hu⟩ := iha (hm ▸ ha) (c • l)
          refine ⟨u, ?_⟩
          rw [hu]
          rw [show (⟨c • a, _⟩ : I') = c • (⟨a, hm ▸ ha⟩ : I') from rfl, smul_tmul]
      exact key j hj l
    | add x y hx hy =>
      obtain ⟨u, rfl⟩ := hx
      obtain ⟨v, rfl⟩ := hy
      exact ⟨u + v, map_add _ _ _⟩
  -- the comparison with the multiplication maps
  have hcomm : ∀ z : I ⊗[D] L,
      TensorProduct.lid D' L (LinearMap.rTensor L I'.subtype (β z)) =
        TensorProduct.lid D L (LinearMap.rTensor L I.subtype z) := by
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul i l =>
      rw [hβ]
      simp [Algebra.smul_def, IsScalarTower.algebraMap_apply D D' L]
    | add x y hx hy => simp only [map_add, hx, hy]
  have hinjD : Function.Injective (LinearMap.rTensor L I.subtype) :=
    Module.Flat.rTensor_preserves_injective_linearMap _ (Submodule.injective_subtype _)
  intro a b hab
  obtain ⟨a, rfl⟩ := hβs a
  obtain ⟨b, rfl⟩ := hβs b
  have : TensorProduct.lid D L (LinearMap.rTensor L I.subtype a) =
      TensorProduct.lid D L (LinearMap.rTensor L I.subtype b) := by
    rw [← hcomm, ← hcomm, hab]
  rw [hinjD ((TensorProduct.lid D L).injective this)]

/-- In a local ring of characteristic `p` with nilpotent maximal ideal, every element congruent to
`1` has a `p`-power equal to `1`. -/
theorem exists_pow_eq_one {L : Type*} [CommRing L] [IsLocalRing L] (p : ℕ) [Fact p.Prime]
    [CharP L p] (hnil : IsNilpotent (maximalIdeal L)) {u : L} (hu : u - 1 ∈ maximalIdeal L) :
    ∃ N : ℕ, u ^ (p ^ N) = 1 := by
  obtain ⟨K, hK⟩ := hnil
  have hn : (u - 1) ^ K = 0 := by
    have : (u - 1) ^ K ∈ maximalIdeal L ^ K := Ideal.pow_mem_pow hu K
    rwa [hK, Ideal.zero_eq_bot, Ideal.mem_bot] at this
  obtain ⟨N, hN⟩ : ∃ N, K ≤ p ^ N := ⟨K, (Nat.lt_pow_self (Fact.out : p.Prime).one_lt).le⟩
  refine ⟨N, ?_⟩
  have h1 : u = 1 + (u - 1) := by ring
  rw [h1, add_pow_char_pow, one_pow, ← Nat.sub_add_cancel hN, pow_add, hn, mul_zero, add_zero]

/-- If `ψ(x) ℓ ≡ 1` modulo the maximal ideal, then some `p`-power of `ℓ` lies in the image of the
local homomorphism `ψ`. -/
theorem exists_pow_mem_range {D L : Type*} [CommRing D] [CommRing L] [IsLocalRing D]
    [IsLocalRing L] (p : ℕ) [Fact p.Prime] [CharP L p] (hnil : IsNilpotent (maximalIdeal L))
    (ψ : D →+* L) [IsLocalHom ψ] {l : L} {x : D} (hx : ψ x * l - 1 ∈ maximalIdeal L) :
    ∃ N : ℕ, l ^ (p ^ N) ∈ Set.range ψ := by
  obtain ⟨N, hN⟩ := exists_pow_eq_one p hnil hx
  have hu : IsUnit (ψ x * l) := by
    by_contra h
    have h1 : ψ x * l ∈ maximalIdeal L := (IsLocalRing.mem_maximalIdeal _).mpr h
    have : (1 : L) ∈ maximalIdeal L := by
      have := (maximalIdeal L).sub_mem h1 hx
      simp at this
    exact (maximalIdeal.isMaximal L).ne_top ((Ideal.eq_top_iff_one _).mpr this)
  have hxu : IsUnit x := isUnit_of_map_unit ψ x (isUnit_of_mul_isUnit_left hu)
  refine ⟨N, ↑(hxu.unit⁻¹) ^ (p ^ N), ?_⟩
  rw [mul_pow] at hN
  rw [map_pow]
  have hψx : ψ ↑hxu.unit⁻¹ * ψ x = 1 := by
    rw [← map_mul, IsUnit.val_inv_mul, map_one]
  calc ψ ↑hxu.unit⁻¹ ^ p ^ N = ψ ↑hxu.unit⁻¹ ^ p ^ N * (ψ x ^ p ^ N * l ^ p ^ N) := by
        rw [hN, mul_one]
    _ = (ψ ↑hxu.unit⁻¹ * ψ x) ^ p ^ N * l ^ p ^ N := by ring
    _ = l ^ p ^ N := by rw [hψx, one_pow, one_mul]

/-- A local ring with nilpotent maximal ideal is adically complete. -/
theorem isAdicComplete_of_isNilpotent {R : Type*} [CommRing R] [IsLocalRing R]
    (h : IsNilpotent (maximalIdeal R)) : IsAdicComplete (maximalIdeal R) R := by
  obtain ⟨N, hN⟩ := h
  have hpow : ∀ n, N ≤ n → ((maximalIdeal R) ^ n • ⊤ : Submodule R R) = ⊥ := by
    intro n hn
    rw [Ideal.smul_top_eq_map, Algebra.algebraMap_self, Ideal.map_id,
      ← Nat.add_sub_cancel' hn, pow_add, hN, Ideal.zero_eq_bot, Ideal.bot_mul]
    rfl
  have h1 : IsHausdorff (maximalIdeal R) R := ⟨fun x hx => by
    have := hx N
    rw [hpow N le_rfl, SModEq.bot] at this
    exact this⟩
  have h2 : IsPrecomplete (maximalIdeal R) R := ⟨fun f hf => ⟨f N, fun n => by
    rcases le_total n N with hn | hn
    · exact hf hn
    · have := hf hn
      rw [hpow N le_rfl, SModEq.bot] at this
      rw [this]⟩⟩
  exact {}

/-- The maximal ideal of an Artinian local ring is nilpotent. -/
theorem isNilpotent_maximalIdeal (R : Type*) [CommRing R] [IsLocalRing R] [IsArtinianRing R] :
    IsNilpotent (maximalIdeal R) := by
  have := IsArtinianRing.isNilpotent_jacobson_bot (R := R)
  rwa [IsLocalRing.jacobson_eq_maximalIdeal ⊥ bot_ne_top] at this

open KaehlerDifferential in
/-- A differential basis is preserved by a formally étale extension of fields. -/
theorem kaehler_basis_of_formallyEtale {k F F' : Type*} [Field k] [Field F] [Field F']
    [Algebra k F] [Algebra k F'] [Algebra F F'] [IsScalarTower k F F']
    [Algebra.FormallyEtale F F'] {ι : Type*} (x : ι → F)
    (hli : LinearIndependent F (fun i => D k F (x i)))
    (hsp : Submodule.span F (Set.range fun i => D k F (x i)) = ⊤) :
    LinearIndependent F' (fun i => D k F' (algebraMap F F' (x i))) ∧
      Submodule.span F' (Set.range fun i => D k F' (algebraMap F F' (x i))) = ⊤ := by
  let b := Module.Basis.mk hli hsp.ge
  let b' := (b.baseChange F').map (tensorKaehlerEquivOfFormallyEtale k F F')
  have hb' : ∀ i, b' i = D k F' (algebraMap F F' (x i)) := by
    intro i
    simp [b', b, Module.Basis.baseChange_apply, mapBaseChange_tmul]
  have h1 : (fun i => D k F' (algebraMap F F' (x i))) = ⇑b' := funext fun i => (hb' i).symm
  rw [h1]
  exact ⟨b'.linearIndependent, b'.span_eq⟩


/-- A `p`-th power has zero differential in characteristic `p`. -/
theorem D_pow_char {k F : Type*} [Field k] [Field F] [Algebra k F] (p : ℕ) [CharP F p] (x : F) :
    KaehlerDifferential.D k F (x ^ p) = 0 := by
  rw [Derivation.leibniz_pow, ← Nat.cast_smul_eq_nsmul F, CharP.cast_eq_zero, zero_smul]

/-- If `ψ(x) ≡ ℓ^e` modulo `𝔪_L` (`e > 0`), then some power `ℓ^Q`, `Q > 0`, is `ψ(w^p)`. -/
theorem exists_pth_power_preimage {D' L : Type*} [CommRing D'] [CommRing L] [IsLocalRing D']
    [IsLocalRing L] (p : ℕ) [Fact p.Prime] [CharP L p] (hnil : IsNilpotent (maximalIdeal L))
    (ψ : D' →+* L) [IsLocalHom ψ] {ℓ : L} (hℓ : IsUnit ℓ) {x : D'} {e : ℕ} (he : 0 < e)
    (hx : ψ x - ℓ ^ e ∈ maximalIdeal L) :
    ∃ (Q : ℕ) (w : D'), 0 < Q ∧ ψ (w ^ p) = ℓ ^ Q := by
  let l : L := ↑((hℓ.unit ^ e)⁻¹)
  have hl : ℓ ^ e * l = 1 := by
    show ↑(hℓ.unit) ^ e * ↑((hℓ.unit ^ e)⁻¹) = (1 : L)
    rw [← Units.val_pow_eq_pow_val, Units.mul_inv]
  have hx' : ψ x * l - 1 ∈ maximalIdeal L := by
    have : ψ x * l - 1 = (ψ x - ℓ ^ e) * l := by rw [sub_mul, hl]
    rw [this]
    exact Ideal.mul_mem_right _ _ hx
  obtain ⟨N, y, hy⟩ := exists_pow_mem_range p hnil ψ hx'
  have hyu : IsUnit y := by
    apply isUnit_of_map_unit ψ
    rw [hy]
    exact (Units.isUnit _).pow _
  let w : D' := ↑(hyu.unit⁻¹)
  have hw : ψ w = ℓ ^ (e * p ^ N) := by
    have h1 : ψ w * ψ y = 1 := by
      rw [← map_mul]
      show ψ (↑(hyu.unit⁻¹) * ↑hyu.unit) = 1
      rw [Units.inv_mul, map_one]
    have h2 : ψ y * ℓ ^ (e * p ^ N) = 1 := by
      rw [hy, pow_mul, ← mul_pow, mul_comm, hl, one_pow]
    calc ψ w = ψ w * (ψ y * ℓ ^ (e * p ^ N)) := by rw [h2, mul_one]
      _ = (ψ w * ψ y) * ℓ ^ (e * p ^ N) := by ring
      _ = ℓ ^ (e * p ^ N) := by rw [h1, one_mul]
  refine ⟨e * p ^ N * p, w, ?_, ?_⟩
  · exact Nat.mul_pos (Nat.mul_pos he (pow_pos (Fact.out : p.Prime).pos _))
      (Fact.out : p.Prime).pos
  · rw [map_pow, hw, ← pow_mul]

end Enlargement

end Langlands.CommutativeAlgebra.Popescu

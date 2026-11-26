import Langlands.BushnellKutzko.LatticeChainLayerCommutation

/-! # Intertwining layer families along the orbits of two shifting units

Let `(L_i)` be a lattice chain of period `e`, let `P` be a stabilizer unit of shift `e` and let
`B₁`, `B₂` be stabilizer units of shift `-n`, each commuting with `P`. Put `g = gcd(e, n)` and
`Y_j = P^{n/g} B_j^{e/g}`, a unit of shift zero. The translates of a layer index `r` under the
monomials `P^a B_j^c` are the indices congruent to `r` modulo `g`.

`exists_layer_intertwiner` takes automorphisms `ψ_r` of the layers `L_r / L_{r+1}` with
`ψ_r ∘ Y₂ = Y₁ ∘ ψ_r` and transports `ψ_r` for `0 ≤ r < g` along the orbits: on the layer of
index `r + a e - c n` it puts `(P^a B₁^c) ∘ ψ_r ∘ (P^a B₂^c)⁻¹`. The result does not depend on the
chosen exponents (`orbitConj_eq`), commutes with `P` and intertwines `B₂` with `B₁`.
`exists_unitFiltration_conj_sub_mem` lifts such a family, for `P` a base uniformizer, to a unit
`u ∈ U(𝔄)` with `u⁻¹ B₁ u ≡ B₂` modulo `𝔓^{1-n}`.

This is the layer form of the normal form argument of Bushnell–Kutzko (1993), (2.5.11),
printed pp. 82–83, as used in the first case of the proof of (2.6.1), printed pp. 83–84.
-/

noncomputable section

namespace Langlands.BushnellKutzko

/-- Products of powers of two commuting elements multiply exponentwise. -/
theorem zpow_mul_zpow_add {G : Type*} [Group G] {P B : G} (hc : Commute P B) (a c a' c' : ℤ) :
    P ^ (a + a') * B ^ (c + c') = (P ^ a * B ^ c) * (P ^ a' * B ^ c') := by
  rw [zpow_add, zpow_add]
  have h := (hc.zpow_zpow a' c).eq
  simp only [mul_assoc]
  rw [← mul_assoc (P ^ a') (B ^ c) (B ^ c'), h, mul_assoc]

/-! ### Orbit representatives -/

/-- With `g = gcd(e, n)` and `e > 0`, every integer is `r + (a e - c n)` with `0 ≤ r < g`. -/
theorem exists_orbitRep {e : ℤ} (n : ℤ) (he : 0 < e) (i : ℤ) :
    ∃ r a c : ℤ, 0 ≤ r ∧ r < (Int.gcd e n : ℤ) ∧ i = r + (a * e - c * n) := by
  have hg : (0 : ℤ) < Int.gcd e n := by
    exact_mod_cast Int.gcd_pos_of_ne_zero_left n he.ne'
  refine ⟨i % (Int.gcd e n : ℤ), (i / (Int.gcd e n : ℤ)) * Int.gcdA e n,
    -((i / (Int.gcd e n : ℤ)) * Int.gcdB e n), Int.emod_nonneg _ hg.ne',
    Int.emod_lt_of_pos _ hg, ?_⟩
  have h1 := Int.gcd_eq_gcd_ab e n
  have h2 := Int.emod_add_mul_ediv i (Int.gcd e n : ℤ)
  linear_combination -h2 + (i / (Int.gcd e n : ℤ)) * h1

/-- The residue `r` in `exists_orbitRep` is unique, and the exponents `(a, c)` are unique up to
adding multiples of `(n / g, e / g)`. -/
theorem orbitRep_unique {e n : ℤ} (he : 0 < e) {r r' a a' c c' : ℤ}
    (hr : 0 ≤ r) (hr' : r < (Int.gcd e n : ℤ)) (hs : 0 ≤ r') (hs' : r' < (Int.gcd e n : ℤ))
    (h : r + (a * e - c * n) = r' + (a' * e - c' * n)) :
    r = r' ∧ ∃ k : ℤ, a = a' + k * (n / (Int.gcd e n : ℤ)) ∧
      c = c' + k * (e / (Int.gcd e n : ℤ)) := by
  set g : ℤ := (Int.gcd e n : ℤ) with hgdef
  have hg : 0 < g := Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_left n he.ne')
  obtain ⟨e', he'⟩ : g ∣ e := Int.gcd_dvd_left e n
  obtain ⟨n', hn'⟩ : g ∣ n := Int.gcd_dvd_right e n
  have hediv : e / g = e' := by rw [he', Int.mul_ediv_cancel_left _ hg.ne']
  have hndiv : n / g = n' := by rw [hn', Int.mul_ediv_cancel_left _ hg.ne']
  rw [hediv, hndiv]
  have hrr : r = r' := by
    have hd : g ∣ r - r' := ⟨(a' - a) * e' - (c' - c) * n', by
      linear_combination h + (a' - a) * he' + (c - c') * hn'⟩
    have hmod : r % g = r' % g :=
      Int.emod_eq_emod_iff_emod_sub_eq_zero.mpr (Int.emod_eq_zero_of_dvd hd)
    rwa [Int.emod_eq_of_lt hr hr', Int.emod_eq_of_lt hs hs'] at hmod
  refine ⟨hrr, ?_⟩
  subst hrr
  have hcop : Int.gcd e' n' = 1 := by
    have := Int.gcd_ediv_gcd_ediv_gcd_of_ne_zero_left (n := e) (m := n) he.ne'
    rwa [← hgdef, hediv, hndiv] at this
  have he'pos : 0 < e' := by
    by_contra hneg
    replace hneg := not_lt.mp hneg
    have : e ≤ 0 := by rw [he']; exact mul_nonpos_of_nonneg_of_nonpos hg.le hneg
    omega
  have hlin : (a - a') * e' = (c - c') * n' := by
    have h3 : g * ((a - a') * e') = g * ((c - c') * n') := by
      linear_combination h - (a - a') * he' + (c - c') * hn'
    exact mul_left_cancel₀ hg.ne' h3
  have hdvd : e' ∣ (c - c') * n' := ⟨a - a', by rw [← hlin]; ring⟩
  obtain ⟨k, hk⟩ := Int.dvd_of_dvd_mul_left_of_gcd_one hdvd hcop
  refine ⟨k, ?_, by linear_combination hk⟩
  have : e' * (a - a') = e' * (k * n') := by
    linear_combination hlin + n' * hk
  have := mul_left_cancel₀ he'pos.ne' this
  linear_combination this

namespace LatticeChain

universe uO uK uV

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K]
  [Algebra O K] [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  (𝓛 : LatticeChain O K V)

/-- The stabilizer valuation as a homomorphism to `Multiplicative ℤ`. -/
def stabilizerValuationHom : 𝓛.stabilizer →* Multiplicative ℤ where
  toFun g := Multiplicative.ofAdd (𝓛.stabilizerValuation g)
  map_one' := by simp
  map_mul' g h := by rw [𝓛.stabilizerValuation_mul]; rfl

/-- The shift of an integer power. -/
theorem stabilizerValuation_zpow (g : 𝓛.stabilizer) (k : ℤ) :
    𝓛.stabilizerValuation (g ^ k) = k * 𝓛.stabilizerValuation g := by
  have h := map_zpow (𝓛.stabilizerValuationHom) g k
  change Multiplicative.ofAdd (𝓛.stabilizerValuation (g ^ k)) =
    (Multiplicative.ofAdd (𝓛.stabilizerValuation g)) ^ k at h
  rw [← ofAdd_zsmul] at h
  exact (Multiplicative.ofAdd.injective h).trans (smul_eq_mul _ _)

/-- Equal units have equal layer maps. -/
theorem stabilizerLayerEquiv_congr {g g' : 𝓛.stabilizer} (hgg : g = g') {i j : ℤ}
    (h : j = i + 𝓛.stabilizerValuation g) (h' : j = i + 𝓛.stabilizerValuation g')
    (q : 𝓛.Layer i) :
    𝓛.stabilizerLayerEquiv g i j h q = 𝓛.stabilizerLayerEquiv g' i j h' q := by
  subst hgg
  rfl

/-! ### Powers of shift-zero units -/

/-- If `ψ` intertwines the layer maps of two shift-zero units, it intertwines those of all their
integer powers. -/
theorem layerEquiv_zpow_intertwine {r : ℤ} (ψ : 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r)
    (Y₁ Y₂ : 𝓛.stabilizer) (hY₁ : 𝓛.stabilizerValuation Y₁ = 0)
    (hY₂ : 𝓛.stabilizerValuation Y₂ = 0)
    (hψ : ∀ (h₁ : r = r + 𝓛.stabilizerValuation Y₁) (h₂ : r = r + 𝓛.stabilizerValuation Y₂)
      (q : 𝓛.Layer r), ψ (𝓛.stabilizerLayerEquiv Y₂ r r h₂ q) =
        𝓛.stabilizerLayerEquiv Y₁ r r h₁ (ψ q))
    (k : ℤ) (h₁ : r = r + 𝓛.stabilizerValuation (Y₁ ^ k))
    (h₂ : r = r + 𝓛.stabilizerValuation (Y₂ ^ k)) (q : 𝓛.Layer r) :
    ψ (𝓛.stabilizerLayerEquiv (Y₂ ^ k) r r h₂ q) =
      𝓛.stabilizerLayerEquiv (Y₁ ^ k) r r h₁ (ψ q) := by
  have hz : ∀ (Y : 𝓛.stabilizer), 𝓛.stabilizerValuation Y = 0 → ∀ m : ℤ,
      r = r + 𝓛.stabilizerValuation (Y ^ m) := by
    intro Y hY m
    rw [𝓛.stabilizerValuation_zpow, hY, mul_zero, add_zero]
  have hY₁' : r = r + 𝓛.stabilizerValuation Y₁ := by rw [hY₁, add_zero]
  have hY₂' : r = r + 𝓛.stabilizerValuation Y₂ := by rw [hY₂, add_zero]
  have hinv : ∀ (Y : 𝓛.stabilizer), 𝓛.stabilizerValuation Y = 0 →
      r = r + 𝓛.stabilizerValuation Y⁻¹ := by
    intro Y hY
    rw [𝓛.stabilizerValuation_inv, hY, neg_zero, add_zero]
  induction k using Int.induction_on generalizing q with
  | zero =>
    have h1 : r = r + 𝓛.stabilizerValuation (1 : 𝓛.stabilizer) := by
      rw [𝓛.stabilizerValuation_one, add_zero]
    rw [𝓛.stabilizerLayerEquiv_congr (zpow_zero Y₂) h₂ h1,
      𝓛.stabilizerLayerEquiv_congr (zpow_zero Y₁) h₁ h1,
      𝓛.stabilizerLayerEquiv_one_apply, 𝓛.stabilizerLayerEquiv_one_apply]
  | succ k ih =>
    have hk₁ := hz Y₁ hY₁ k
    have hk₂ := hz Y₂ hY₂ k
    have hm₁ : r = r + 𝓛.stabilizerValuation (Y₁ ^ (k : ℤ) * Y₁) := by
      rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, hY₁]; ring
    have hm₂ : r = r + 𝓛.stabilizerValuation (Y₂ ^ (k : ℤ) * Y₂) := by
      rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, hY₂]; ring
    rw [𝓛.stabilizerLayerEquiv_congr (zpow_add_one Y₂ (k : ℤ)) h₂ hm₂,
      𝓛.stabilizerLayerEquiv_mul_apply (Y₂ ^ (k : ℤ)) Y₂ hY₂' hk₂ hm₂, ih hk₁ hk₂,
      hψ hY₁' hY₂', 𝓛.stabilizerLayerEquiv_congr (zpow_add_one Y₁ (k : ℤ)) h₁ hm₁,
      𝓛.stabilizerLayerEquiv_mul_apply (Y₁ ^ (k : ℤ)) Y₁ hY₁' hk₁ hm₁]
  | pred k ih =>
    have hk₁ := hz Y₁ hY₁ (-(k : ℤ))
    have hk₂ := hz Y₂ hY₂ (-(k : ℤ))
    have hm₁ : r = r + 𝓛.stabilizerValuation (Y₁ ^ (-(k : ℤ)) * Y₁⁻¹) := by
      rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, 𝓛.stabilizerValuation_inv,
        hY₁]; ring
    have hm₂ : r = r + 𝓛.stabilizerValuation (Y₂ ^ (-(k : ℤ)) * Y₂⁻¹) := by
      rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, 𝓛.stabilizerValuation_inv,
        hY₂]; ring
    rw [𝓛.stabilizerLayerEquiv_congr (zpow_sub_one Y₂ (-(k : ℤ))) h₂ hm₂,
      𝓛.stabilizerLayerEquiv_mul_apply (Y₂ ^ (-(k : ℤ))) Y₂⁻¹ (hinv Y₂ hY₂) hk₂ hm₂,
      ih hk₁ hk₂, 𝓛.stabilizerLayerEquiv_congr (zpow_sub_one Y₁ (-(k : ℤ))) h₁ hm₁,
      𝓛.stabilizerLayerEquiv_mul_apply (Y₁ ^ (-(k : ℤ))) Y₁⁻¹ (hinv Y₁ hY₁) hk₁ hm₁]
    congr 1
    have key : ψ q = 𝓛.stabilizerLayerEquiv Y₁ r r hY₁'
        (ψ (𝓛.stabilizerLayerEquiv Y₂⁻¹ r r (hinv Y₂ hY₂) q)) := by
      have h := hψ hY₁' hY₂' (𝓛.stabilizerLayerEquiv Y₂⁻¹ r r (hinv Y₂ hY₂) q)
      rwa [𝓛.stabilizerLayerEquiv_cancel_apply Y₂ Y₂⁻¹ (mul_inv_cancel Y₂) (hinv Y₂ hY₂)
        hY₂'] at h
    rw [key, 𝓛.stabilizerLayerEquiv_cancel_apply Y₁⁻¹ Y₁ (inv_mul_cancel Y₁) hY₁'
      (hinv Y₁ hY₁)]

/-! ### Transport along the orbits -/

section Orbit

variable {𝓛}

/-- The automorphism `ψ_r` of the layer `L_r / L_{r+1}`, transported to the layer `L_i / L_{i+1}`:
first by the inverse of `P^a B₂^c`, then by `P^a B₁^c`. -/
def orbitConj (P B₁ B₂ : 𝓛.stabilizer) (ψ : ∀ r : ℤ, 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r)
    (r a c i : ℤ) (h₁ : i = r + 𝓛.stabilizerValuation (P ^ a * B₁ ^ c))
    (h₂ : i = r + 𝓛.stabilizerValuation (P ^ a * B₂ ^ c)) : 𝓛.Layer i ≃ₗ[O] 𝓛.Layer i :=
  (𝓛.stabilizerLayerEquiv (P ^ a * B₂ ^ c) r i h₂).symm ≪≫ₗ
    (ψ r ≪≫ₗ 𝓛.stabilizerLayerEquiv (P ^ a * B₁ ^ c) r i h₁)

/-- The value of the transported automorphism. -/
theorem orbitConj_apply (P B₁ B₂ : 𝓛.stabilizer) (ψ : ∀ r : ℤ, 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r)
    (r a c i : ℤ) (h₁ : i = r + 𝓛.stabilizerValuation (P ^ a * B₁ ^ c))
    (h₂ : i = r + 𝓛.stabilizerValuation (P ^ a * B₂ ^ c)) (q : 𝓛.Layer i) :
    orbitConj P B₁ B₂ ψ r a c i h₁ h₂ q =
      𝓛.stabilizerLayerEquiv (P ^ a * B₁ ^ c) r i h₁
        (ψ r ((𝓛.stabilizerLayerEquiv (P ^ a * B₂ ^ c) r i h₂).symm q)) :=
  rfl

/-- Transport by a further monomial `P^{a₀} B^{c₀}`. -/
theorem orbitConj_transport {P B₁ B₂ : 𝓛.stabilizer} (hc₁ : Commute P B₁) (hc₂ : Commute P B₂)
    (ψ : ∀ r : ℤ, 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r) {r a c i i' : ℤ} (a₀ c₀ : ℤ)
    (h₁ : i = r + 𝓛.stabilizerValuation (P ^ a * B₁ ^ c))
    (h₂ : i = r + 𝓛.stabilizerValuation (P ^ a * B₂ ^ c))
    (h₁' : i' = r + 𝓛.stabilizerValuation (P ^ (a₀ + a) * B₁ ^ (c₀ + c)))
    (h₂' : i' = r + 𝓛.stabilizerValuation (P ^ (a₀ + a) * B₂ ^ (c₀ + c)))
    (k₁ : i' = i + 𝓛.stabilizerValuation (P ^ a₀ * B₁ ^ c₀))
    (k₂ : i' = i + 𝓛.stabilizerValuation (P ^ a₀ * B₂ ^ c₀)) (q : 𝓛.Layer i) :
    orbitConj P B₁ B₂ ψ r (a₀ + a) (c₀ + c) i' h₁' h₂'
        (𝓛.stabilizerLayerEquiv (P ^ a₀ * B₂ ^ c₀) i i' k₂ q) =
      𝓛.stabilizerLayerEquiv (P ^ a₀ * B₁ ^ c₀) i i' k₁ (orbitConj P B₁ B₂ ψ r a c i h₁ h₂ q) := by
  have hm₁ : i' = r + 𝓛.stabilizerValuation ((P ^ a₀ * B₁ ^ c₀) * (P ^ a * B₁ ^ c)) := by
    rw [𝓛.stabilizerValuation_mul]; omega
  have hm₂ : i' = r + 𝓛.stabilizerValuation ((P ^ a₀ * B₂ ^ c₀) * (P ^ a * B₂ ^ c)) := by
    rw [𝓛.stabilizerValuation_mul]; omega
  set x := (𝓛.stabilizerLayerEquiv (P ^ a * B₂ ^ c) r i h₂).symm q with hx
  have hsymm : (𝓛.stabilizerLayerEquiv (P ^ (a₀ + a) * B₂ ^ (c₀ + c)) r i' h₂').symm
      (𝓛.stabilizerLayerEquiv (P ^ a₀ * B₂ ^ c₀) i i' k₂ q) = x := by
    rw [LinearEquiv.symm_apply_eq,
      𝓛.stabilizerLayerEquiv_congr (zpow_mul_zpow_add hc₂ a₀ c₀ a c) h₂' hm₂,
      𝓛.stabilizerLayerEquiv_mul_apply _ _ h₂ k₂ hm₂, hx, LinearEquiv.apply_symm_apply]
  rw [orbitConj_apply, orbitConj_apply, hsymm, ← hx,
    𝓛.stabilizerLayerEquiv_congr (zpow_mul_zpow_add hc₁ a₀ c₀ a c) h₁' hm₁,
    𝓛.stabilizerLayerEquiv_mul_apply _ _ h₁ k₁ hm₁]

variable {P B₁ B₂ : 𝓛.stabilizer} {e n : ℤ}

/-- The shift of the monomial `P^a B^c`. -/
theorem stabilizerValuation_monomial (hP : 𝓛.stabilizerValuation P = e) {B : 𝓛.stabilizer}
    (hB : 𝓛.stabilizerValuation B = -n) (a c : ℤ) :
    𝓛.stabilizerValuation (P ^ a * B ^ c) = a * e - c * n := by
  rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, 𝓛.stabilizerValuation_zpow, hP, hB]
  ring

/-- The unit `P^{n/g} B^{e/g}` has shift zero. -/
theorem stabilizerValuation_orbitUnit (hP : 𝓛.stabilizerValuation P = e) {B : 𝓛.stabilizer}
    (hB : 𝓛.stabilizerValuation B = -n) (he : 0 < e) :
    𝓛.stabilizerValuation (P ^ (n / (Int.gcd e n : ℤ)) * B ^ (e / (Int.gcd e n : ℤ))) = 0 := by
  rw [stabilizerValuation_monomial hP hB]
  have hg : (0 : ℤ) < Int.gcd e n := Int.natCast_pos.mpr (Int.gcd_pos_of_ne_zero_left n he.ne')
  obtain ⟨e', he'⟩ := Int.gcd_dvd_left e n
  obtain ⟨n', hn'⟩ := Int.gcd_dvd_right e n
  have h1 : e / (Int.gcd e n : ℤ) = e' := Int.ediv_eq_of_eq_mul_right hg.ne' he'
  have h2 : n / (Int.gcd e n : ℤ) = n' := Int.ediv_eq_of_eq_mul_right hg.ne' hn'
  rw [h1, h2]
  linear_combination n' * he' - e' * hn'

/-- Moving the exponents by `k (n/g, e/g)` multiplies the monomial by `(P^{n/g} B^{e/g})^k`. -/
theorem monomial_orbit_zpow {B : 𝓛.stabilizer} (hc : Commute P B) (a c k : ℤ) :
    P ^ (a + k * (n / (Int.gcd e n : ℤ))) * B ^ (c + k * (e / (Int.gcd e n : ℤ))) =
      (P ^ a * B ^ c) * (P ^ (n / (Int.gcd e n : ℤ)) * B ^ (e / (Int.gcd e n : ℤ))) ^ k := by
  rw [zpow_mul_zpow_add hc, ((hc.zpow_zpow _ _).mul_zpow k), ← zpow_mul, ← zpow_mul,
    mul_comm k, mul_comm k]

/-- The transported automorphism does not depend on the representative of the layer index. -/
theorem orbitConj_eq (hP : 𝓛.stabilizerValuation P = e) (hB₁ : 𝓛.stabilizerValuation B₁ = -n)
    (hB₂ : 𝓛.stabilizerValuation B₂ = -n) (hc₁ : Commute P B₁) (hc₂ : Commute P B₂)
    (he : 0 < e) (ψ : ∀ r : ℤ, 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r)
    (hψ : ∀ (r : ℤ)
      (h₁ : r = r + 𝓛.stabilizerValuation
        (P ^ (n / (Int.gcd e n : ℤ)) * B₁ ^ (e / (Int.gcd e n : ℤ))))
      (h₂ : r = r + 𝓛.stabilizerValuation
        (P ^ (n / (Int.gcd e n : ℤ)) * B₂ ^ (e / (Int.gcd e n : ℤ))))
      (q : 𝓛.Layer r),
      ψ r (𝓛.stabilizerLayerEquiv _ r r h₂ q) = 𝓛.stabilizerLayerEquiv _ r r h₁ (ψ r q))
    {r a c r' a' c' i : ℤ} (hr : 0 ≤ r) (hr' : r < (Int.gcd e n : ℤ))
    (hs : 0 ≤ r') (hs' : r' < (Int.gcd e n : ℤ))
    (h₁ : i = r + 𝓛.stabilizerValuation (P ^ a * B₁ ^ c))
    (h₂ : i = r + 𝓛.stabilizerValuation (P ^ a * B₂ ^ c))
    (h₁' : i = r' + 𝓛.stabilizerValuation (P ^ a' * B₁ ^ c'))
    (h₂' : i = r' + 𝓛.stabilizerValuation (P ^ a' * B₂ ^ c')) :
    orbitConj P B₁ B₂ ψ r a c i h₁ h₂ = orbitConj P B₁ B₂ ψ r' a' c' i h₁' h₂' := by
  have heq : r + (a * e - c * n) = r' + (a' * e - c' * n) := by
    rw [← stabilizerValuation_monomial hP hB₁, ← stabilizerValuation_monomial hP hB₁, ← h₁, ← h₁']
  obtain ⟨rfl, k, rfl, rfl⟩ := orbitRep_unique he hr hr' hs hs' heq
  set Y₁ := P ^ (n / (Int.gcd e n : ℤ)) * B₁ ^ (e / (Int.gcd e n : ℤ)) with hY₁def
  set Y₂ := P ^ (n / (Int.gcd e n : ℤ)) * B₂ ^ (e / (Int.gcd e n : ℤ)) with hY₂def
  have hY₁ : 𝓛.stabilizerValuation Y₁ = 0 := stabilizerValuation_orbitUnit hP hB₁ he
  have hY₂ : 𝓛.stabilizerValuation Y₂ = 0 := stabilizerValuation_orbitUnit hP hB₂ he
  have hYk₁ : r = r + 𝓛.stabilizerValuation (Y₁ ^ k) := by
    rw [𝓛.stabilizerValuation_zpow, hY₁, mul_zero, add_zero]
  have hYk₂ : r = r + 𝓛.stabilizerValuation (Y₂ ^ k) := by
    rw [𝓛.stabilizerValuation_zpow, hY₂, mul_zero, add_zero]
  have hm₁ : i = r + 𝓛.stabilizerValuation ((P ^ a' * B₁ ^ c') * Y₁ ^ k) := by
    rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, hY₁, mul_zero, add_zero]
    exact h₁'
  have hm₂ : i = r + 𝓛.stabilizerValuation ((P ^ a' * B₂ ^ c') * Y₂ ^ k) := by
    rw [𝓛.stabilizerValuation_mul, 𝓛.stabilizerValuation_zpow, hY₂, mul_zero, add_zero]
    exact h₂'
  apply LinearEquiv.ext
  intro q
  set q₀ := (𝓛.stabilizerLayerEquiv (P ^ a' * B₂ ^ c') r i h₂').symm q with hq₀
  set q₁ := (𝓛.stabilizerLayerEquiv (Y₂ ^ k) r r hYk₂).symm q₀ with hq₁
  have hsymm : (𝓛.stabilizerLayerEquiv
      (P ^ (a' + k * (n / (Int.gcd e n : ℤ))) * B₂ ^ (c' + k * (e / (Int.gcd e n : ℤ)))) r i
        h₂).symm
      q = q₁ := by
    rw [LinearEquiv.symm_apply_eq, 𝓛.stabilizerLayerEquiv_congr (monomial_orbit_zpow hc₂ a' c' k)
      h₂ hm₂, 𝓛.stabilizerLayerEquiv_mul_apply _ _ hYk₂ h₂' hm₂, hq₁,
      LinearEquiv.apply_symm_apply, hq₀, LinearEquiv.apply_symm_apply]
  have hpow := layerEquiv_zpow_intertwine 𝓛 (ψ r) Y₁ Y₂ hY₁ hY₂ (hψ r) k hYk₁ hYk₂ q₁
  rw [orbitConj_apply, orbitConj_apply, hsymm,
    𝓛.stabilizerLayerEquiv_congr (monomial_orbit_zpow hc₁ a' c' k) h₁ hm₁,
    𝓛.stabilizerLayerEquiv_mul_apply _ _ hYk₁ h₁' hm₁, ← hpow, hq₁,
    LinearEquiv.apply_symm_apply]

/-- Automorphisms `ψ_r` of the layers which intertwine the shift-zero units
`P^{n/g} B₂^{e/g}` and `P^{n/g} B₁^{e/g}`, with `g = gcd(e, n)`, extend to a family of layer
automorphisms which commutes with `P` and intertwines `B₂` with `B₁`. -/
theorem exists_layer_intertwiner (hP : 𝓛.stabilizerValuation P = e)
    (hB₁ : 𝓛.stabilizerValuation B₁ = -n) (hB₂ : 𝓛.stabilizerValuation B₂ = -n)
    (hc₁ : Commute P B₁) (hc₂ : Commute P B₂) (he : 0 < e)
    (ψ : ∀ r : ℤ, 𝓛.Layer r ≃ₗ[O] 𝓛.Layer r)
    (hψ : ∀ (r : ℤ)
      (h₁ : r = r + 𝓛.stabilizerValuation
        (P ^ (n / (Int.gcd e n : ℤ)) * B₁ ^ (e / (Int.gcd e n : ℤ))))
      (h₂ : r = r + 𝓛.stabilizerValuation
        (P ^ (n / (Int.gcd e n : ℤ)) * B₂ ^ (e / (Int.gcd e n : ℤ))))
      (q : 𝓛.Layer r),
      ψ r (𝓛.stabilizerLayerEquiv _ r r h₂ q) = 𝓛.stabilizerLayerEquiv _ r r h₁ (ψ r q)) :
    ∃ φ : ∀ i : ℤ, 𝓛.Layer i ≃ₗ[O] 𝓛.Layer i,
      (∀ (i j : ℤ) (h : j = i + 𝓛.stabilizerValuation P) (q : 𝓛.Layer i),
        𝓛.stabilizerLayerEquiv P i j h (φ i q) = φ j (𝓛.stabilizerLayerEquiv P i j h q)) ∧
      (∀ (i j : ℤ) (h₁ : j = i + 𝓛.stabilizerValuation B₁)
        (h₂ : j = i + 𝓛.stabilizerValuation B₂) (q : 𝓛.Layer i),
        𝓛.stabilizerLayerEquiv B₁ i j h₁ (φ i q) = φ j (𝓛.stabilizerLayerEquiv B₂ i j h₂ q)) := by
  choose R A C hR0 hRg hRi using fun i => exists_orbitRep n he i
  have hrep₁ : ∀ i, i = R i + 𝓛.stabilizerValuation (P ^ A i * B₁ ^ C i) := fun i => by
    rw [stabilizerValuation_monomial hP hB₁]
    exact hRi i
  have hrep₂ : ∀ i, i = R i + 𝓛.stabilizerValuation (P ^ A i * B₂ ^ C i) := fun i => by
    rw [stabilizerValuation_monomial hP hB₂]
    exact hRi i
  let φ : ∀ i, 𝓛.Layer i ≃ₗ[O] 𝓛.Layer i := fun i =>
    orbitConj P B₁ B₂ ψ (R i) (A i) (C i) i (hrep₁ i) (hrep₂ i)
  have key : ∀ (a₀ c₀ i j : ℤ) (k₁ : j = i + 𝓛.stabilizerValuation (P ^ a₀ * B₁ ^ c₀))
      (k₂ : j = i + 𝓛.stabilizerValuation (P ^ a₀ * B₂ ^ c₀)) (q : 𝓛.Layer i),
      φ j (𝓛.stabilizerLayerEquiv (P ^ a₀ * B₂ ^ c₀) i j k₂ q) =
        𝓛.stabilizerLayerEquiv (P ^ a₀ * B₁ ^ c₀) i j k₁ (φ i q) := by
    intro a₀ c₀ i j k₁ k₂ q
    have k₁' := k₁
    rw [stabilizerValuation_monomial hP hB₁] at k₁'
    have h₁' : j = R i + 𝓛.stabilizerValuation (P ^ (a₀ + A i) * B₁ ^ (c₀ + C i)) := by
      rw [stabilizerValuation_monomial hP hB₁]
      linear_combination k₁' + hRi i
    have h₂' : j = R i + 𝓛.stabilizerValuation (P ^ (a₀ + A i) * B₂ ^ (c₀ + C i)) := by
      rw [stabilizerValuation_monomial hP hB₂]
      linear_combination k₁' + hRi i
    have hwd : φ j = orbitConj P B₁ B₂ ψ (R i) (a₀ + A i) (c₀ + C i) j h₁' h₂' :=
      orbitConj_eq hP hB₁ hB₂ hc₁ hc₂ he ψ hψ (hR0 j) (hRg j) (hR0 i) (hRg i) _ _ _ _
    rw [hwd]
    exact orbitConj_transport hc₁ hc₂ ψ a₀ c₀ (hrep₁ i) (hrep₂ i) h₁' h₂' k₁ k₂ q
  refine ⟨φ, ?_, ?_⟩
  · intro i j h q
    have hP1 : ∀ B : 𝓛.stabilizer, P ^ (1 : ℤ) * B ^ (0 : ℤ) = P := fun B => by simp
    have k₁ : j = i + 𝓛.stabilizerValuation (P ^ (1 : ℤ) * B₁ ^ (0 : ℤ)) := by
      rw [hP1]; exact h
    have k₂ : j = i + 𝓛.stabilizerValuation (P ^ (1 : ℤ) * B₂ ^ (0 : ℤ)) := by
      rw [hP1]; exact h
    rw [𝓛.stabilizerLayerEquiv_congr (hP1 B₁).symm h k₁,
      𝓛.stabilizerLayerEquiv_congr (hP1 B₂).symm h k₂]
    exact (key 1 0 i j k₁ k₂ q).symm
  · intro i j h₁ h₂ q
    have hB1 : ∀ B : 𝓛.stabilizer, P ^ (0 : ℤ) * B ^ (1 : ℤ) = B := fun B => by simp
    have k₁ : j = i + 𝓛.stabilizerValuation (P ^ (0 : ℤ) * B₁ ^ (1 : ℤ)) := by
      rw [hB1]; exact h₁
    have k₂ : j = i + 𝓛.stabilizerValuation (P ^ (0 : ℤ) * B₂ ^ (1 : ℤ)) := by
      rw [hB1]; exact h₂
    rw [𝓛.stabilizerLayerEquiv_congr (hB1 B₁).symm h₁ k₁,
      𝓛.stabilizerLayerEquiv_congr (hB1 B₂).symm h₂ k₂]
    exact (key 0 1 i j k₁ k₂ q).symm

end Orbit

/-! ### Lifting an intertwining family to a unit of the order -/

/-- The layer action of a product is the composite of the layer actions. -/
theorem layerAction_mul (x y : 𝓛.order) (i : ℤ) :
    𝓛.layerAction (x * y) i = 𝓛.layerAction x i ∘ₗ 𝓛.layerAction y i := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rfl

/-- The identity acts as the identity on each layer. -/
theorem layerAction_one (i : ℤ) : 𝓛.layerAction 1 i = LinearMap.id := by
  apply LinearMap.ext
  intro q
  obtain ⟨v, hv, rfl⟩ := 𝓛.intervalMk_surjective i (i + 1) q
  rfl

section Lift

variable [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K]

/-- A family of layer automorphisms which commutes with a base uniformizer and intertwines the
layer maps of `B₂` with those of `B₁` lifts to `u ∈ U(𝔄)` with `u⁻¹ B₁ u ≡ B₂` modulo
`𝔓^{1-n}`, where `B₁` and `B₂` shift the chain by `-n`. -/
theorem exists_unitFiltration_conj_sub_mem {π : O} (hπ : Irreducible π)
    {B₁ B₂ : 𝓛.stabilizer} {n : ℤ}
    (hB₁ : 𝓛.stabilizerValuation B₁ = -n) (hB₂ : 𝓛.stabilizerValuation B₂ = -n)
    (φ : ∀ i : ℤ, 𝓛.Layer i ≃ₗ[O] 𝓛.Layer i)
    (hφP : ∀ (i j : ℤ) (h : j = i + 𝓛.stabilizerValuation (𝓛.uniformizerStabilizer hπ))
      (q : 𝓛.Layer i), 𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h (φ i q) =
        φ j (𝓛.stabilizerLayerEquiv (𝓛.uniformizerStabilizer hπ) i j h q))
    (hφB : ∀ (i j : ℤ) (h₁ : j = i + 𝓛.stabilizerValuation B₁)
      (h₂ : j = i + 𝓛.stabilizerValuation B₂) (q : 𝓛.Layer i),
      𝓛.stabilizerLayerEquiv B₁ i j h₁ (φ i q) = φ j (𝓛.stabilizerLayerEquiv B₂ i j h₂ q)) :
    ∃ u ∈ 𝓛.unitFiltration 0,
      ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) * ((B₁ : (Module.End K V)ˣ) : Module.End K V) *
        (u : Module.End K V) - ((B₂ : (Module.End K V)ˣ) : Module.End K V) ∈
          𝓛.endFiltration (1 - n) := by
  let D : ∀ i : ℤ, Module.End O (𝓛.Layer i) := fun i => (φ i).toLinearMap
  let D' : ∀ i : ℤ, Module.End O (𝓛.Layer i) := fun i => (φ i).symm.toLinearMap
  have hD : 𝓛.LayerFamilyCommutes D (𝓛.uniformizerStabilizer hπ) := fun i j h q => hφP i j h q
  have hD' : 𝓛.LayerFamilyCommutes D' (𝓛.uniformizerStabilizer hπ) := by
    intro i j h q
    change 𝓛.stabilizerLayerEquiv _ i j h ((φ i).symm q) =
      (φ j).symm (𝓛.stabilizerLayerEquiv _ i j h q)
    rw [LinearEquiv.eq_symm_apply, ← hφP i j h, LinearEquiv.apply_symm_apply]
  obtain ⟨x, hx⟩ := 𝓛.exists_order_lift_layers hπ D hD
  obtain ⟨x', hx'⟩ := 𝓛.exists_order_lift_layers hπ D' hD'
  have hxx' : x.val * x'.val - 1 ∈ 𝓛.endFiltration 1 := by
    have h := (𝓛.layerAction_eq_iff (x * x') 1).mp (fun i => by
      rw [layerAction_mul, hx, hx', layerAction_one]
      apply LinearMap.ext
      intro q
      exact (φ i).apply_symm_apply q)
    simpa using h
  have hx'x : x'.val * x.val - 1 ∈ 𝓛.endFiltration 1 := by
    have h := (𝓛.layerAction_eq_iff (x' * x) 1).mp (fun i => by
      rw [layerAction_mul, hx, hx', layerAction_one]
      apply LinearMap.ext
      intro q
      exact (φ i).symm_apply_apply q)
    simpa using h
  obtain ⟨h₁, hh₁, hh₁v⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl hxx'
  obtain ⟨h₂, hh₂, hh₂v⟩ := 𝓛.exists_mem_unitFiltration (n := 1) le_rfl hx'x
  have hh₁v' : (h₁ : Module.End K V) = x.val * x'.val := by rw [hh₁v]; abel
  have hh₂v' : (h₂ : Module.End K V) = x'.val * x.val := by rw [hh₂v]; abel
  set y : Module.End K V := x'.val * ((h₁⁻¹ : (Module.End K V)ˣ) : Module.End K V) with hy
  have hr : x.val * y = 1 := by
    rw [hy, ← mul_assoc, ← hh₁v', Units.mul_inv]
  have hl' : ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * x.val = 1 := by
    rw [mul_assoc, ← hh₂v', Units.inv_mul]
  have hyeq : y = ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val := by
    calc y = (((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * x.val) * y := by
          rw [hl', one_mul]
      _ = ((h₂⁻¹ : (Module.End K V)ˣ) : Module.End K V) * x'.val * (x.val * y) := by
          simp only [mul_assoc]
      _ = _ := by rw [hr, mul_one]
  have hl : y * x.val = 1 := by rw [hyeq, hl']
  let u : (Module.End K V)ˣ := ⟨x.val, y, hr, hl⟩
  have hyO : y ∈ 𝓛.order := mul_mem x'.prop hh₁.2.1
  refine ⟨u, (𝓛.mem_unitFiltration_zero).mpr ⟨x.prop, hyO⟩, ?_⟩
  have hcomm : ((B₁ : (Module.End K V)ˣ) : Module.End K V) * x.val -
      x.val * ((B₂ : (Module.End K V)ˣ) : Module.End K V) ∈ 𝓛.endFiltration (1 - n) := by
    intro i v hv
    have hj₁ : i - n = i + 𝓛.stabilizerValuation B₁ := by rw [hB₁]; ring
    have hj₂ : i - n = i + 𝓛.stabilizerValuation B₂ := by rw [hB₂]; ring
    have hxv : x.val v ∈ 𝓛.lattice i := (𝓛.mem_order.mp x.prop) i v hv
    have hB₂v : ((B₂ : (Module.End K V)ˣ) : Module.End K V) v ∈ 𝓛.lattice (i - n) := by
      rw [hj₂]
      exact (𝓛.mem_lattice_stabilizer_iff B₂ i v).mpr hv
    have hx₀ := LinearMap.congr_fun (hx i) (𝓛.intervalMk i (i + 1) v hv)
    have hx₁ := LinearMap.congr_fun (hx (i - n))
      (𝓛.intervalMk (i - n) (i - n + 1) _ hB₂v)
    rw [layerAction_mk] at hx₀ hx₁
    have h := hφB i (i - n) hj₁ hj₂ (𝓛.intervalMk i (i + 1) v hv)
    change 𝓛.stabilizerLayerEquiv B₁ i (i - n) hj₁ (D i (𝓛.intervalMk i (i + 1) v hv)) =
      D (i - n) (𝓛.stabilizerLayerEquiv B₂ i (i - n) hj₂ (𝓛.intervalMk i (i + 1) v hv)) at h
    rw [← hx₀, stabilizerLayerEquiv_mk, stabilizerLayerEquiv_mk, ← hx₁,
      intervalMk_eq_iff] at h
    rw [show i + (1 - n) = i - n + 1 by ring]
    simpa only [LinearMap.sub_apply, Module.End.mul_apply] using h
  have hexpr : ((u⁻¹ : (Module.End K V)ˣ) : Module.End K V) *
      ((B₁ : (Module.End K V)ˣ) : Module.End K V) * (u : Module.End K V) -
        ((B₂ : (Module.End K V)ˣ) : Module.End K V) =
      y * (((B₁ : (Module.End K V)ˣ) : Module.End K V) * x.val -
        x.val * ((B₂ : (Module.End K V)ˣ) : Module.End K V)) := by
    change y * _ * x.val - _ = _
    rw [mul_sub, ← mul_assoc y x.val, hl, one_mul, mul_assoc]
  rw [hexpr, show (1 - n : ℤ) = 0 + (1 - n) by ring]
  exact 𝓛.mul_mem_endFiltration ((𝓛.mem_order_iff_mem_endFiltration).mp hyO) hcomm

end Lift

end LatticeChain

end Langlands.BushnellKutzko

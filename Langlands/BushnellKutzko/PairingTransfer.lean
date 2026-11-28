import Langlands.BushnellKutzko.DiagonalSplitTypeRefinement
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

/-! # Transfer of non-vanishing by a commutator pairing

A form of the transfer step of the proof of Bushnell–Kutzko (8.2.5)(iv) in which the
conjugating elements normalize `K` and the conjugate characters differ from `ϑ` by a
character of the conjugating group. -/

noncomputable section

open scoped BigOperators

namespace Langlands.Jacquet

universe uG uV uZ uX

variable {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V]

open BushnellKutzko.SplitBlocks

/-- **Transfer by an additive family of conjugations.** Let `Z` be a finite additive group,
`g : Z → G` elements normalizing `K` (in both directions) with `g_q⁻¹ M g_q ⊆ M`, and
`Φ_k ∈ Ẑ` for `k ∈ K` with `ϑ(g_q k g_q⁻¹) Φ_k(q) = ϑ(k)`, where `Φ_k` is trivial exactly for
`k ∈ 𝒦`. Then a vector outside `rel(M)` on which `K ∩ 𝒦` acts through `ϑ` gives a vector
outside `rel(M)` on which `K` acts through `ϑ`. -/
theorem exists_isotypic_not_mem_relations_of_addChar (ρ : Representation ℂ G V)
    {K 𝒦 : Subgroup G} [Fintype (K ⧸ 𝒦.subgroupOf K)] (M : Subgroup G) (ϑ : K →* ℂˣ)
    {Z : Type uZ} [AddCommGroup Z] [Fintype Z] (g : Z → G) (Φ : K → AddChar Z ℂ)
    (hgK : ∀ q, ∀ k ∈ K, g q * k * (g q)⁻¹ ∈ K) (hgK' : ∀ q, ∀ k ∈ K, (g q)⁻¹ * k * g q ∈ K)
    (hratio : ∀ q (k : K), (ϑ ⟨_, hgK q k k.2⟩ : ℂ) * Φ k q = ϑ k)
    (hrad : ∀ k : K, Φ k = 0 ↔ (k : G) ∈ 𝒦)
    (hgM : ∀ q, ∀ m ∈ M, (g q)⁻¹ * m * (g q)⁻¹⁻¹ ∈ M)
    {v : V} (hv : ∀ κ : K, (κ : G) ∈ 𝒦 → ρ κ v = (ϑ κ : ℂ) • v)
    (hvM : v ∉ relations ρ M) :
    ∃ w : V, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ relations ρ M := by
  classical
  have : Nonempty Z := ⟨0⟩
  let χ : Z → K →* ℂˣ := fun q => ϑ.comp (conjEndo K (g q) (hgK q))
  have hχ : ∀ q (k : K), (χ q k : ℂ) * Φ k q = ϑ k := fun q k => hratio q k
  have hΦne : ∀ (k : K) (q : Z), Φ k q ≠ 0 := fun k q h => by
    have := (Φ k).map_add_eq_mul q (-q)
    rw [add_neg_cancel, AddChar.map_zero_eq_one, h, zero_mul] at this
    exact one_ne_zero this
  have hfac : ∀ (q : Z) (k : K),
      (((χ q k)⁻¹ : ℂˣ) : ℂ) = Φ k q * (((ϑ k)⁻¹ : ℂˣ) : ℂ) := by
    intro q k
    rw [Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, ← hχ q k]
    have h0 : (χ q k : ℂ) ≠ 0 := Units.ne_zero _
    have h1 := hΦne k q
    field_simp
  refine exists_isotypic_not_mem_relations M ϑ χ g ?_ ?_ ?_ hgM hv hvM
  · intro q k hk
    apply Units.ext
    have h1 : Φ k q = 1 := by rw [(hrad k).mpr hk, AddChar.zero_apply]
    rw [← hχ q k, h1, mul_one]
  · intro k
    rw [Finset.sum_congr rfl (fun q _ => hfac q k), ← Finset.sum_mul, AddChar.sum_eq_ite]
    by_cases hk : (k : G) ∈ 𝒦
    · simp only [show Φ k = 0 from (hrad k).mpr hk, hk, ↓reduceIte]
    · simp only [show ¬ Φ k = 0 from fun h => hk ((hrad k).mp h), hk, ↓reduceIte, zero_mul]
  · intro q w hw k
    set k' : K := ⟨(g q)⁻¹ * k * g q, hgK' q k k.2⟩ with hk'
    have hck : conjEndo K (g q) (hgK q) k' = k := by
      apply Subtype.ext
      rw [conjEndo_val, hk']
      group
    calc ρ k (ρ (g q) w) = ρ (g q) (ρ k' w) := by
          rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, hk']
          congr 2
          group
      _ = (ϑ k : ℂ) • ρ (g q) w := by
          rw [hw k', map_smul]
          congr 2
          simp only [χ, MonoidHom.comp_apply, hck]

/-- The inverse conjugation ratio descends to an additive character when the original
character is fixed on the kernel of the quotient map. -/
def quotientConjRatio {K : Subgroup G} {Y : Type uZ} [AddCommGroup Y]
    (ϑ : K →* ℂˣ) (p : K →* Multiplicative Y) (hp : Function.Surjective p)
    {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hfix : ∀ k : K, p k = 1 → ϑ (conjEndo K g hg k) = ϑ k) : AddChar Y ℂ :=
  let ratio : K →* ℂˣ := ϑ / (ϑ.comp (conjEndo K g hg))
  have hker : p.ker ≤ ratio.ker := by
    intro k hk
    simp [ratio, hfix k (MonoidHom.mem_ker.mp hk)]
  AddChar.toMonoidHomEquiv.symm
    ((Units.coeHom ℂ).comp (p.liftOfSurjective hp ⟨ratio, hker⟩))

theorem quotientConjRatio_apply {K : Subgroup G} {Y : Type uZ} [AddCommGroup Y]
    (ϑ : K →* ℂˣ) (p : K →* Multiplicative Y) (hp : Function.Surjective p)
    {g : G} (hg : ∀ k ∈ K, g * k * g⁻¹ ∈ K)
    (hfix : ∀ k : K, p k = 1 → ϑ (conjEndo K g hg k) = ϑ k) (k : K) :
    quotientConjRatio ϑ p hp hg hfix (p k).toAdd =
      ((ϑ k / ϑ (conjEndo K g hg k) : ℂˣ) : ℂ) := by
  simp [quotientConjRatio]

/-- If conjugation acts trivially on the quotient, the descended ratios form an
additive family of characters of that quotient. -/
def quotientConjRatios {K : Subgroup G} {Y : Type uZ} [AddCommGroup Y]
    {X : Type uX} [AddCommGroup X] (ϑ : K →* ℂˣ)
    (p : K →* Multiplicative Y) (hp : Function.Surjective p) (g : Multiplicative X →* G)
    (hg : ∀ x : X, ∀ k ∈ K, g (.ofAdd x) * k * (g (.ofAdd x))⁻¹ ∈ K)
    (hpconj : ∀ (x : X) (k : K), p (conjEndo K (g (.ofAdd x)) (hg x) k) = p k)
    (hfix : ∀ (x : X) (k : K), p k = 1 →
      ϑ (conjEndo K (g (.ofAdd x)) (hg x) k) = ϑ k) : X →+ AddChar Y ℂ where
  toFun x := quotientConjRatio ϑ p hp (hg x) (hfix x)
  map_zero' := by
    ext y
    obtain ⟨k, hk⟩ := hp (.ofAdd y)
    rw [← show (p k).toAdd = y from congrArg Multiplicative.toAdd hk, quotientConjRatio_apply]
    have heq : conjEndo K (g (.ofAdd (0 : X))) (hg 0) k = k := by
      apply Subtype.ext
      simp [conjEndo_val]
    rw [heq]
    simp
  map_add' x x' := by
    ext y
    obtain ⟨k, hk⟩ := hp (.ofAdd y)
    rw [← show (p k).toAdd = y from congrArg Multiplicative.toAdd hk, AddChar.add_apply]
    let k' := conjEndo K (g (.ofAdd x')) (hg x') k
    have heq : conjEndo K (g (.ofAdd (x + x'))) (hg (x + x')) k =
        conjEndo K (g (.ofAdd x)) (hg x) k' := by
      apply Subtype.ext
      simp only [k', conjEndo_val, ofAdd_add, map_mul]
      group
    have hr := quotientConjRatio_apply ϑ p hp (hg x) (hfix x) k'
    rw [show p k' = p k from hpconj x' k] at hr
    rw [quotientConjRatio_apply, heq, hr, quotientConjRatio_apply, ← Units.val_mul]
    change ((ϑ k / ϑ (conjEndo K (g (.ofAdd x)) (hg x) k') : ℂˣ) : ℂ) =
      ↑((ϑ k' / ϑ (conjEndo K (g (.ofAdd x)) (hg x) k')) * (ϑ k / ϑ k'))
    congr 1
    rw [div_mul_div_comm,
      mul_comm (ϑ (conjEndo K (g (.ofAdd x)) (hg x) k')) (ϑ k'),
      mul_div_mul_left_eq_div]

theorem quotientConjRatios_apply {K : Subgroup G} {Y : Type uZ} [AddCommGroup Y]
    {X : Type uX} [AddCommGroup X] (ϑ : K →* ℂˣ)
    (p : K →* Multiplicative Y) (hp : Function.Surjective p) (g : Multiplicative X →* G)
    (hg : ∀ x : X, ∀ k ∈ K, g (.ofAdd x) * k * (g (.ofAdd x))⁻¹ ∈ K)
    (hpconj : ∀ (x : X) (k : K), p (conjEndo K (g (.ofAdd x)) (hg x) k) = p k)
    (hfix : ∀ (x : X) (k : K), p k = 1 →
      ϑ (conjEndo K (g (.ofAdd x)) (hg x) k) = ϑ k) (x : X) (k : K) :
    quotientConjRatios ϑ p hp g hg hpconj hfix x (p k).toAdd =
      ((ϑ k / ϑ (conjEndo K (g (.ofAdd x)) (hg x) k) : ℂˣ) : ℂ) :=
  quotientConjRatio_apply ϑ p hp (hg x) (hfix x) k

/-- Surjectivity of the conjugation family transfers a vector outside the `M`-relations
from the kernel of the quotient map to the whole group. -/
def FiniteQuotientCharacterTransferStatement : Prop :=
    ∀ {G : Type uG} [Group G] {V : Type uV} [AddCommGroup V] [Module ℂ V],
    ∀ (ρ : Representation ℂ G V) {K : Subgroup G} (M : Subgroup G) (ϑ : K →* ℂˣ)
    {Y : Type uZ} [AddCommGroup Y] [Finite Y] {X : Type uX} [AddCommGroup X]
    (p : K →* Multiplicative Y) (hp : Function.Surjective p) (g : Multiplicative X →* G)
    (hg : ∀ x : X, ∀ k ∈ K, g (.ofAdd x) * k * (g (.ofAdd x))⁻¹ ∈ K)
    (hpconj : ∀ (x : X) (k : K), p (conjEndo K (g (.ofAdd x)) (hg x) k) = p k)
    (hfix : ∀ (x : X) (k : K), p k = 1 →
      ϑ (conjEndo K (g (.ofAdd x)) (hg x) k) = ϑ k)
    (hsurj : Function.Surjective (quotientConjRatios ϑ p hp g hg hpconj hfix))
    (hgM : ∀ (x : X), ∀ m ∈ M, (g (.ofAdd x))⁻¹ * m * g (.ofAdd x) ∈ M)
    {v : V} (hv : ∀ k : K, p k = 1 → ρ k v = (ϑ k : ℂ) • v)
    (hvM : v ∉ relations ρ M),
    ∃ w : V, (∀ k : K, ρ k w = (ϑ k : ℂ) • w) ∧ w ∉ relations ρ M

theorem exists_isotypic_not_mem_relations_of_quotientConjRatios :
    FiniteQuotientCharacterTransferStatement.{uG, uV, uZ, uX} := by
  intro G _ V _ _ ρ K M ϑ Y _ _ X _ p hp g hg hpconj hfix hsurj hgM v hv hvM
  classical
  let x := fun χ => (hsurj χ).choose
  have hx (χ : AddChar Y ℂ) : quotientConjRatios ϑ p hp g hg hpconj hfix (x χ) = χ :=
    (hsurj χ).choose_spec
  let H := p.ker.map K.subtype
  have hH : H.subgroupOf K = p.ker := by
    ext k
    constructor
    · rintro ⟨j, hj, hjk⟩
      exact Subtype.ext hjk ▸ hj
    · intro hk
      exact ⟨k, hk, rfl⟩
  have : Finite (K ⧸ H.subgroupOf K) := by
    rw [hH]
    exact Finite.of_equiv p.range (QuotientGroup.quotientKerEquivRange p).symm.toEquiv
  let := Fintype.ofFinite (K ⧸ H.subgroupOf K)
  let := Fintype.ofFinite Y
  let := Fintype.ofFinite (AddChar Y ℂ)
  let Φ (k : K) : AddChar (AddChar Y ℂ) ℂ := AddChar.doubleDualEmb (p k).toAdd
  refine exists_isotypic_not_mem_relations_of_addChar ρ (𝒦 := H) M ϑ
    (fun χ => g (.ofAdd (x χ))) Φ
    (fun χ => hg (x χ)) ?_ ?_ ?_ ?_ ?_ hvM
  · intro χ k hk
    simpa only [ofAdd_neg, map_inv, inv_inv] using hg (-(x χ)) k hk
  · intro χ k
    have h := quotientConjRatios_apply ϑ p hp g hg hpconj hfix (x χ) k
    rw [hx χ] at h
    rw [show Φ k χ = χ (p k).toAdd from rfl, h, ← Units.val_mul]
    congr 1
    change ϑ (conjEndo K (g (.ofAdd (x χ))) (hg (x χ)) k) *
      (ϑ k / ϑ (conjEndo K (g (.ofAdd (x χ))) (hg (x χ)) k)) = ϑ k
    exact mul_div_cancel _ _
  · intro k
    rw [show ((k : G) ∈ H) ↔ k ∈ H.subgroupOf K from Iff.rfl, hH, MonoidHom.mem_ker]
    exact AddChar.doubleDualEmb_eq_zero
  · intro χ m hm
    simpa only [inv_inv] using hgM (x χ) m hm
  · intro k hk
    apply hv
    have : k ∈ H.subgroupOf K := hk
    rwa [hH, MonoidHom.mem_ker] at this

end Langlands.Jacquet

import Langlands.BushnellKutzko.FormalIntertwining
import Langlands.BushnellKutzko.RefinementCore

/-! # Formal intertwining and conjugation of a lattice coset -/

noncomputable section

open scoped Pointwise

namespace Langlands.BushnellKutzko

universe uO uF uV

variable {O : Type uO} {F : Type uF} {V : Type uV} [CommRing O] [Field F] [Algebra O F]
  [AddCommGroup V] [Module F V] [Module O V] [IsScalarTower O F V]

local notation "A" => Module.End F V
local notation "G" => (Module.End F V)ˣ

/-- Formal self-intertwining of the coset of a coefficient modulo an integral submodule. -/
def latticeCosetIntertwining (b : A) (D : Submodule O A) : Set G :=
  {g | ∃ x : A, x - b ∈ D ∧ (↑g⁻¹ : A) * x * (g : A) - b ∈ D}

@[simp]
theorem latticeCosetIntertwining_endFiltration (S : Stratum O F V) :
    latticeCosetIntertwining S.b (S.chain.endFiltration (-S.r)) = S.formalSelfIntertwining := rfl

/-- Enlarging the error lattice enlarges the formal intertwining set. -/
theorem latticeCosetIntertwining_mono (b : A) : Monotone (latticeCosetIntertwining (O := O) b) :=
  fun _ _ h _ ⟨x, hx, hg⟩ => ⟨x, h hx, h hg⟩

/-- A single correction by the smaller neighborhood increases the ambient depth
of the error. Both adjoint and multiplication terms stay in the error lattice. -/
private theorem latticeCoset_conjugate_once (L : LatticeChain O F V) (b : A)
    (D J : Submodule O A) (K : Subgroup G) (t : ℤ)
    (hK : ∀ g : G, g ∈ K ↔ (g : A) - 1 ∈ J)
    (hJ : J ≤ L.endFiltration 1) (hJD : J * D ≤ D) (hDJ : D * J ≤ D)
    (hD : D = J.map (adjointMap O b) ⊔ L.endFiltration t)
    {k : ℤ} (hkt : k < t) {δ : A} (hδ : δ ∈ D) (hδk : δ ∈ L.endFiltration k) :
    ∃ g ∈ K, ∃ δ' ∈ D, δ' ∈ L.endFiltration (k + 1) ∧
      (↑g⁻¹ : A) * (b + δ) * (g : A) = b + δ' := by
  obtain ⟨a, ha, p, hp, hsum⟩ := Submodule.mem_sup.mp (hD ▸ hδ)
  obtain ⟨v, hv, rfl⟩ := Submodule.mem_map.mp ha
  let y := -v
  have hy : y ∈ J := neg_mem hv
  have had : adjointMap O b y ∈ D := by
    rw [hD]
    exact Submodule.mem_sup_left (Submodule.mem_map_of_mem hy)
  have hadp : δ + adjointMap O b y = p := by
    rw [← hsum, map_neg]
    abel
  have hadk : adjointMap O b y ∈ L.endFiltration k := by
    have he : p - δ = adjointMap O b y := by
      rw [← hadp]
      abel
    rw [← he]
    exact sub_mem (L.endFiltration_antitone hkt.le hp) hδk
  obtain ⟨g, _, hgval⟩ := L.exists_mem_unitFiltration (n := 1) (by decide) (hJ hy)
  have hg : g ∈ K := (hK g).mpr (by simpa only [hgval, add_sub_cancel_left] using hy)
  let z : A := (↑g⁻¹ : A) - 1
  have hz : z ∈ J := (hK g⁻¹).mp (inv_mem hg)
  let c := δ * y - y * δ
  have hc : c ∈ D := sub_mem (hDJ (Submodule.mul_mem_mul hδ hy)) (hJD (Submodule.mul_mem_mul hy hδ))
  have hck : c ∈ L.endFiltration (k + 1) := by
    refine sub_mem (L.mul_mem_endFiltration hδk (hJ hy)) ?_
    rw [add_comm]
    exact L.mul_mem_endFiltration (hJ hy) hδk
  have hck' : c ∈ L.endFiltration k := L.endFiltration_antitone (by omega) hck
  have hterm : z * (adjointMap O b y + c) ∈ D := hJD (Submodule.mul_mem_mul hz (add_mem had hc))
  have htermk : z * (adjointMap O b y + c) ∈ L.endFiltration (k + 1) := by
    rw [add_comm]
    exact L.mul_mem_endFiltration (hJ hz) (add_mem hadk hck')
  have hδ' : p + c + z * (adjointMap O b y + c) ∈ D := by
    have hpD : p ∈ D := by
      rw [← hadp]
      exact add_mem hδ had
    exact add_mem (add_mem hpD hc) hterm
  have hδ'k : p + c + z * (adjointMap O b y + c) ∈ L.endFiltration (k + 1) :=
    add_mem (add_mem (L.endFiltration_antitone (by omega) hp) hck) htermk
  refine ⟨g, hg, _, hδ', hδ'k, ?_⟩
  have hcomm : (b + δ) * (g : A) - (g : A) * (b + δ) = adjointMap O b y + c := by
    rw [hgval]
    change (b + δ) * (1 + y) - (1 + y) * (b + δ) = (b * y - y * b) + (δ * y - y * δ)
    noncomm_ring
  have he : (↑g⁻¹ : A) * (b + δ) * (g : A) =
      b + δ + (↑g⁻¹ : A) * ((b + δ) * (g : A) - (g : A) * (b + δ)) := by
    rw [mul_sub, ← mul_assoc (↑g⁻¹ : A), ← mul_assoc (↑g⁻¹ : A) (g : A), Units.inv_mul, one_mul]
    abel
  rw [he, hcomm, show (↑g⁻¹ : A) = 1 + z by dsimp only [z]; abel, add_mul, one_mul]
  calc
    b + δ + (adjointMap O b y + c + z * (adjointMap O b y + c)) =
        b + ((δ + adjointMap O b y) + c + z * (adjointMap O b y + c)) := by abel
    _ = _ := by rw [hadp]

/-- Successive corrections conjugate an element of the enlarged lattice coset
back into the coset of the filtration step. This is the finite depth iteration
of BK93 (3.3.12)–(3.3.13). -/
theorem exists_conj_sub_mem_filtration_of_adjoint_image (L : LatticeChain O F V) (b : A)
    (D J : Submodule O A) (K : Subgroup G) (t : ℤ)
    (hK : ∀ g : G, g ∈ K ↔ (g : A) - 1 ∈ J)
    (hJ : J ≤ L.endFiltration 1) (hJD : J * D ≤ D) (hDJ : D * J ≤ D)
    (hD : D = J.map (adjointMap O b) ⊔ L.endFiltration t)
    {δ : A} (hδ : δ ∈ D) {k : ℤ} (hδk : δ ∈ L.endFiltration k) :
    ∃ g ∈ K, (↑g⁻¹ : A) * (b + δ) * (g : A) - b ∈ L.endFiltration t := by
  have iterate (d : ℕ) : ∀ (k : ℤ), k + d = t →
      ∀ δ ∈ D, δ ∈ L.endFiltration k →
      ∃ g ∈ K, (↑g⁻¹ : A) * (b + δ) * (g : A) - b ∈ L.endFiltration t := by
    induction d with
    | zero =>
      intro k hk δ hδ hδk
      refine ⟨1, one_mem K, ?_⟩
      simpa only [inv_one, Units.val_one, one_mul, mul_one, add_sub_cancel_left,
        Nat.cast_zero, add_zero] using (show δ ∈ L.endFiltration t from (by simpa using hk : k = t) ▸ hδk)
    | succ d ih =>
      intro k hk δ hδ hδk
      obtain ⟨g, hg, δ', hδ', hδ'k, he⟩ :=
        latticeCoset_conjugate_once L b D J K t hK hJ hJD hDJ hD (by omega) hδ hδk
      obtain ⟨u, hu, hu'⟩ := ih (k + 1) (by omega) δ' hδ' hδ'k
      refine ⟨g * u, K.mul_mem hg hu, ?_⟩
      rw [mul_inv_rev, Units.val_mul, Units.val_mul]
      rw [show (↑u⁻¹ : A) * (↑g⁻¹ : A) * (b + δ) * ((g : A) * (u : A)) =
        (↑u⁻¹ : A) * ((↑g⁻¹ : A) * (b + δ) * (g : A)) * (u : A) by simp only [mul_assoc], he]
      exact hu'
  by_cases hkt : k ≤ t
  · exact iterate (t - k).toNat k (by omega) δ hδ hδk
  · refine ⟨1, one_mem K, ?_⟩
    simpa only [inv_one, Units.val_one, one_mul, mul_one, add_sub_cancel_left] using
      L.endFiltration_antitone (by omega : t ≤ k) hδk

private def inverseConjugate (g : G) (x : A) : A := (↑g⁻¹ : A) * x * (g : A)

private theorem inverseConjugate_mul (g h : G) (x : A) :
    inverseConjugate (g * h) x = inverseConjugate h (inverseConjugate g x) := by
  simp only [inverseConjugate, mul_inv_rev, Units.val_mul, mul_assoc]

/-- The adjoint-image inclusion and the two multiplication bounds imply that
the larger lattice coset is preserved by the congruence units. -/
theorem latticeCoset_conj_sub_mem_of_adjoint_image (b : A) {D J : Submodule O A}
    (hJD : J * D ≤ D) (hDJ : D * J ≤ D) (hA : J.map (adjointMap O b) ≤ D)
    {g : G} (hg : (g : A) - 1 ∈ J) (hgi : (↑g⁻¹ : A) - 1 ∈ J)
    {x : A} (hx : x - b ∈ D) : (↑g⁻¹ : A) * x * (g : A) - b ∈ D := by
  have hleft {z : A} (hz : z ∈ D) : (↑g⁻¹ : A) * z ∈ D := by
    have he : (↑g⁻¹ : A) * z = z + ((↑g⁻¹ : A) - 1) * z := by noncomm_ring
    rw [he]
    exact add_mem hz (hJD (Submodule.mul_mem_mul hgi hz))
  have hright {z : A} (hz : z ∈ D) : z * (g : A) ∈ D := by
    have he : z * (g : A) = z + z * ((g : A) - 1) := by noncomm_ring
    rw [he]
    exact add_mem hz (hDJ (Submodule.mul_mem_mul hz hg))
  have hc : (↑g⁻¹ : A) * b * (g : A) - b =
      (↑g⁻¹ : A) * adjointMap O b ((g : A) - 1) := by
    have ha : adjointMap O b ((g : A) - 1) = b * (g : A) - (g : A) * b := by
      change b * ((g : A) - 1) - ((g : A) - 1) * b = _
      noncomm_ring
    rw [ha, mul_sub, ← mul_assoc, ← mul_assoc (↑g⁻¹ : A), Units.inv_mul, one_mul]
  have he : (↑g⁻¹ : A) * x * (g : A) - b =
      (↑g⁻¹ : A) * (x - b) * (g : A) + ((↑g⁻¹ : A) * b * (g : A) - b) := by
    noncomm_ring
  rw [he, hc]
  exact add_mem (hright (hleft hx)) (hleft (hA (Submodule.mem_map_of_mem hg)))

/-- If a subgroup preserves the larger coset and moves each of its elements
into the smaller coset, formal intertwining of the larger coset is the
two-sided product of the subgroup and the smaller intertwining set. -/
theorem latticeCosetIntertwining_eq_sandwich (b : A) {D P : Submodule O A}
    (K : Subgroup G) (hPD : P ≤ D)
    (hpres : ∀ g ∈ K, ∀ x : A, x - b ∈ D → (↑g⁻¹ : A) * x * (g : A) - b ∈ D)
    (hmove : ∀ x : A, x - b ∈ D → ∃ g ∈ K, (↑g⁻¹ : A) * x * (g : A) - b ∈ P) :
    latticeCosetIntertwining b D = (K : Set G) * latticeCosetIntertwining b P * (K : Set G) := by
  ext g
  constructor
  · rintro ⟨x, hx, hxg⟩
    obtain ⟨y, hy, hyx⟩ := hmove x hx
    obtain ⟨z, hz, hz'⟩ := hmove (inverseConjugate g x) hxg
    let h := y⁻¹ * g * z
    have hh : h ∈ latticeCosetIntertwining b P := by
      refine ⟨inverseConjugate y x, hyx, ?_⟩
      change inverseConjugate h (inverseConjugate y x) - b ∈ P
      rw [← inverseConjugate_mul, show y * h = g * z by dsimp only [h]; group,
        inverseConjugate_mul]
      exact hz'
    exact Set.mem_mul.mpr ⟨y * h, Set.mul_mem_mul hy hh, z⁻¹, K.inv_mem hz,
      by dsimp only [h]; group⟩
  · intro hg
    obtain ⟨yh, hyh, z, hz, rfl⟩ := Set.mem_mul.mp hg
    obtain ⟨y, hy, h, hh, rfl⟩ := Set.mem_mul.mp hyh
    obtain ⟨x, hx, hxh⟩ := hh
    refine ⟨inverseConjugate y⁻¹ x, hpres y⁻¹ (K.inv_mem hy) x (hPD hx), ?_⟩
    change inverseConjugate (y * h * z) (inverseConjugate y⁻¹ x) - b ∈ D
    rw [← inverseConjugate_mul, show y⁻¹ * (y * h * z) = h * z by group, inverseConjugate_mul]
    exact hpres z hz (inverseConjugate h x) (hPD hxh)

end Langlands.BushnellKutzko

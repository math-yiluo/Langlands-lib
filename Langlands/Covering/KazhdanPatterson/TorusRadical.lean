import Langlands.Covering.KazhdanPatterson.TorusCover
import Mathlib.Order.Minimal

/-! # The center and maximal abelian subgroups of the diagonal cover -/

namespace Langlands.KazhdanPatterson

open scoped BigOperators commutatorElement
open NormalizedTwoCocycle.Extension (inl inl_injective projection projection_surjective)

attribute [local instance] trivialCoefficientAction

universe u v

variable {r : ℕ} {U : Type u} {A : Type v} [CommGroup U] [CommGroup A]

/-- Diagonal tuples whose lifts commute with every lift in the torus cover. -/
def torusRadical (H : U →* U →* A) (c : ℤ) : Subgroup (Fin r → U) :=
  (torusCommutatorPairing H c).ker

theorem mem_torusRadical_iff (H : U →* U →* A) (c : ℤ) (t : Fin r → U) :
    t ∈ torusRadical H c ↔ ∀ s, torusCommutatorPairing H c t s = 1 := by
  change torusCommutatorPairing H c t = 1 ↔ _
  exact ⟨fun h s => DFunLike.congr_fun h s, fun h => MonoidHom.ext (fun s => h s)⟩

theorem torusCover_center_eq (H : U →* U →* A) (c : ℤ) :
    Subgroup.center (TorusCover (r := r) H c) =
      (torusRadical H c).comap (projection (torusCocycle H c)) := by
  ext x
  exact (torusCover_mem_center_iff H c x).trans (mem_torusRadical_iff H c x.right).symm

private theorem prod_symbol_mulSingle (H : U →* U →* A) (t : Fin r → U) (i : Fin r) (a : U) :
    (∏ j, H (t j) ((Pi.mulSingle i a : Fin r → U) j)) = H (t i) a := by
  rw [Finset.prod_eq_single i]
  · simp
  · intro j _ hji
    simp [Pi.mulSingle_eq_of_ne hji]
  · simp

theorem torusCommutatorPairing_mulSingle (H : U →* U →* A)
    (hskew : ∀ a b, H b a = (H a b)⁻¹) (c : ℤ) (t : Fin r → U) (i : Fin r) (a : U) :
    torusCommutatorPairing H c t (Pi.mulSingle i a) =
      H (diagonalDeterminant t ^ (2 * c + 1) / t i) a := by
  rw [torusCommutatorPairing_eq H hskew, diagonalDeterminant_apply (Pi.mulSingle i a),
    Fintype.prod_pi_mulSingle', prod_symbol_mulSingle, map_div, map_zpow]
  rfl

/-- The center criterion obtained by testing one coordinate at a time. -/
theorem mem_torusRadical_iff_coordinate (H : U →* U →* A)
    (hskew : ∀ a b, H b a = (H a b)⁻¹) (c : ℤ) (t : Fin r → U) :
    t ∈ torusRadical H c ↔
      ∀ i a, H (diagonalDeterminant t ^ (2 * c + 1) / t i) a = 1 := by
  change torusCommutatorPairing H c t = 1 ↔ _
  constructor
  · intro h i a
    rw [← torusCommutatorPairing_mulSingle H hskew, h]
    rfl
  · intro h
    apply MonoidHom.functions_ext A
    intro i a
    rw [torusCommutatorPairing_mulSingle H hskew]
    exact h i a

/-- When the Hilbert-symbol radical is the group of `e`-th powers, centrality is
equivalent to an `e`-th power condition in each coordinate. -/
theorem torusCover_mem_center_iff_powers (H : U →* U →* A)
    (hskew : ∀ a b, H b a = (H a b)⁻¹) (e : ℕ)
    (hrad : ∀ u, (∀ a, H u a = 1) ↔ ∃ v : U, v ^ e = u)
    (c : ℤ) (x : TorusCover (r := r) H c) :
    x ∈ Subgroup.center (TorusCover (r := r) H c) ↔
      ∀ i, ∃ v : U, v ^ e = diagonalDeterminant x.right ^ (2 * c + 1) / x.right i := by
  rw [torusCover_center_eq]
  change x.right ∈ torusRadical H c ↔ _
  simp only [mem_torusRadical_iff_coordinate H hskew, hrad]

/-- A diagonal subgroup is isotropic if the commutator pairing is trivial on it. -/
def IsTorusIsotropic (H : U →* U →* A) (c : ℤ) (T : Subgroup (Fin r → U)) : Prop :=
  ∀ t ∈ T, ∀ s ∈ T, torusCommutatorPairing H c t s = 1

private theorem torusCover_mul_comm_iff (H : U →* U →* A) (c : ℤ)
    (x y : TorusCover (r := r) H c) :
    x * y = y * x ↔ torusCommutatorPairing H c x.right y.right = 1 := by
  rw [← commutatorElement_eq_one_iff_mul_comm, torusCover_commutator, ← map_one (inl _)]
  exact (inl_injective _).eq_iff

theorem torusCover_isMulCommutative_iff (H : U →* U →* A) (c : ℤ)
    (S : Subgroup (TorusCover (r := r) H c)) :
    IsMulCommutative S ↔ IsTorusIsotropic H c (S.map (projection (torusCocycle H c))) := by
  rw [isMulCommutative_iff_of_setLike]
  constructor
  · rintro h _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    exact (torusCover_mul_comm_iff H c x y).mp (h x hx y hy)
  · intro h x hx y hy
    exact (torusCover_mul_comm_iff H c x y).mpr
      (h x.right (Subgroup.mem_map_of_mem _ hx) y.right (Subgroup.mem_map_of_mem _ hy))

/-- The maximal abelian subgroups of the torus cover are the full inverse images
of the maximal isotropic subgroups of the diagonal torus. -/
theorem torusCover_maximalAbelian_iff (H : U →* U →* A) (c : ℤ)
    (S : Subgroup (TorusCover (r := r) H c)) :
    Maximal (fun K : Subgroup (TorusCover (r := r) H c) => IsMulCommutative K) S ↔
      ∃ T, Maximal (IsTorusIsotropic H c) T ∧
        S = T.comap (projection (torusCocycle H c)) := by
  let p := projection (torusCocycle (r := r) H c)
  have hmap (T : Subgroup (Fin r → U)) : (T.comap p).map p = T :=
    Subgroup.map_comap_eq_self_of_surjective (projection_surjective _) T
  have hab (T : Subgroup (Fin r → U)) :
      IsMulCommutative (T.comap p) ↔ IsTorusIsotropic H c T := by
    rw [torusCover_isMulCommutative_iff H c]
    change IsTorusIsotropic H c ((T.comap p).map p) ↔ _
    rw [hmap]
  constructor
  · intro hS
    have ht : IsTorusIsotropic H c (S.map p) :=
      (torusCover_isMulCommutative_iff H c S).mp hS.1
    have hle_comap : S ≤ (S.map p).comap p := Subgroup.le_comap_map p S
    have hs : S = (S.map p).comap p :=
      le_antisymm hle_comap (hS.2 ((hab _).mpr ht) hle_comap)
    refine ⟨S.map p, ⟨ht, ?_⟩, hs⟩
    intro T hT hle
    have hst : S ≤ T.comap p := Subgroup.map_le_iff_le_comap.mp hle
    calc
      T = (T.comap p).map p := (hmap T).symm
      _ ≤ S.map p := Subgroup.map_mono (hS.2 ((hab T).mpr hT) hst)
  · rintro ⟨T, hT, rfl⟩
    refine ⟨(hab T).mpr hT.1, ?_⟩
    intro K hK hle
    apply Subgroup.map_le_iff_le_comap.mp
    apply hT.2 ((torusCover_isMulCommutative_iff H c K).mp hK)
    rw [← hmap T]
    exact Subgroup.map_mono hle

end Langlands.KazhdanPatterson

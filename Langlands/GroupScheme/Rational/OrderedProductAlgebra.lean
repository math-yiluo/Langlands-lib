import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.Group.Subgroup.Ker
import Mathlib.Data.List.OfFn

/-! # Ordered products in central extensions of groups -/

noncomputable section

universe v w

namespace Langlands.GroupScheme.RelativeRoot.CentralExtension

/-- The ordered product of a finite family of group homomorphisms. -/
def orderedProduct {n : ℕ} {G : Type v} [Monoid G]
    {H : Fin n → Type v} [∀ i, Monoid (H i)]
    (j : ∀ i, H i →* G) (x : ∀ i, H i) : G :=
  (List.ofFn fun i => j i (x i)).prod

/-- Applying a homomorphism preserves the original factor order. -/
theorem map_orderedProduct {n : ℕ} {G : Type v} [Monoid G]
    {Q : Type w} [Monoid Q]
    {H : Fin n → Type v} [∀ i, Monoid (H i)]
    {R : Fin n → Type w} [∀ i, Monoid (R i)]
    (j : ∀ i, H i →* G) (k : ∀ i, R i →* Q)
    (q : G →* Q) (p : ∀ i, H i →* R i)
    (h : ∀ i x, q (j i x) = k i (p i x)) (x : ∀ i, H i) :
    q (orderedProduct j x) = orderedProduct k (fun i => p i (x i)) := by
  simp only [orderedProduct, map_list_prod, List.map_ofFn]
  apply congrArg List.prod
  apply congrArg List.ofFn
  funext i
  exact h i (x i)

private theorem prod_map_mul_of_central {M : Type v} [Monoid M] {I : Type w}
    (a z : I → M) (hc : ∀ i j, Commute (z i) (a j)) (l : List I) :
    (l.map (fun i => a i * z i)).prod =
      (l.map a).prod * (l.map z).prod := by
  induction l with
  | nil => simp
  | cons i l ih =>
      simp only [List.map_cons, List.prod_cons, ih]
      have hcomm : Commute (z i) (l.map a).prod :=
        Commute.list_prod_right _ _ (by
          intro x hx
          obtain ⟨j, _, rfl⟩ := List.mem_map.1 hx
          exact hc i j)
      calc
        (a i * z i) * ((l.map a).prod * (l.map z).prod) =
            a i * (z i * (l.map a).prod) * (l.map z).prod := by
              simp only [mul_assoc]
        _ = a i * ((l.map a).prod * z i) * (l.map z).prod := by rw [hcomm.eq]
        _ = (a i * (l.map a).prod) * (z i * (l.map z).prod) := by
              simp only [mul_assoc]

/-- Central corrections may be moved past other factors without changing order. -/
theorem orderedProduct_mul_of_central {n : ℕ} {G : Type v} [Monoid G]
    {H : Fin n → Type v} [∀ i, Monoid (H i)]
    (j : ∀ i, H i →* G) (x z : ∀ i, H i)
    (hc : ∀ i g, Commute (j i (z i)) g) :
    orderedProduct j (fun i => x i * z i) =
      orderedProduct j x * orderedProduct j z := by
  unfold orderedProduct
  simp only [map_mul]
  simpa only [List.map_ofFn, Function.comp_def, id_eq] using
    prod_map_mul_of_central (fun i => j i (x i)) (fun i => j i (z i))
      (fun i r => hc i (j r (x r))) (List.ofFn id)

section Groups

variable {n : ℕ} {G : Type v} [Group G] {Q : Type w} [Group Q]
    {H : Fin n → Type v} [∀ i, Group (H i)]
    {R : Fin n → Type w} [∀ i, Group (R i)]
    (j : ∀ i, H i →* G) (k : ∀ i, R i →* Q)
    (q : G →* Q) (p : ∀ i, H i →* R i)
    (h : ∀ i x, q (j i x) = k i (p i x))
    (hc : ∀ z, q z = 1 → ∀ g, Commute z g)

include h hc

/-- Uniqueness of quotient coordinates and kernel coordinates implies uniqueness
of the original ordered factorization. -/
theorem injective_of_quotient_and_kernel
    (hQ : Function.Injective (orderedProduct k))
    (hK : ∀ z : ∀ i, H i, (∀ i, p i (z i) = 1) →
      orderedProduct j z = 1 → ∀ i, z i = 1) :
    Function.Injective (orderedProduct j) := by
  intro x y he
  have hxy : (fun i => p i (x i)) = fun i => p i (y i) := by
    apply hQ
    rw [← map_orderedProduct j k q p h, ← map_orderedProduct j k q p h, he]
  let z : ∀ i, H i := fun i => (x i)⁻¹ * y i
  have hz : ∀ i, p i (z i) = 1 := by
    intro i
    simp only [z, map_mul, map_inv, congrFun hxy i, inv_mul_cancel]
  have hcz : ∀ i g, Commute (j i (z i)) g := by
    intro i g
    apply hc _ _ g
    rw [h, hz, map_one]
  have hy : y = fun i => x i * z i := by
    funext i
    simp only [z, mul_inv_cancel_left]
  have hprod : orderedProduct j z = 1 := by
    have e := he
    rw [hy, orderedProduct_mul_of_central j x z hcz] at e
    exact (mul_eq_left).1 e.symm
  have hz1 := hK z hz hprod
  funext i
  exact inv_mul_eq_one.mp (hz1 i)

/-- Lifts of quotient coordinates can be corrected by central kernel coordinates
to factor the given element. No surjectivity of the original factor maps is used. -/
theorem exists_of_lifts_and_kernel
    (hK : ∀ z : G, q z = 1 →
      ∃ t : ∀ i, H i, (∀ i, p i (t i) = 1) ∧ orderedProduct j t = z)
    (g : G) (x : ∀ i, H i)
    (hx : orderedProduct k (fun i => p i (x i)) = q g) :
    ∃ y : ∀ i, H i, orderedProduct j y = g := by
  let z : G := (orderedProduct j x)⁻¹ * g
  have hz : q z = 1 := by
    simp only [z, map_mul, map_inv, map_orderedProduct j k q p h, hx, inv_mul_cancel]
  obtain ⟨t, ht, hprod⟩ := hK z hz
  refine ⟨fun i => x i * t i, ?_⟩
  rw [orderedProduct_mul_of_central j x t (fun i g' => hc _ (by
    rw [h, ht, map_one]) g'), hprod]
  exact mul_inv_cancel_left _ _

end Groups

end Langlands.GroupScheme.RelativeRoot.CentralExtension

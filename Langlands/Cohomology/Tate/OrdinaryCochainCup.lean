import Mathlib.RepresentationTheory.Homological.GroupCohomology.Basic
import Langlands.Cohomology.Tate.ZeroDefinitions
import Langlands.Cohomology.Tate.OrdinaryCupLeibniz

noncomputable section

universe u

open CategoryTheory groupCohomology

namespace Langlands.Tate

variable {R G : Type u} [CommRing R] [Group G] {A B C : Rep R G}

/-- The explicit ordinary cup product of inhomogeneous cochains. -/
def ordinaryCochainCup (φ : Pairing A B C) (p q : ℕ) :
    (inhomogeneousCochains A).X p →ₗ[R] (inhomogeneousCochains B).X q →ₗ[R]
      (inhomogeneousCochains C).X (p + q) :=
  LinearMap.mk₂ R
    (fun f g => fun x : Fin (p + q) → G =>
      φ.bilinear (f fun i => x (Fin.castAdd q i))
        (B.ρ (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod
          (g fun j => x (Fin.natAdd p j))))
    (fun f f' g => by funext x; simp)
    (fun r f g => by funext x; simp)
    (fun f g g' => by funext x; simp)
    (fun r f g => by funext x; simp)

/-- The displayed value of the ordinary cochain cup on a tuple. -/
lemma ordinaryCochainCup_apply (φ : Pairing A B C) (p q : ℕ)
    (f : (inhomogeneousCochains A).X p) (g : (inhomogeneousCochains B).X q)
    (x : Fin (p + q) → G) :
    ordinaryCochainCup φ p q f g x =
      φ.bilinear (f fun i => x (Fin.castAdd q i))
        (B.ρ (List.ofFn fun i : Fin p => x (Fin.castAdd q i)).prod
          (g fun j => x (Fin.natAdd p j))) := rfl

section Tuples

private lemma partialProd_last {n : ℕ} (v : Fin n → G) :
    Fin.partialProd v (Fin.last n) = (List.ofFn v).prod := by
  rw [Fin.partialProd, Fin.val_last, List.take_of_length_le (by simp)]

/-- Contracting an interior adjacent pair does not change the ordered product. -/
private lemma prod_ofFn_contractNth_castSucc {p : ℕ} (u : Fin (p + 1) → G) (i : Fin p) :
    (List.ofFn fun i' => Fin.contractNth i.castSucc (· * ·) u i').prod = (List.ofFn u).prod := by
  have key := congrFun (Fin.partialProd_contractNth u i.castSucc) (Fin.last p)
  rw [Function.comp_apply, Fin.succAbove_of_le_castSucc _ _
    (by rw [Fin.le_iff_val_le_val]; simp), Fin.succ_last, partialProd_last,
    partialProd_last] at key
  exact key

private lemma contractNth_castAdd_castAdd {p q : ℕ} (x : Fin (p + q + 1) → G) (i i' : Fin p) :
    Fin.contractNth (Fin.castAdd (q + 1) i) (· * ·) x (Fin.castAdd q i') =
      Fin.contractNth i.castSucc (· * ·)
        (fun k : Fin (p + 1) => x (Fin.cast (by omega) (Fin.castAdd q k))) i' := by
  have hx : ∀ a b : Fin (p + q + 1), (a : ℕ) = b → x a = x b :=
    fun a b hab => congrArg x (Fin.ext hab)
  simp only [Fin.contractNth, Fin.val_castAdd, Fin.val_castSucc]
  split_ifs
  · exact hx _ _ (by simp)
  · exact congrArg₂ (· * ·) (hx _ _ (by simp)) (hx _ _ (by simp))
  · exact hx _ _ (by simp)

private lemma contractNth_castAdd_natAdd {p q : ℕ} (x : Fin (p + q + 1) → G) (i : Fin p)
    (j : Fin q) :
    Fin.contractNth (Fin.castAdd (q + 1) i) (· * ·) x (Fin.natAdd p j) =
      x (Fin.cast (by omega : p + 1 + q = p + q + 1) (Fin.natAdd (p + 1) j)) := by
  rw [Fin.contractNth_apply_of_gt _ _ _ _ (by simp; omega)]
  exact congrArg x (Fin.ext (by simp; omega))

private lemma contractNth_natAdd_castAdd {p q : ℕ} (x : Fin (p + q + 1) → G) (k : Fin (q + 1))
    (i : Fin p) :
    Fin.contractNth (Fin.natAdd (m := q + 1) p k) (· * ·) x (Fin.castAdd q i) =
      x (Fin.castAdd (q + 1) i) := by
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp; omega)]
  exact congrArg x (Fin.ext (by simp))

private lemma contractNth_natAdd_natAdd {p q : ℕ} (x : Fin (p + q + 1) → G) (k : Fin (q + 1))
    (j : Fin q) :
    Fin.contractNth (Fin.natAdd (m := q + 1) p k) (· * ·) x (Fin.natAdd p j) =
      Fin.contractNth k (· * ·) (fun j' : Fin (q + 1) => x (Fin.natAdd p j')) j := by
  have hx : ∀ a b : Fin (p + q + 1), (a : ℕ) = b → x a = x b :=
    fun a b hab => congrArg x (Fin.ext hab)
  simp only [Fin.contractNth, Fin.val_natAdd, add_lt_add_iff_left, add_right_inj]
  split_ifs
  · exact hx _ _ (by simp)
  · exact congrArg₂ (· * ·) (hx _ _ (by simp)) (hx _ _ (by simp; omega))
  · exact hx _ _ (by simp; omega)

private lemma contractNth_last_front {p q : ℕ} (x : Fin (p + q + 1) → G) :
    Fin.contractNth (Fin.last p) (· * ·)
        (fun k : Fin (p + 1) => x (Fin.cast (by omega : p + 1 + q = p + q + 1) (Fin.castAdd q k))) =
      fun i => x (Fin.castAdd (q + 1) i) := by
  funext i
  rw [Fin.contractNth_apply_of_lt _ _ _ _ (by simp)]
  exact congrArg x (Fin.ext (by simp))

end Tuples

/-- The Leibniz identity `d (f ∪ g) = (d f) ∪ g + (-1) ^ p • f ∪ (d g)`, with the first
summand transported from degree `(p + 1) + q` to `(p + q) + 1`. -/
theorem ordinaryCochainCup_d (φ : Pairing A B C) (p q : ℕ)
    (f : (inhomogeneousCochains A).X p) (g : (inhomogeneousCochains B).X q) :
    _root_.inhomogeneousCochains.d C (p + q) (ordinaryCochainCup φ p q f g) =
      OrdinaryCup.transport C (by omega : (p + 1) + q = (p + q) + 1)
        (ordinaryCochainCup φ (p + 1) q (_root_.inhomogeneousCochains.d A p f) g) +
      (-1 : R) ^ p • ordinaryCochainCup φ p (q + 1) f
        (_root_.inhomogeneousCochains.d B q g) := by
  funext x
  simp only [_root_.inhomogeneousCochains.d_hom_apply]
  rw [Pi.add_apply, Pi.smul_apply, OrdinaryCup.transport_apply]
  simp only [ordinaryCochainCup, LinearMap.mk₂_apply, _root_.inhomogeneousCochains.d_hom_apply,
    Function.comp_apply]
  have h : p + 1 + q = p + q + 1 := by omega
  have hx : ∀ a b : Fin (p + q + 1), (a : ℕ) = b → x a = x b :=
    fun a b hab => congrArg x (Fin.ext hab)
  -- the leading action terms agree by equivariance of the pairing
  have e0 : φ.bilinear ((A.ρ (x (Fin.cast h (Fin.castAdd q 0))))
        (f fun i => x (Fin.cast h (Fin.castAdd q i.succ))))
        ((B.ρ (List.ofFn fun i => x (Fin.cast h (Fin.castAdd q i))).prod)
          (g fun j => x (Fin.cast h (Fin.natAdd (p + 1) j)))) =
      C.ρ (x 0) (φ.bilinear (f fun i => x (Fin.castAdd q i).succ)
        ((B.ρ (List.ofFn fun i => x (Fin.castAdd q i).succ).prod)
          (g fun j => x (Fin.natAdd p j).succ))) := by
    have h1 : (fun i : Fin p => x (Fin.cast h (Fin.castAdd q i.succ))) =
        fun i => x (Fin.castAdd q i).succ := funext fun i => hx _ _ (by simp)
    have h2 : (fun j : Fin q => x (Fin.cast h (Fin.natAdd (p + 1) j))) =
        fun j => x (Fin.natAdd p j).succ := funext fun j => hx _ _ (by simp; omega)
    have h3 : x (Fin.cast h (Fin.castAdd q 0)) = x 0 := hx _ _ (by simp)
    rw [List.ofFn_succ, List.prod_cons, map_mul, Module.End.mul_apply, φ.equivariant, h1, h2, h3]
  have hsplit : ∀ F : Fin (p + q + 1) → C, ∑ i, F i =
      ∑ i : Fin p, F (Fin.castAdd (q + 1) i) + ∑ k : Fin (q + 1), F (Fin.natAdd p k) :=
    fun F => Fin.sum_univ_add (a := p) (b := q + 1) F
  -- the product over the first `p + 1` entries splits off its last factor
  have q9 : (List.ofFn fun k : Fin (p + 1) => x (Fin.cast h (Fin.castAdd q k))).prod =
      (List.ofFn fun i : Fin p => x (Fin.castAdd (q + 1) i)).prod * x (Fin.natAdd p (0 : Fin (q + 1))) := by
    rw [List.ofFn_succ', List.prod_concat]
    exact congrArg₂ (· * ·) (congrArg _ (congrArg _ (funext fun i => hx _ _ (by simp))))
      (hx _ _ (by simp))
  have q7 : ∀ i : Fin q, x (Fin.natAdd p i.succ) = x (Fin.cast h (Fin.natAdd (p + 1) i)) :=
    fun i => hx _ _ (by simp; omega)
  rw [map_add, LinearMap.add_apply, e0, hsplit, Fin.sum_univ_castSucc (n := p)]
  simp only [map_add, map_sum, map_smul, LinearMap.add_apply, LinearMap.sum_apply,
    LinearMap.smul_apply, smul_add, Finset.smul_sum, smul_smul,
    Fin.val_castAdd, Fin.val_natAdd, Fin.val_castSucc, Fin.val_last,
    contractNth_castAdd_castAdd, contractNth_castAdd_natAdd, contractNth_natAdd_castAdd,
    contractNth_natAdd_natAdd, contractNth_last_front, prod_ofFn_contractNth_castSucc,
    q7, q9, map_mul, Module.End.mul_apply, pow_add, pow_one, mul_assoc]
  module

end Langlands.Tate

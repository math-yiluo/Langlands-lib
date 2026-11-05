import Mathlib.Algebra.Category.Ring.Limits
import Mathlib.CategoryTheory.Limits.Types.Pullbacks
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic
import Mathlib.RingTheory.Ideal.Maps
import Mathlib.RingTheory.Nilpotent.Defs

/-! # Kernels in actual pullback squares of commutative rings -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits

namespace Langlands.AlgebraicGeometry.Picard.InfinitesimalRingPullback

variable {R A B C : Type u} [CommRing R] [CommRing A] [CommRing B] [CommRing C]
  (p : R →+* A) (q : R →+* B) (a : A →+* C) (b : B →+* C)
  (h : IsPullback (CommRingCat.ofHom p) (CommRingCat.ofHom q)
    (CommRingCat.ofHom a) (CommRingCat.ofHom b))

include h

/-- The second projection sends the kernel of the first into the opposite kernel. -/
lemma ker_fst_le_comap_ker : RingHom.ker p ≤ (RingHom.ker b).comap q := by
  intro r hr
  change b (q r) = 0
  have hw := congrArg (fun f : CommRingCat.of R ⟶ CommRingCat.of C ↦ f r) h.w
  change a (p r) = b (q r) at hw
  rw [RingHom.mem_ker.mp hr, map_zero] at hw
  exact hw.symm

/-- The actual projection on kernels, retaining multiplication as well as addition. -/
def kernelMap : RingHom.ker p →ₙ+* RingHom.ker b where
  toFun r := ⟨q r, ker_fst_le_comap_ker p q a b h r.property⟩
  map_zero' := Subtype.ext (map_zero q)
  map_add' r s := Subtype.ext (map_add q (r : R) (s : R))
  map_mul' r s := Subtype.ext (map_mul q (r : R) (s : R))

@[simp] lemma kernelMap_coe (r : RingHom.ker p) :
    (kernelMap p q a b h r : B) = q r := rfl

/-- The kernel projection is bijective for every actual ring pullback square. -/
lemma kernelMap_bijective : Function.Bijective (kernelMap p q a b h) := by
  constructor
  · intro r s hrs
    apply Subtype.ext
    apply Types.ext_of_isPullback (h.map (forget CommRingCat))
    · exact (RingHom.mem_ker.mp r.property).trans (RingHom.mem_ker.mp s.property).symm
    · exact congrArg Subtype.val hrs
  · intro y
    obtain ⟨r, hrp, hrq⟩ := Types.exists_of_isPullback
      (h.map (forget CommRingCat)) (0 : A) (y : B)
      (by
        change a 0 = b (y : B)
        rw [map_zero]
        exact (RingHom.mem_ker.mp y.property).symm)
    exact ⟨⟨r, RingHom.mem_ker.mpr hrp⟩, Subtype.ext hrq⟩

/-- The two actual kernels are isomorphic as nonunital rings. -/
def kernelEquiv : RingHom.ker p ≃+* RingHom.ker b :=
  RingEquiv.ofBijective (kernelMap p q a b h) (kernelMap_bijective p q a b h)

@[simp] lemma kernelEquiv_coe (r : RingHom.ker p) :
    (kernelEquiv p q a b h r : B) = q r := rfl

/-- A positive exponent killing the opposite kernel kills the projection kernel. -/
lemma ker_fst_pow_eq_bot {n : ℕ} (hn : n ≠ 0)
    (hb : (RingHom.ker b) ^ n = ⊥) : (RingHom.ker p) ^ n = ⊥ := by
  have hq : (RingHom.ker p) ^ n ≤ RingHom.ker q := by
    calc
      (RingHom.ker p) ^ n ≤ ((RingHom.ker b).comap q) ^ n :=
        Ideal.pow_right_mono (ker_fst_le_comap_ker p q a b h) n
      _ ≤ ((RingHom.ker b) ^ n).comap q := Ideal.le_comap_pow q n
      _ = RingHom.ker q := by rw [hb]; rfl
  apply le_antisymm ?_ bot_le
  intro r hr
  apply Ideal.mem_bot.mpr
  apply Types.ext_of_isPullback (h.map (forget CommRingCat))
  · change p r = p 0
    rw [map_zero]
    exact RingHom.mem_ker.mp (Ideal.pow_le_self hn hr)
  · change q r = q 0
    rw [map_zero]
    exact RingHom.mem_ker.mp (hq hr)

/-- Nilpotence of the opposite kernel passes to the actual projection kernel. -/
lemma ker_fst_isNilpotent (hb : IsNilpotent (RingHom.ker b)) :
    IsNilpotent (RingHom.ker p) := by
  obtain ⟨n, hn⟩ := hb
  have hn' : (RingHom.ker b) ^ (n + 1) = ⊥ := by
    change (RingHom.ker b) ^ n = ⊥ at hn
    simp [pow_succ, hn]
  exact ⟨n + 1, ker_fst_pow_eq_bot p q a b h (Nat.succ_ne_zero n) hn'⟩

end Langlands.AlgebraicGeometry.Picard.InfinitesimalRingPullback

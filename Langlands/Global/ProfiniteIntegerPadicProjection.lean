import Langlands.Global.ProfiniteIntegerRing
import Mathlib.NumberTheory.Padics.RingHoms

noncomputable section

namespace Langlands.Global

open scoped Topology

namespace ResidueLimit

/-- A compatible cone of continuous finite residues has continuous p-adic lift. -/
theorem continuous_padic_lift {R : Type*} [NonAssocSemiring R] [TopologicalSpace R]
    (p : ℕ) [Fact p.Prime] (f : ∀ n : ℕ, R →+* ZMod (p ^ n))
    (hf : ∀ i j (h : i ≤ j), (ZMod.castHom (pow_dvd_pow p h) _).comp (f j) = f i)
    (hc : ∀ n, Continuous (f n)) : Continuous (PadicInt.lift hf) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  apply Metric.continuousAt_iff'.mpr
  intro ε hε
  obtain ⟨n, hn⟩ := PadicInt.exists_pow_neg_lt p hε
  have hz : ∀ᶠ z in 𝓝 (f n x), z = f n x := by simp
  have he : ∀ᶠ y in 𝓝 x, f n y = f n x :=
    (hc n).continuousAt.eventually hz
  filter_upwards [he] with y hy
  apply lt_of_le_of_lt _ hn
  rw [dist_eq_norm, PadicInt.norm_le_pow_iff_mem_span_pow,
    ← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, sub_eq_zero]
  rw [← RingHom.comp_apply, PadicInt.lift_spec, ← RingHom.comp_apply,
    PadicInt.lift_spec]
  exact hy

end ResidueLimit

namespace ProfiniteIntegerRing

variable (p : ℕ) [Fact p.Prime]

/-- A prime power, including the zeroth power, as a positive residue modulus. -/
def primePowerModulus (n : ℕ) : ℕ+ := ⟨p ^ n, pow_pos (Fact.out : p.Prime).pos n⟩

/-- The canonical projection from full compatible residues to the p-adic integers. -/
def toPadic : ProfiniteIntegerRing →+* ℤ_[p] :=
  PadicInt.lift (f := fun n => reduction (primePowerModulus p n))
    (fun i j h => ResidueLimit.transition_comp_reduction (modulus := fun n : ℕ+ => n)
      (primePowerModulus p i) (primePowerModulus p j) (pow_dvd_pow p h))

@[simp] theorem toZModPow_toPadic (n : ℕ) (x : ProfiniteIntegerRing) :
    PadicInt.toZModPow n (toPadic p x) = reduction (primePowerModulus p n) x :=
  DFunLike.congr_fun (PadicInt.lift_spec _ n) x

@[simp] theorem toPadic_intCast (z : ℤ) :
    toPadic p (intCastHom z) = (z : ℤ_[p]) := map_intCast _ z

theorem continuous_toPadic : Continuous (toPadic p) :=
  ResidueLimit.continuous_padic_lift p _ _
    (fun n => ResidueLimit.continuous_reduction (primePowerModulus p n))

/-- The prime-power residue formula uniquely determines the projection. -/
theorem toPadic_unique (g : ProfiniteIntegerRing →+* ℤ_[p])
    (hg : ∀ n, (PadicInt.toZModPow n).comp g = reduction (primePowerModulus p n)) :
    g = toPadic p := by
  apply PadicInt.toZModPow_eq_iff_ext.mp
  intro n
  ext x
  exact (DFunLike.congr_fun (hg n) x).trans (toZModPow_toPadic p n x).symm

end ProfiniteIntegerRing

namespace PrimeToProfiniteIntegerRing

variable (p m : ℕ) [Fact p.Prime]

/-- A prime power is an allowed away modulus when the prime is coprime to `m`. -/
def primePowerModulus (h : Nat.Coprime p m) (n : ℕ) : PrimeToModulus m :=
  ⟨ProfiniteIntegerRing.primePowerModulus p n, h.pow_left n⟩

/-- The p-adic projection of the residue limit away from `m`. -/
def toPadic (h : Nat.Coprime p m) : PrimeToProfiniteIntegerRing m →+* ℤ_[p] :=
  PadicInt.lift (f := fun n => reduction (primePowerModulus p m h n))
    (fun i j hij => ResidueLimit.transition_comp_reduction
      (modulus := fun n : PrimeToModulus m => n.val)
      (primePowerModulus p m h i) (primePowerModulus p m h j) (pow_dvd_pow p hij))

@[simp] theorem toZModPow_toPadic (h : Nat.Coprime p m) (n : ℕ)
    (x : PrimeToProfiniteIntegerRing m) :
    PadicInt.toZModPow n (toPadic p m h x) =
      reduction (primePowerModulus p m h n) x :=
  DFunLike.congr_fun (PadicInt.lift_spec _ n) x

@[simp] theorem toPadic_intCast (h : Nat.Coprime p m) (z : ℤ) :
    toPadic p m h (intCastHom m z) = (z : ℤ_[p]) := map_intCast _ z

theorem continuous_toPadic (h : Nat.Coprime p m) : Continuous (toPadic p m h) :=
  ResidueLimit.continuous_padic_lift p _ _
    (fun n => ResidueLimit.continuous_reduction (primePowerModulus p m h n))

theorem toPadic_unique (h : Nat.Coprime p m)
    (g : PrimeToProfiniteIntegerRing m →+* ℤ_[p])
    (hg : ∀ n, (PadicInt.toZModPow n).comp g = reduction (primePowerModulus p m h n)) :
    g = toPadic p m h := by
  apply PadicInt.toZModPow_eq_iff_ext.mp
  intro n
  ext x
  exact (DFunLike.congr_fun (hg n) x).trans (toZModPow_toPadic p m h n x).symm

@[simp] theorem toPadic_restrict (h : Nat.Coprime p m) (x : ProfiniteIntegerRing) :
    toPadic p m h (restrict m x) = ProfiniteIntegerRing.toPadic p x := by
  apply PadicInt.ext_of_toZModPow.mp
  intro n
  simp only [toZModPow_toPadic, ProfiniteIntegerRing.toZModPow_toPadic]
  rfl

end PrimeToProfiniteIntegerRing

end Langlands.Global

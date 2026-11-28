import Mathlib.LinearAlgebra.RootSystem.Base
import Langlands.LinearAlgebra.RootReflectionCoefficients

/-! # The Casimir identity for root data of type `E₈` -/

namespace Langlands.E8Casimir

open RootReflectionCoefficients

universe u v w

/-- In a reduced integral root datum of type `E₈` whose coroots span the cocharacter lattice,
the root-coroot sum is multiplication by `60` on the character lattice. -/
def IdentityStatement : Prop :=
  ∀ {ι : Type u} {M : Type v} {N : Type w} [AddCommGroup M] [AddCommGroup N]
    {P : RootDatum ι M N} [Fintype ι] [P.IsReduced] {s : Fin 8 → ι},
    (∀ i j, P.pairing (s i) (s j) = CartanMatrix.E 8 i j) →
    ∀ (b : P.Base), (∀ k, s k ∈ b.support) → (∀ i ∈ b.support, ∃ k, s k = i) →
    P.corootSpan ℤ = ⊤ →
    ∀ x : M, ∑ i, P.toLinearMap x (P.coroot i) • P.root i = (60 : ℤ) • x

/-- The positive root coefficient vectors in increasing order, with the coefficient of vertex
`k` in hexadecimal position `k` counted from the right. -/
private def positiveCodes : Array ℤ := #[
  0x00000001, 0x00000010, 0x00000100, 0x00000101, 0x00001000, 0x00001010,
  0x00001100, 0x00001101, 0x00001110, 0x00001111, 0x00010000, 0x00011000,
  0x00011010, 0x00011100, 0x00011101, 0x00011110, 0x00011111, 0x00012110,
  0x00012111, 0x00012211, 0x00100000, 0x00110000, 0x00111000, 0x00111010,
  0x00111100, 0x00111101, 0x00111110, 0x00111111, 0x00112110, 0x00112111,
  0x00112211, 0x00122110, 0x00122111, 0x00122211, 0x00123211, 0x00123221,
  0x01000000, 0x01100000, 0x01110000, 0x01111000, 0x01111010, 0x01111100,
  0x01111101, 0x01111110, 0x01111111, 0x01112110, 0x01112111, 0x01112211,
  0x01122110, 0x01122111, 0x01122211, 0x01123211, 0x01123221, 0x01222110,
  0x01222111, 0x01222211, 0x01223211, 0x01223221, 0x01233211, 0x01233221,
  0x01234221, 0x01234321, 0x01234322, 0x10000000, 0x11000000, 0x11100000,
  0x11110000, 0x11111000, 0x11111010, 0x11111100, 0x11111101, 0x11111110,
  0x11111111, 0x11112110, 0x11112111, 0x11112211, 0x11122110, 0x11122111,
  0x11122211, 0x11123211, 0x11123221, 0x11222110, 0x11222111, 0x11222211,
  0x11223211, 0x11223221, 0x11233211, 0x11233221, 0x11234221, 0x11234321,
  0x11234322, 0x12222110, 0x12222111, 0x12222211, 0x12223211, 0x12223221,
  0x12233211, 0x12233221, 0x12234221, 0x12234321, 0x12234322, 0x12333211,
  0x12333221, 0x12334221, 0x12334321, 0x12334322, 0x12344221, 0x12344321,
  0x12344322, 0x12345321, 0x12345322, 0x12345331, 0x12345332, 0x12345422,
  0x12345432, 0x12346432, 0x12356432, 0x12456432, 0x13456432, 0x23456432]

private def code (a : Fin 240) : ℤ :=
  if a.val < 120 then -(positiveCodes.getD (119 - a.val) 0)
  else positiveCodes.getD (a.val - 120) 0

private def place (k : Fin 8) : ℕ := 16 ^ k.val

private def coeff (a : Fin 240) (k : Fin 8) : ℤ :=
  let z := code a
  z.sign * ((z.natAbs / place k % 16 : ℕ) : ℤ)

private def coeffCode (c : Fin 8 → ℤ) : ℤ :=
  ∑ k, c k * (place k : ℤ)

/-- Search the half-open interval `[lo, hi)` for a code. The certificate checks all uses of
the resulting index against the required coefficient vector. -/
private def search (z : ℤ) : ℕ → ℕ → ℕ → Fin 240
  | 0, _, _ => 0
  | fuel + 1, lo, hi =>
    if lo < hi then
      let mid := (lo + hi) / 2
      let a := Fin.ofNat 240 mid
      if code a = z then a
      else if z < code a then search z fuel lo mid
      else search z fuel (mid + 1) hi
    else 0

private def findCode (z : ℤ) : Fin 240 := search z 8 0 240

private def pairing (a : Fin 240) (m : Fin 8) : ℤ :=
  ∑ k, coeff a k * CartanMatrix.E 8 k m

private def reflectedCode (a : Fin 240) (m : Fin 8) : ℤ :=
  code a - pairing a m * (place m : ℤ)

private def reflIndex (a : Fin 240) (m : Fin 8) : Fin 240 :=
  findCode (reflectedCode a m)

private def simpleIndex (m : Fin 8) : Fin 240 := findCode (place m : ℤ)

private def parentVertex (a : Fin 240) : Fin 8 :=
  ((List.finRange 8).find? fun m =>
    decide ((reflectedCode a m).natAbs ≤ (code a).natAbs ∧ reflectedCode a m ≠ code a)).getD 0

private def parent (a : Fin 240) : Fin 240 := reflIndex a (parentVertex a)

set_option maxHeartbeats 1600000 in
private theorem coeff_reflIndex (a : Fin 240) (m : Fin 8) :
    coeff (reflIndex a m) = reflect (CartanMatrix.E 8) m (coeff a) := by
  revert a m
  decide +kernel

private theorem coeff_neg (a : Fin 240) : coeff a.rev = -coeff a := by
  revert a
  decide +kernel

private theorem coeff_simpleIndex (m : Fin 8) :
    coeff (simpleIndex m) = Pi.single m 1 := by
  revert m
  decide +kernel

set_option maxHeartbeats 1600000 in
private theorem parent_spec (a : Fin 240) :
    coeff a = Pi.single (parentVertex a) 1 ∨
    coeff a = -Pi.single (parentVertex a) 1 ∨
    ((code (parent a)).natAbs < (code a).natAbs ∧
      coeff a = reflect (CartanMatrix.E 8) (parentVertex a) (coeff (parent a))) := by
  revert a
  decide +kernel

private theorem coeffCode_coeff (a : Fin 240) : coeffCode (coeff a) = code a := by
  revert a
  decide +kernel

private theorem code_lt (a : Fin 239) : code a.castSucc < code a.succ := by
  revert a
  decide +kernel

private theorem coeff_injective : Function.Injective coeff := by
  have hmono : StrictMono code := Fin.strictMono_iff_lt_succ.mpr code_lt
  intro a b hab
  apply hmono.injective
  simpa only [coeffCode_coeff] using congrArg coeffCode hab

set_option maxHeartbeats 1600000 in
private theorem sum_coeff_mul_pairing (k j : Fin 8) :
    ∑ a, coeff a k * pairing a j = if k = j then 60 else 0 := by
  revert k j
  decide +kernel

section RootDatum

variable {ι M N : Type*} [AddCommGroup M] [AddCommGroup N] (P : RootDatum ι M N)
  (s : Fin 8 → ι)

/-- The integral combination of the selected simple coroots. -/
private def cocomb (c : Fin 8 → ℤ) : N := ∑ k, c k • P.coroot (s k)

variable {P s}

private theorem combination_neg (c : Fin 8 → ℤ) :
    combination P s (-c) = -combination P s c := by
  simp [combination, neg_smul, Finset.sum_neg_distrib]

private theorem cocomb_neg (c : Fin 8 → ℤ) : cocomb P s (-c) = -cocomb P s c := by
  simp [cocomb, neg_smul, Finset.sum_neg_distrib]

private theorem combination_single (k : Fin 8) : combination P s (Pi.single k 1) = P.root (s k) := by
  simp [combination, Pi.single_apply, ite_smul]

private theorem cocomb_single (k : Fin 8) : cocomb P s (Pi.single k 1) = P.coroot (s k) := by
  simp [cocomb, Pi.single_apply, ite_smul]

variable (hA : ∀ i j, P.pairing (s i) (s j) = CartanMatrix.E 8 i j)
include hA

private theorem toLinearMap_combination_coroot (c : Fin 8 → ℤ) (m : Fin 8) :
    P.toLinearMap (combination P s c) (P.coroot (s m)) = ∑ k, c k * CartanMatrix.E 8 k m := by
  simp only [combination, map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    RootPairing.root_coroot_eq_pairing, hA, smul_eq_mul]

private theorem toLinearMap_root_cocomb (c : Fin 8 → ℤ) (m : Fin 8) :
    P.toLinearMap (P.root (s m)) (cocomb P s c) = ∑ k, c k * CartanMatrix.E 8 k m := by
  simp only [cocomb, map_sum, map_zsmul, RootPairing.root_coroot_eq_pairing, hA, smul_eq_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [← CartanMatrix.E_transpose 8, Matrix.transpose_apply, CartanMatrix.E_transpose]

/-- The same coefficient reflection works for roots and coroots, since the Cartan matrix is
symmetric. -/
private theorem reflectionPerm_spec {r : ι} {c : Fin 8 → ℤ}
    (h₁ : P.root r = combination P s c) (h₂ : P.coroot r = cocomb P s c) (m : Fin 8) :
    P.root (P.reflectionPerm (s m) r) = combination P s (reflect (CartanMatrix.E 8) m c) ∧
      P.coroot (P.reflectionPerm (s m) r) = cocomb P s (reflect (CartanMatrix.E 8) m c) := by
  constructor
  · have hp : P.pairing r (s m) = ∑ k, c k * CartanMatrix.E 8 k m := by
      rw [← RootPairing.root_coroot_eq_pairing, h₁, toLinearMap_combination_coroot hA]
    rw [P.root_reflectionPerm, P.reflection_apply_root, hp, h₁]
    simp [combination, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]
  · have hp : P.pairing (s m) r = ∑ k, c k * CartanMatrix.E 8 k m := by
      rw [← RootPairing.root_coroot_eq_pairing, h₂, toLinearMap_root_cocomb hA]
    rw [P.coroot_reflectionPerm, P.coreflection_apply_coroot, hp, h₂]
    simp [cocomb, reflect, sub_smul, Finset.sum_sub_distrib, ite_smul]

private theorem exists_index (a : Fin 240) :
    ∃ r : ι, P.root r = combination P s (coeff a) ∧ P.coroot r = cocomb P s (coeff a) := by
  induction h : (code a).natAbs using Nat.strong_induction_on generalizing a with
  | h n ih =>
    rcases parent_spec a with hpos | hneg | ⟨hlt, hc⟩
    · exact ⟨s (parentVertex a), by rw [hpos, combination_single], by rw [hpos, cocomb_single]⟩
    · let i := s (parentVertex a)
      refine ⟨P.reflectionPerm i i, ?_, ?_⟩
      · rw [P.root_reflectionPerm, P.reflection_apply_self, hneg, combination_neg, combination_single]
      · rw [P.coroot_reflectionPerm, P.coreflection_apply_self, hneg, cocomb_neg, cocomb_single]
    · obtain ⟨r, h₁, h₂⟩ := ih _ (h ▸ hlt) (parent a) rfl
      rw [hc]
      exact ⟨_, reflectionPerm_spec hA h₁ h₂ (parentVertex a)⟩

private theorem exists_coeff [Finite ι] [P.IsReduced] (b : P.Base)
    (hsupp : ∀ i ∈ b.support, ∃ k, s k = i) (r : ι) :
    ∃ a, P.root r = combination P s (coeff a) ∧ P.coroot r = cocomb P s (coeff a) := by
  refine b.induction_reflect (p := fun r => ∃ a, P.root r = combination P s (coeff a) ∧
    P.coroot r = cocomb P s (coeff a)) r ?_ ?_ ?_
  · rintro i ⟨a, h₁, h₂⟩
    refine ⟨a.rev, ?_, ?_⟩
    · rw [P.root_reflectionPerm, P.reflection_apply_self, h₁, coeff_neg, combination_neg]
    · rw [P.coroot_reflectionPerm, P.coreflection_apply_self, h₂, coeff_neg, cocomb_neg]
  · intro i hi
    obtain ⟨k, rfl⟩ := hsupp i hi
    exact ⟨simpleIndex k, by rw [coeff_simpleIndex, combination_single],
      by rw [coeff_simpleIndex, cocomb_single]⟩
  · rintro i j ⟨a, h₁, h₂⟩ hj
    obtain ⟨m, rfl⟩ := hsupp j hj
    refine ⟨reflIndex a m, ?_⟩
    rw [coeff_reflIndex]
    exact reflectionPerm_spec hA h₁ h₂ m

private theorem injective_of_cartan : Function.Injective s := by
  intro i j hij
  by_contra hne
  have h := hA i j
  rw [hij, P.pairing_same] at h
  have := CartanMatrix.E_off_diag_nonpos 8 i j hne
  omega

end RootDatum

theorem sum_toLinearMap_coroot_smul_root : IdentityStatement.{u, v, w} := by
  intro ι M N _ _ P _ _ s hA b hs hsupp hspan x
  classical
  choose f hf₁ hf₂ using exists_index (P := P) (s := s) hA
  have hlin : LinearIndependent ℤ fun k => P.root (s k) :=
    b.linearIndepOn_root.comp (fun k => ⟨s k, hs k⟩)
      (fun _ _ h => injective_of_cartan hA (congrArg Subtype.val h))
  have hinj : Function.Injective f := by
    intro a a' h
    apply coeff_injective
    funext k
    have heq := congrArg P.root h
    rw [hf₁, hf₁] at heq
    exact Fintype.linearIndependent_iffₛ.mp hlin _ _ heq k
  have hsurj : Function.Surjective f := by
    intro r
    obtain ⟨a, hr, -⟩ := exists_coeff hA b hsupp r
    exact ⟨a, P.root.injective (by rw [hf₁, hr])⟩
  have hsum : ∑ i, P.toLinearMap x (P.coroot i) • P.root i =
      ∑ a, P.toLinearMap x (cocomb P s (coeff a)) • combination P s (coeff a) :=
    (Fintype.sum_bijective f ⟨hinj, hsurj⟩ _ _ (fun a => by rw [hf₁, hf₂])).symm
  rw [hsum]
  apply (LinearMap.IsPerfPair.bijective_left P.toLinearMap).1
  have hspan' : Submodule.span ℤ (P.coroot '' b.support) = ⊤ := by
    rwa [b.span_int_coroot_support]
  refine LinearMap.ext_on hspan' ?_
  rintro _ ⟨i, hi, rfl⟩
  obtain ⟨j, rfl⟩ := hsupp i hi
  simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply,
    toLinearMap_combination_coroot hA, smul_eq_mul, cocomb]
  calc ∑ a, (∑ k, coeff a k * P.toLinearMap x (P.coroot (s k))) *
        ∑ l, coeff a l * CartanMatrix.E 8 l j
      = ∑ k, P.toLinearMap x (P.coroot (s k)) * ∑ a, coeff a k * pairing a j := by
        unfold pairing
        simp_rw [Finset.sum_mul, Finset.mul_sum]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun a _ =>
          Finset.sum_congr rfl fun l _ => by ring
    _ = 60 * P.toLinearMap x (P.coroot (s j)) := by
        simp_rw [sum_coeff_mul_pairing, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
          ite_true]
        ring

end Langlands.E8Casimir

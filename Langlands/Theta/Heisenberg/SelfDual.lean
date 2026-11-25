import Langlands.Theta.Heisenberg.Representation
import Langlands.Theta.Heisenberg.SelfDualSubgroup

/-!
# Self-dual subgroups: the regular representation and the orthogonal of a set

Let `B` be a bilinear form on a module `W` over a commutative ring `R` with `2` invertible and `ψ`
an additive character of `R`.

* `regular B ψ` is the representation of `HeisenbergGroup B` on all functions on `W` induced from
  the character `ψ` of the centre: `(w, t)` acts by `f ↦ (z ↦ ψ t * ψ (⅟2 * B z w) * f (z + w))`.
  It has central character `ψ`.
* `charOrthogonal B ψ T = {x | ψ (B x t) = 1 for all t ∈ T}` is the orthogonal of a set `T` for
  the pairing `ψ ∘ B` (GKT (1.2)); a subgroup `A` with `charOrthogonal B ψ A = A` is self-dual.
* For alternating `B`, `ψ(½ B)` is an alternating bicharacter whose orthogonals are the sets
  `charOrthogonal B ψ T`, and in a representation with central character `ψ` the elements `(x, 0)`
  act by a projective representation of `W` with cocycle `ψ(½ B)`: the setting of
  `Langlands.Theta.Heisenberg.SelfDualSubgroup`.
-/

noncomputable section

namespace Langlands.HeisenbergGroup

universe u v w

open Internal

section Regular

variable {R : Type u} [CommRing R] [Invertible (2 : R)] {W : Type v} [AddCommGroup W] [Module R W]
  (B : LinearMap.BilinForm R W) (ψ : AddChar R ℂ)

/-- The translation operators of the regular representation:
`regularFun B ψ w f z = ψ (⅟2 * B z w) * f (z + w)`. -/
def regularFun (w : W) : Module.End ℂ (W → ℂ) :=
  translate (fun x y => ψ (⅟2 * B x y)) w

/-- The value of `regularFun B ψ w f` at `z`. -/
@[simp] theorem regularFun_apply (w : W) (f : W → ℂ) (z : W) :
    regularFun B ψ w f z = ψ (⅟2 * B z w) * f (z + w) := rfl

/-- `regularFun B ψ 0 = 1`. -/
theorem regularFun_zero : regularFun B ψ 0 = 1 := by
  ext f z; simp

/-- `regularFun B ψ x ∘ regularFun B ψ y = ψ(½ B(x, y)) regularFun B ψ (x + y)`. -/
theorem regularFun_mul (x y : W) :
    regularFun B ψ x * regularFun B ψ y = ψ (⅟2 * B x y) • regularFun B ψ (x + y) := by
  ext f z
  simp only [Module.End.mul_apply, regularFun_apply, LinearMap.smul_apply, Pi.smul_apply,
    smul_eq_mul, map_add, LinearMap.add_apply, mul_add, AddChar.map_add_eq_mul, add_assoc]
  ring

/-- The representation of the Heisenberg group induced from the character `ψ` of its centre,
on all functions on `W`: `(w, t)` acts by `ψ t • regularFun B ψ w`. -/
def regular : Representation ℂ (HeisenbergGroup B) (W → ℂ) where
  toFun g := ψ g.cen • regularFun B ψ g.vec
  map_one' := by simp [regularFun_zero]
  map_mul' g h := by
    simp only [mul_cen, mul_vec, AddChar.map_add_eq_mul, smul_mul_smul, regularFun_mul, smul_smul]

/-- `(w, t)` acts in `regular B ψ` by `ψ t • regularFun B ψ w`. -/
theorem regular_apply (g : HeisenbergGroup B) : regular B ψ g = ψ g.cen • regularFun B ψ g.vec :=
  rfl

/-- `(w, 0)` acts in `regular B ψ` by `regularFun B ψ w`. -/
@[simp] theorem regular_ofVec (w : W) : regular B ψ (ofVec w) = regularFun B ψ w := by
  simp [regular_apply]

/-- The regular representation has central character `ψ`. -/
theorem hasCentralCharacter_regular : HasCentralCharacter (regular B ψ) ψ := fun t f => by
  simp [regular_apply, regularFun_zero]

omit [Invertible (2 : R)] in
/-- The orthogonal `{x | ψ (B x t) = 1 for all t ∈ T}` of a set `T` for the pairing `ψ ∘ B`. -/
def charOrthogonal (T : Set W) : AddSubgroup W where
  carrier := {x | ∀ t ∈ T, ψ (B x t) = 1}
  add_mem' := fun {a b} ha hb t ht => by
    rw [map_add, LinearMap.add_apply, AddChar.map_add_eq_mul, ha t ht, hb t ht, mul_one]
  zero_mem' := fun t _ => by simp
  neg_mem' := fun {a} ha t ht => by
    rw [map_neg, LinearMap.neg_apply, AddChar.map_neg_eq_inv, ha t ht, inv_one]

omit [Invertible (2 : R)] in
/-- Membership in `charOrthogonal`. -/
theorem mem_charOrthogonal {T : Set W} {x : W} :
    x ∈ charOrthogonal B ψ T ↔ ∀ t ∈ T, ψ (B x t) = 1 := Iff.rfl

variable {B ψ}

/-- For alternating `B`, `ψ(½ B)` is an alternating bicharacter. -/
theorem isAlternatingBicharacter_psi (hB : B.IsAlt) :
    IsAlternatingBicharacter fun x y => ψ (⅟2 * B x y) where
  map_add_left x y z := by rw [← AddChar.map_add_eq_mul, map_add, LinearMap.add_apply, mul_add]
  map_add_right x y z := by rw [← AddChar.map_add_eq_mul, map_add, mul_add]
  apply_self x := by rw [hB.self_eq_zero]; simp

omit [Invertible (2 : R)] in
/-- `ψ(½ t)² = ψ t`. -/
theorem psi_half_sq [Invertible (2 : R)] (t : R) : ψ (⅟2 * t) ^ 2 = ψ t := by
  rw [pow_two, ← AddChar.map_add_eq_mul, ← add_mul, ← two_mul, mul_invOf_self, one_mul]

/-- The orthogonal for the bicharacter `ψ(½ B)` (with squares) is `charOrthogonal B ψ`. -/
theorem orthogonal_psi_eq (hB : B.IsAlt) (T : Set W) :
    (isAlternatingBicharacter_psi (ψ := ψ) hB).orthogonal T = charOrthogonal B ψ T := by
  ext x
  simp only [IsAlternatingBicharacter.mem_orthogonal, mem_charOrthogonal, psi_half_sq]

/-- With a central character `ψ`, the elements `(x, 0)` act by a projective representation of `W`
with cocycle `ψ (⅟2 * B x y)`. -/
theorem isProjectiveRep_of_hasCentralCharacter {M : Type w} [AddCommGroup M] [Module ℂ M]
    {π : Representation ℂ (HeisenbergGroup B) M} (hπ : HasCentralCharacter π ψ) :
    IsProjectiveRep (fun x y => ψ (⅟2 * B x y)) fun x => π (ofVec x) where
  apply_zero v := by simp
  apply_apply x y v := by
    rw [← Module.End.mul_apply, ← map_mul, ofVec_mul_ofVec, map_mul, Module.End.mul_apply, hπ]

end Regular

section Subspace

variable {F : Type u} [Field F] {W : Type v} [AddCommGroup W] [Module F W]
  (B : LinearMap.BilinForm F W) {ψ : AddChar F ℂ}

/-- **The orthogonal of a subspace** (GKT (1.2) for a subspace `L`): for a non-trivial character
`ψ`, `x` is orthogonal to `L` for `ψ ∘ B` if and only if `B x l = 0` for all `l ∈ L`. In particular
a subspace is self-dual exactly when it is its own `B`-orthogonal (a Lagrangian, GKT p. 25). -/
theorem mem_charOrthogonal_submodule (hψ : ψ ≠ 1) (L : Submodule F W) {x : W} :
    x ∈ charOrthogonal B ψ (L : Set W) ↔ ∀ l ∈ L, B x l = 0 := by
  constructor
  · intro h l hl
    by_contra hne
    apply hψ
    ext t
    have := h ((t / B x l) • l) (L.smul_mem _ hl)
    rw [LinearMap.map_smul, smul_eq_mul, div_mul_cancel₀ t hne] at this
    simpa using this
  · intro h l hl
    rw [h l hl, AddChar.map_zero_eq_one]

end Subspace

end Langlands.HeisenbergGroup

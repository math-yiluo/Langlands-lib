import Langlands.Weil.Representation.Invariants
import Langlands.WeilDeligne.InductionAlong
import Mathlib.Tactic

/-!
# Degree coordinates on inertia invariants of coinduction

The construction is algebraic and works for arbitrary groups with compatible
integer degree homomorphisms.
-/

noncomputable section

namespace Langlands.FiniteRepresentation.InductionDegree

universe uK uG uH uV

variable {K : Type uK} [Field K]
variable {G : Type uG} {H : Type uH} [Group G] [Group H]
variable {V : Type uV} [AddCommGroup V] [Module K V]

/-- An integer-valued notation for a multiplicative degree homomorphism. -/
def intDegree {L : Type*} [Group L] (d : L →* Multiplicative ℤ) (x : L) : ℤ :=
  (d x).toAdd

@[simp] theorem intDegree_one {L : Type*} [Group L]
    (d : L →* Multiplicative ℤ) : intDegree d 1 = 0 := by
  simp [intDegree]

@[simp] theorem intDegree_mul {L : Type*} [Group L]
    (d : L →* Multiplicative ℤ) (x y : L) :
    intDegree d (x * y) = intDegree d x + intDegree d y := by
  simp [intDegree]

@[simp] theorem intDegree_inv {L : Type*} [Group L]
    (d : L →* Multiplicative ℤ) (x : L) :
    intDegree d x⁻¹ = -intDegree d x := by
  simp [intDegree]

@[simp] theorem intDegree_zpow {L : Type*} [Group L]
    (d : L →* Multiplicative ℤ) (x : L) (n : ℤ) :
    intDegree d (x ^ n) = n * intDegree d x := by
  simp [intDegree]

theorem mem_ker_iff {L : Type*} [Group L]
    (d : L →* Multiplicative ℤ) (x : L) :
    x ∈ d.ker ↔ intDegree d x = 0 := by
  change d x = 1 ↔ (d x).toAdd = 0
  exact Multiplicative.toAdd.injective.eq_iff.symm

/-- The residue in the decomposition `m = f*q - r`, `0 ≤ r < f`. -/
def residue (f : ℕ) (hf : 0 < f) (m : ℤ) : Fin f :=
  ⟨((-m) % (f : ℤ)).toNat, by
    have h₀ := Int.emod_nonneg (-m) (show (f : ℤ) ≠ 0 by omega)
    have h₁ := Int.emod_lt_of_pos (-m) (show (0 : ℤ) < f by omega)
    omega⟩

/-- The quotient in the decomposition `m = f*q - r`. -/
def quotient (f : ℕ) (m : ℤ) : ℤ := -((-m) / (f : ℤ))

theorem quotient_residue (f : ℕ) (hf : 0 < f) (m : ℤ) :
    (f : ℤ) * quotient f m - (residue f hf m : ℕ) = m := by
  have h₀ := Int.emod_nonneg (-m) (show (f : ℤ) ≠ 0 by omega)
  have h₁ := Int.emod_add_mul_ediv (-m) (f : ℤ)
  simp only [quotient, residue]
  rw [Int.toNat_of_nonneg h₀]
  rw [mul_neg]
  omega

theorem residue_add_mul (f : ℕ) (hf : 0 < f) (m k : ℤ) :
    residue f hf (m + k * f) = residue f hf m := by
  apply Fin.ext
  simp only [residue]
  congr 1
  rw [show -(m + k * (f : ℤ)) = -m + (-k) * f by ring,
    Int.add_mul_emod_self_right]

theorem quotient_add_mul (f : ℕ) (hf : 0 < f) (m k : ℤ) :
    quotient f (m + k * f) = quotient f m + k := by
  simp only [quotient]
  rw [show -(m + k * (f : ℤ)) = -m + (-k) * f by ring,
    Int.add_mul_ediv_right _ _ (show (f : ℤ) ≠ 0 by omega)]
  ring

@[simp] theorem residue_neg (f : ℕ) (hf : 0 < f) (i : Fin f) :
    residue f hf (-(i : ℤ)) = i := by
  apply Fin.ext
  simp only [residue, neg_neg]
  rw [Int.emod_eq_of_lt (by omega) (by exact_mod_cast i.isLt)]
  simp

@[simp] theorem quotient_neg (f : ℕ) (i : Fin f) :
    quotient f (-(i : ℤ)) = 0 := by
  simp only [quotient, neg_neg]
  rw [Int.ediv_eq_zero_of_lt (by omega) (by exact_mod_cast i.isLt), neg_zero]

variable (dG : G →* Multiplicative ℤ) (dH : H →* Multiplicative ℤ)
variable (ι : H →* G) (ρ : Representation K H V)

/-- Source inertia invariants. -/
abbrev Source := Representation.invariants (ρ.comp dH.ker.subtype)

/-- Ambient inertia invariants in the actual coinduced function space. -/
abbrev Target :=
  Representation.invariants ((Representation.coind ι ρ).comp dG.ker.subtype)

theorem source_action_eq_of_degree_eq (u : Source dH ρ) {h h' : H}
    (hh : intDegree dH h = intDegree dH h') :
    ρ h u.val = ρ h' u.val := by
  have hz : h'⁻¹ * h ∈ dH.ker := by
    rw [mem_ker_iff]
    simp [hh]
  calc
    ρ h u.val = ρ (h' * (h'⁻¹ * h)) u.val := by simp
    _ = ρ h' (ρ (h'⁻¹ * h) u.val) := by rw [map_mul]; rfl
    _ = ρ h' u.val := congrArg (ρ h') (u.property ⟨_, hz⟩)

theorem target_value_eq_of_degree_eq (u : Target dG ι ρ) {x y : G}
    (hxy : intDegree dG x = intDegree dG y) :
    u.val.val x = u.val.val y := by
  have hz : y⁻¹ * x ∈ dG.ker := by
    rw [mem_ker_iff]
    simp [hxy]
  have hz' := congrArg (fun v : Representation.coindV ι ρ => v.val y)
    (u.property ⟨_, hz⟩)
  change u.val.val (y * (y⁻¹ * x)) = u.val.val y at hz'
  simpa using hz'

variable (f : ℕ) (hf : 0 < f)
variable (hdeg : ∀ h : H, intDegree dG (ι h) = (f : ℤ) * intDegree dH h)

include hdeg in
theorem target_value_mem_source (u : Target dG ι ρ) (x : G) :
    u.val.val x ∈ Representation.invariants (ρ.comp dH.ker.subtype) := by
  intro j
  change ρ j.val (u.val.val x) = u.val.val x
  rw [← u.val.property]
  apply target_value_eq_of_degree_eq
  rw [intDegree_mul, hdeg, (mem_ker_iff dH j.val).mp j.property]
  ring

variable (Φ : G) (hΦ : intDegree dG Φ = 1)
variable (η : H) (hη : intDegree dH η = 1)

/-- Evaluation on the negative powers of an arbitrary degree-one element. -/
def coordinatesMap : Target dG ι ρ →ₗ[K] (Fin f → Source dH ρ) where
  toFun u i := ⟨u.val.val (Φ ^ (-(i : ℤ))),
    target_value_mem_source dG dH ι ρ f hdeg u _⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

include hdeg hΦ hη in
theorem target_value_formula (u : Target dG ι ρ) (x : G) :
    u.val.val x =
      ρ (η ^ quotient f (intDegree dG x))
        (u.val.val (Φ ^ (-(residue f hf (intDegree dG x) : ℤ)))) := by
  rw [← u.val.property]
  apply target_value_eq_of_degree_eq
  simp only [intDegree_mul, hdeg, intDegree_zpow, hη, hΦ, mul_one]
  have h := quotient_residue f hf (intDegree dG x)
  omega

include hf hΦ η hη in
theorem coordinatesMap_injective :
    Function.Injective (coordinatesMap dG dH ι ρ f hdeg Φ) := by
  intro u v huv
  apply Subtype.ext
  apply Subtype.ext
  funext x
  rw [target_value_formula dG dH ι ρ f hf hdeg Φ hΦ η hη u x,
    target_value_formula dG dH ι ρ f hf hdeg Φ hΦ η hη v x]
  congr 1
  exact congrArg Subtype.val (congrFun huv (residue f hf (intDegree dG x)))

/-- Reconstruction of an equivariant function from the finite list of values. -/
def fromCoordinates (v : Fin f → Source dH ρ) : Target dG ι ρ := by
  let z (x : G) : V :=
    ρ (η ^ quotient f (intDegree dG x)) (v (residue f hf (intDegree dG x))).val
  have hz (h : H) (x : G) : z (ι h * x) = ρ h (z x) := by
    have hd : intDegree dG (ι h * x) =
        intDegree dG x + intDegree dH h * (f : ℤ) := by
      rw [intDegree_mul, hdeg]
      ring
    dsimp [z]
    rw [hd, residue_add_mul, quotient_add_mul f hf]
    rw [← Module.End.mul_apply, ← map_mul]
    apply source_action_eq_of_degree_eq
    simp only [intDegree_zpow, intDegree_mul, hη, mul_one]
    ring
  refine ⟨⟨z, hz⟩, ?_⟩
  intro j
  apply Subtype.ext
  funext x
  change z (x * j.val) = z x
  have hd : intDegree dG (x * j.val) = intDegree dG x := by
    rw [intDegree_mul, (mem_ker_iff dG j.val).mp j.property, add_zero]
  dsimp [z]
  rw [hd]

include hΦ in
theorem coordinatesMap_fromCoordinates (v : Fin f → Source dH ρ) :
    coordinatesMap dG dH ι ρ f hdeg Φ
      (fromCoordinates dG dH ι ρ f hf hdeg η hη v) = v := by
  funext i
  apply Subtype.ext
  change ρ (η ^ quotient f (intDegree dG (Φ ^ (-(i : ℤ)))))
      (v (residue f hf (intDegree dG (Φ ^ (-(i : ℤ)))))).val = (v i).val
  simp only [intDegree_zpow, hΦ, mul_one, quotient_neg, residue_neg,
    zpow_zero, map_one, Module.End.one_apply]

/-- The actual invariant coinduced space is a list of `f` source invariant vectors. -/
def coordinates : Target dG ι ρ ≃ₗ[K] (Fin f → Source dH ρ) :=
  LinearEquiv.ofBijective (coordinatesMap dG dH ι ρ f hdeg Φ)
    ⟨coordinatesMap_injective dG dH ι ρ f hf hdeg Φ hΦ η hη,
      fun v => ⟨fromCoordinates dG dH ι ρ f hf hdeg η hη v,
        coordinatesMap_fromCoordinates dG dH ι ρ f hf hdeg Φ hΦ η hη v⟩⟩

end Langlands.FiniteRepresentation.InductionDegree

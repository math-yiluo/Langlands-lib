import Langlands.Global.ArchimedeanCartanSymmetricAlgebra

/-! # Actual fixed subalgebras and Cartan invariant restriction -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Fixed elements in the full symmetric algebra for the full standard compact group. -/
def lieSymmetricCompactInvariants : Subalgebra ℂ (LieSymmetricAlgebra K n) where
  carrier := {P | ∀ k : standardInfiniteCompact K n,
    lieSymmetricConjugation K n k.val P = P}
  zero_mem' := by intro k; exact map_zero _
  one_mem' := by intro k; exact map_one _
  add_mem' := by intro P Q hP hQ k; simp only [map_add, hP k, hQ k]
  mul_mem' := by intro P Q hP hQ k; simp only [map_mul, hP k, hQ k]
  algebraMap_mem' := by intro z k; exact AlgEquiv.commutes _ z

/-- Fixed elements in the complementary symmetric algebra for the full compact group. -/
def cartanSymmetricCompactInvariants : Subalgebra ℂ (CartanSymmetricAlgebra K n) where
  carrier := {P | ∀ k : standardInfiniteCompact K n,
    cartanSymmetricConjugation K n k P = P}
  zero_mem' := by intro k; exact map_zero _
  one_mem' := by intro k; exact map_one _
  add_mem' := by intro P Q hP hQ k; simp only [map_add, hP k, hQ k]
  mul_mem' := by intro P Q hP hQ k; simp only [map_mul, hP k, hQ k]
  algebraMap_mem' := by intro z k; exact AlgEquiv.commutes _ z

/-- Fixed elements in the full symmetric algebra under every actual archimedean group element. -/
def lieSymmetricGroupInvariants : Subalgebra ℂ (LieSymmetricAlgebra K n) where
  carrier := {P | ∀ g : InfiniteAdelicGL K n, lieSymmetricConjugation K n g P = P}
  zero_mem' := by intro g; exact map_zero _
  one_mem' := by intro g; exact map_one _
  add_mem' := by intro P Q hP hQ g; simp only [map_add, hP g, hQ g]
  mul_mem' := by intro P Q hP hQ g; simp only [map_mul, hP g, hQ g]
  algebraMap_mem' := by intro z g; exact AlgEquiv.commutes _ z

@[simp]
theorem mem_lieSymmetricCompactInvariants (P : LieSymmetricAlgebra K n) :
    P ∈ lieSymmetricCompactInvariants K n ↔
      ∀ k : standardInfiniteCompact K n, lieSymmetricConjugation K n k.val P = P := Iff.rfl

@[simp]
theorem mem_cartanSymmetricCompactInvariants (P : CartanSymmetricAlgebra K n) :
    P ∈ cartanSymmetricCompactInvariants K n ↔
      ∀ k : standardInfiniteCompact K n, cartanSymmetricConjugation K n k P = P := Iff.rfl

@[simp]
theorem mem_lieSymmetricGroupInvariants (P : LieSymmetricAlgebra K n) :
    P ∈ lieSymmetricGroupInvariants K n ↔
      ∀ g : InfiniteAdelicGL K n, lieSymmetricConjugation K n g P = P := Iff.rfl

/-- The actual complementary inclusion restricted to compact fixed elements. -/
def cartanCompactInvariantInclusion :
    cartanSymmetricCompactInvariants K n →ₐ[ℂ] lieSymmetricCompactInvariants K n :=
  ((cartanSymmetricInclusion K n).comp
    (cartanSymmetricCompactInvariants K n).val).codRestrict
      (lieSymmetricCompactInvariants K n) (by
        intro P k
        change lieSymmetricConjugation K n k.val (cartanSymmetricInclusion K n P.val) =
          cartanSymmetricInclusion K n P.val
        rw [← cartanSymmetricInclusion_conjugation, P.property k])

/-- The actual complementary projection restricted to compact fixed elements. -/
def cartanCompactInvariantProjection :
    lieSymmetricCompactInvariants K n →ₐ[ℂ] cartanSymmetricCompactInvariants K n :=
  ((cartanSymmetricProjection K n).comp
    (lieSymmetricCompactInvariants K n).val).codRestrict
      (cartanSymmetricCompactInvariants K n) (by
        intro P k
        change cartanSymmetricConjugation K n k (cartanSymmetricProjection K n P.val) =
          cartanSymmetricProjection K n P.val
        rw [← cartanSymmetricProjection_conjugation, P.property k])

@[simp]
theorem cartanCompactInvariantInclusion_coe (P : cartanSymmetricCompactInvariants K n) :
    (cartanCompactInvariantInclusion K n P : LieSymmetricAlgebra K n) =
      cartanSymmetricInclusion K n P.val := rfl

@[simp]
theorem cartanCompactInvariantProjection_coe (P : lieSymmetricCompactInvariants K n) :
    (cartanCompactInvariantProjection K n P : CartanSymmetricAlgebra K n) =
      cartanSymmetricProjection K n P.val := rfl

@[simp]
theorem cartanCompactInvariantProjection_inclusion (P : cartanSymmetricCompactInvariants K n) :
    cartanCompactInvariantProjection K n (cartanCompactInvariantInclusion K n P) = P := by
  apply Subtype.ext
  exact cartanSymmetricProjection_inclusion K n P.val

theorem cartanCompactInvariantInclusion_injective :
    Function.Injective (cartanCompactInvariantInclusion K n) :=
  Function.LeftInverse.injective (cartanCompactInvariantProjection_inclusion K n)

theorem cartanCompactInvariantProjection_surjective :
    Function.Surjective (cartanCompactInvariantProjection K n) :=
  Function.RightInverse.surjective (cartanCompactInvariantProjection_inclusion K n)

theorem lieSymmetricGroupInvariants_le_compact :
    lieSymmetricGroupInvariants K n ≤ lieSymmetricCompactInvariants K n := by
  intro P hP k
  exact hP k.val

/-- Forget invariance under group elements outside the standard compact subgroup. -/
def lieSymmetricGroupToCompactInvariants :
    lieSymmetricGroupInvariants K n →ₐ[ℂ] lieSymmetricCompactInvariants K n :=
  Subalgebra.inclusion (lieSymmetricGroupInvariants_le_compact K n)

/-- Restrict full-group fixed symmetric tensors to the actual Cartan complement. -/
def cartanGroupInvariantRestriction :
    lieSymmetricGroupInvariants K n →ₐ[ℂ] cartanSymmetricCompactInvariants K n :=
  (cartanCompactInvariantProjection K n).comp (lieSymmetricGroupToCompactInvariants K n)

@[simp]
theorem cartanGroupInvariantRestriction_coe (P : lieSymmetricGroupInvariants K n) :
    (cartanGroupInvariantRestriction K n P : CartanSymmetricAlgebra K n) =
      cartanSymmetricProjection K n P.val := rfl

end Langlands.Global.ArchimedeanGL

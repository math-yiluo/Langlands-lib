import Langlands.BaseChange.TwistedCharacter
import Langlands.Representation.Smooth.Schur.Proof
import Mathlib.Data.ZMod.Basic
import Mathlib.GroupTheory.SemidirectProduct

/-! # Extension of a twisted representation to a cyclic semidirect product -/

noncomputable section

namespace Langlands.BaseChange

open scoped MonoidAlgebra

universe uG uV u v

abbrev CyclicComponent (l : ℕ) := Multiplicative (ZMod l)

/-- The distinguished generator of the component group. -/
def cyclicGenerator (l : ℕ) : CyclicComponent l :=
  Multiplicative.ofAdd (1 : ZMod l)

private theorem pow_mod_period {M : Type*} [Monoid M] {x : M} {l : ℕ}
    (hx : x ^ l = 1) (k : ℕ) : x ^ (k % l) = x ^ k := by
  conv_rhs => rw [← Nat.mod_add_div k l]
  rw [pow_add, pow_mul, hx, one_pow, mul_one]

/-- A monoid element of period dividing `l` defines an action of the cyclic group of order
`l` by its powers. -/
def cyclicPowerHom {M : Type*} [Monoid M] {l : ℕ} [NeZero l] (x : M)
    (hx : x ^ l = 1) : CyclicComponent l →* M where
  toFun c := x ^ c.toAdd.val
  map_one' := by
    change x ^ (0 : ZMod l).val = 1
    rw [ZMod.val_zero, pow_zero]
  map_mul' c d := by
    change x ^ (c.toAdd + d.toAdd).val = x ^ c.toAdd.val * x ^ d.toAdd.val
    rw [ZMod.val_add, pow_mod_period hx, pow_add]

@[simp]
theorem cyclicPowerHom_generator {M : Type*} [Monoid M] {l : ℕ} [NeZero l] {x : M}
    (hx : x ^ l = 1) : cyclicPowerHom x hx (cyclicGenerator l) = x := by
  change x ^ (1 : ZMod l).val = x
  rw [ZMod.val_one_eq_one_mod, pow_mod_period hx, pow_one]

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

private theorem intertwiner_pow_mul (ρ : Representation ℂ G V) (θ : MulAut G)
    (B : Module.End ℂ V) (hB : ∀ g, B * ρ g = ρ (θ g) * B) (k : ℕ) (g : G) :
    B ^ k * ρ g = ρ ((θ ^ k) g) * B ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [show (θ ^ (k + 1)) g = θ ((θ ^ k) g) by rw [pow_succ']; rfl]
    simp only [pow_succ' B k, mul_assoc, ih]
    rw [← mul_assoc, hB, mul_assoc]

/-- Scaling a twisting isomorphism gives one whose `l`th power is the identity, by
admissible Schur's lemma and extraction of an `l`th root over `ℂ`. -/
theorem exists_normalizedCyclicIntertwiner [TopologicalSpace G] {l : ℕ} (hl : 0 < l)
    (θ : MulAut G) (hθ : θ ^ l = 1) (ρ : Representation ℂ G V) (hρ : IsAdmissible ρ)
    (hi : ρ.IsIrreducible) (A : ρ.Equiv (ρ.comp θ.toMonoidHom)) :
    ∃ c : ℂ, c ≠ 0 ∧ ∃ B : ρ.Equiv (ρ.comp θ.toMonoidHom),
      B.toLinearMap ^ l = 1 ∧ A.toLinearMap = c • B.toLinearMap := by
  have hcov (g : G) : A.toLinearMap * ρ g = ρ (θ g) * A.toLinearMap :=
    A.isIntertwining' g
  let T : ρ.IntertwiningMap ρ :=
    { toLinearMap := A.toLinearMap ^ l
      isIntertwining' := fun g => by
        change A.toLinearMap ^ l * ρ g = ρ g * A.toLinearMap ^ l
        have heq := intertwiner_pow_mul ρ θ A.toLinearMap hcov l g
        simpa [hθ] using heq }
  obtain ⟨a, ha, _⟩ := admissibleSchur_scalarEndomorphism ρ hρ hi T
  have hpower : A.toLinearMap ^ l = a • (1 : Module.End ℂ V) :=
    congrArg Representation.IntertwiningMap.toLinearMap ha
  have ha₀ : a ≠ 0 := by
    let _ := hi
    let _ : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
    have hinj : Function.Injective (A.toLinearMap ^ l : Module.End ℂ V) := by
      rw [Module.End.coe_pow]
      exact A.injective.iterate l
    intro ha₀
    rw [ha₀, zero_smul] at hpower
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    exact hx (hinj (by rw [hpower]; simp))
  obtain ⟨c, hc⟩ := IsAlgClosed.exists_pow_nat_eq a hl
  have hc₀ : c ≠ 0 := fun h => ha₀ (by simpa [h, zero_pow hl.ne'] using hc.symm)
  let B : ρ.Equiv (ρ.comp θ.toMonoidHom) :=
    { toLinearEquiv := A.toLinearEquiv.trans (LinearEquiv.smulOfNeZero ℂ V c⁻¹ (inv_ne_zero hc₀))
      isIntertwining' := fun g => by
        ext w
        change c⁻¹ • A (ρ g w) = ρ (θ g) (c⁻¹ • A w)
        rw [map_smul]
        exact congrArg (c⁻¹ • ·) (DFunLike.congr_fun (hcov g) w) }
  have hB : B.toLinearMap = c⁻¹ • A.toLinearMap := rfl
  refine ⟨c, hc₀, B, ?_, ?_⟩
  · rw [hB, smul_pow, hpower, smul_smul, inv_pow, hc, inv_mul_cancel₀ ha₀, one_smul]
  · rw [hB, smul_inv_smul₀ hc₀]

variable {l : ℕ} [NeZero l]

/-- The representation acting by `ρ(g) B^i` on `(g, i)`. The covariance relation gives
multiplicativity and `B^l = 1` makes the formula independent of the cyclic exponent. -/
def cyclicExtension (θ : MulAut G) (hθ : θ ^ l = 1)
    (ρ : Representation ℂ G V) (B : Module.End ℂ V) (hB : B ^ l = 1)
    (hcov : ∀ g, B * ρ g = ρ (θ g) * B) :
    Representation ℂ (G ⋊[cyclicPowerHom θ hθ] CyclicComponent l) V where
  toFun x := ρ x.left * cyclicPowerHom B hB x.right
  map_one' := by simp
  map_mul' x y := by
    simp only [SemidirectProduct.mul_left, SemidirectProduct.mul_right, map_mul]
    have heq := intertwiner_pow_mul ρ θ B hcov x.right.toAdd.val y.left
    change cyclicPowerHom B hB x.right * ρ y.left =
      ρ (cyclicPowerHom θ hθ x.right y.left) * cyclicPowerHom B hB x.right at heq
    simp only [mul_assoc]
    rw [← mul_assoc (ρ (cyclicPowerHom θ hθ x.right y.left)), ← heq, mul_assoc]

@[simp]
theorem cyclicExtension_apply (θ : MulAut G) (hθ : θ ^ l = 1)
    (ρ : Representation ℂ G V) (B : Module.End ℂ V) (hB : B ^ l = 1)
    (hcov : ∀ g, B * ρ g = ρ (θ g) * B) (g : G) (c : CyclicComponent l) :
    cyclicExtension θ hθ ρ B hB hcov ⟨g, c⟩ = ρ g * cyclicPowerHom B hB c :=
  rfl

@[simp]
theorem cyclicExtension_inl (θ : MulAut G) (hθ : θ ^ l = 1)
    (ρ : Representation ℂ G V) (B : Module.End ℂ V) (hB : B ^ l = 1)
    (hcov : ∀ g, B * ρ g = ρ (θ g) * B) (g : G) :
    cyclicExtension θ hθ ρ B hB hcov (SemidirectProduct.inl g) = ρ g := by
  change ρ g * cyclicPowerHom B hB 1 = ρ g
  rw [map_one, mul_one]

/-- Restriction along the canonical inclusion recovers `ρ`, so irreducibility of `ρ`
implies irreducibility of the extension. -/
theorem cyclicExtension_irreducible (θ : MulAut G) (hθ : θ ^ l = 1)
    (ρ : Representation ℂ G V) (B : Module.End ℂ V) (hB : B ^ l = 1)
    (hcov : ∀ g, B * ρ g = ρ (θ g) * B) (hi : ρ.IsIrreducible) :
    (cyclicExtension θ hθ ρ B hB hcov).IsIrreducible := by
  let _ := hi
  let S := cyclicExtension θ hθ ρ B hB hcov
  have hnontriv : Nontrivial V := IsSimpleModule.nontrivial (MonoidAlgebra ℂ G) ρ.asModule
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · exact ⟨⟨⊥, ⊤, fun h => bot_ne_top (congrArg Subrepresentation.toSubmodule h)⟩⟩
  · intro M
    let M' : Subrepresentation ρ :=
      { toSubmodule := M.toSubmodule
        apply_mem_toSubmodule g v hv := by
          have hm := M.apply_mem_toSubmodule (SemidirectProduct.inl g) hv
          simpa [S] using hm }
    rcases eq_bot_or_eq_top M' with h | h
    · left
      apply Subrepresentation.ext
      change M'.toSubmodule = (⊥ : Subrepresentation ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h
    · right
      apply Subrepresentation.ext
      change M'.toSubmodule = (⊤ : Subrepresentation ρ).toSubmodule
      exact congrArg Subrepresentation.toSubmodule h

section GeneralLinear

variable {F : Type u} [CommRing F] {E : Type v} [CommRing E] [Algebra F E]

/-- Entrywise application of an algebra automorphism respects composition. -/
def entrywiseAutHom (n : ℕ) : (E ≃ₐ[F] E) →* MulAut (GeneralLinear n E) where
  toFun σ := entrywiseAut σ n
  map_one' := MulEquiv.ext entrywiseAut_one_apply
  map_mul' σ τ := MulEquiv.ext (entrywiseAut_mul_apply σ τ)

end GeneralLinear

end Langlands.BaseChange

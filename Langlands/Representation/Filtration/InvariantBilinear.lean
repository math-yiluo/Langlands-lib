import Langlands.Representation.Filtration.ObjectDefinitions
import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.RingTheory.Length

/-! Covariant bilinear forms and bounds along actual representation filtrations. -/

noncomputable section

namespace Langlands.InvariantBilinear

universe uK uG uV uW uX

variable {k : Type uK} [Field k] {G : Type uG} [Monoid G]
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module k V] [AddCommGroup W] [Module k W]
variable [AddCommGroup X] [Module k X]

/-- The actual space of bilinear forms with simultaneous covariance `χ`. -/
def forms (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k) :
    Submodule k (V →ₗ[k] W →ₗ[k] k) where
  carrier := {B | ∀ g v w, B (ρ g v) (σ g w) = χ g * B v w}
  zero_mem' := by simp
  add_mem' := by
    intro B C hB hC g v w
    change B (ρ g v) (σ g w) + C (ρ g v) (σ g w) =
      χ g * (B v w + C v w)
    rw [hB, hC, mul_add]
  smul_mem' := by
    intro a B hB g v w
    change a * B (ρ g v) (σ g w) = χ g * (a * B v w)
    rw [hB, mul_left_comm]

instance formsAddCommGroup (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k) :
    AddCommGroup (forms ρ σ χ) := by
  exact @Submodule.addCommGroup k (V →ₗ[k] W →ₗ[k] k) _ _ _ (forms ρ σ χ)

/-- Extended-natural length of the full covariant bilinear-form space. -/
def length (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k) : ℕ∞ :=
  Module.length k (forms ρ σ χ)

/-- Pullback in the first argument along an actual intertwiner. -/
def comapLeft {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (f : ρ.IntertwiningMap τ) :
    forms τ σ χ →ₗ[k] forms ρ σ χ where
  toFun B := ⟨B.val.comp f.toLinearMap, by
    intro g v w
    change B.val (f (ρ g v)) (σ g w) = χ g * B.val (f v) w
    rw [f.isIntertwining]
    exact B.property g (f v) w⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem comapLeft_injective {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (f : ρ.IntertwiningMap τ)
    (hf : Function.Surjective f) : Function.Injective (comapLeft σ χ f) := by
  intro B C h
  apply Subtype.ext
  ext x w
  obtain ⟨v, rfl⟩ := hf x
  exact congrArg (fun D : forms ρ σ χ => D.val v w) h

/-- Equivalence in the first argument preserves the full form space. -/
def equivLeft {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (e : ρ.Equiv τ) :
    forms ρ σ χ ≃ₗ[k] forms τ σ χ :=
  { comapLeft σ χ e.symm.toIntertwiningMap with
    invFun := comapLeft σ χ e.toIntertwiningMap
    left_inv := by
      intro B
      apply Subtype.ext
      ext v w
      exact congrArg (fun x => B.val x w) (e.symm_apply_apply v)
    right_inv := by
      intro B
      apply Subtype.ext
      ext x w
      exact congrArg (fun v => B.val v w) (e.apply_symm_apply x) }

theorem length_congr_left {ρ : Representation k G V} {τ : Representation k G X}
    (σ : Representation k G W) (χ : G → k) (e : ρ.Equiv τ) :
    length ρ σ χ = length τ σ χ :=
  (equivLeft σ χ e).length_eq

/-- Exchanging the two arguments preserves simultaneous covariance. -/
def flipEquiv (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k) :
    forms ρ σ χ ≃ₗ[k] forms σ ρ χ where
  toFun B := ⟨B.val.flip, fun g w v => B.property g v w⟩
  invFun B := ⟨B.val.flip, fun g v w => B.property g w v⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem length_flip (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k) :
    length ρ σ χ = length σ ρ χ :=
  (flipEquiv ρ σ χ).length_eq

theorem length_top_left (ρ : Representation k G V) (σ : Representation k G W)
    (χ : G → k) : length (⊤ : Subrepresentation ρ).toRepresentation σ χ = length ρ σ χ := by
  refine length_congr_left σ χ
    { toLinearMap := (⊤ : Subrepresentation ρ).toSubmodule.subtype
      isIntertwining' := fun _ => rfl
      invFun := fun v => ⟨v, trivial⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

theorem length_bot_left (ρ : Representation k G V) (σ : Representation k G W)
    (χ : G → k) : length (⊥ : Subrepresentation ρ).toRepresentation σ χ = 0 := by
  apply Module.length_eq_zero_iff.mpr
  constructor
  intro B C
  apply Subtype.ext
  ext ⟨v, hv⟩ w
  have hv' : v = 0 := hv
  subst hv'
  change B.val 0 w = C.val 0 w
  simp

/-- Restricting the first argument has the expected quotient as its kernel. -/
def descendLeft (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k)
    (S : Subrepresentation ρ) :
    LinearMap.ker (comapLeft σ χ
      ({ toLinearMap := S.toSubmodule.subtype
         isIntertwining' := fun _ => rfl } : S.toRepresentation.IntertwiningMap ρ)) →ₗ[k]
      forms (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) σ χ := by
  let incl : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let r := comapLeft σ χ incl
  have hker (B : LinearMap.ker r) : S.toSubmodule ≤ LinearMap.ker B.val.val := by
    intro v hv
    have h := congrArg (fun C : forms S.toRepresentation σ χ => C.val ⟨v, hv⟩) B.property
    exact h
  refine
    { toFun := fun B => ⟨S.toSubmodule.liftQ B.val.val (hker B), ?_⟩
      map_add' := ?_
      map_smul' := ?_ }
  · intro g q w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    exact B.val.property g v w
  · intro B C
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl
  · intro a B
    apply Subtype.ext
    apply LinearMap.ext
    intro q
    apply LinearMap.ext
    intro w
    obtain ⟨v, rfl⟩ := Submodule.mkQ_surjective S.toSubmodule q
    rfl

theorem descendLeft_injective (ρ : Representation k G V) (σ : Representation k G W)
    (χ : G → k) (S : Subrepresentation ρ) :
    Function.Injective (descendLeft ρ σ χ S) := by
  intro B C h
  apply Subtype.ext
  apply Subtype.ext
  ext v w
  exact congrArg (fun D => D.val (S.toSubmodule.mkQ v) w) h

/-- A subrepresentation and its actual quotient bound the form-space length. -/
theorem length_le_subrepresentation_add_quotient
    (ρ : Representation k G V) (σ : Representation k G W) (χ : G → k)
    (S : Subrepresentation ρ) :
    length ρ σ χ ≤ length S.toRepresentation σ χ +
      length (ρ.quotient S.toSubmodule (fun g _ hv => S.apply_mem_toSubmodule g hv)) σ χ := by
  let incl : S.toRepresentation.IntertwiningMap ρ :=
    { toLinearMap := S.toSubmodule.subtype
      isIntertwining' := fun _ => rfl }
  let r := comapLeft σ χ incl
  have hex : Function.Exact (LinearMap.ker r).subtype r.rangeRestrict := by
    apply LinearMap.exact_iff.mpr
    rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype]
  have heq := Module.length_eq_add_of_exact (R := k) (N := LinearMap.ker r)
    (M := forms ρ σ χ) (P := LinearMap.range r) (LinearMap.ker r).subtype r.rangeRestrict
    (Submodule.injective_subtype _) r.surjective_rangeRestrict hex
  change Module.length k (forms ρ σ χ) ≤ _
  rw [heq, add_comm]
  exact add_le_add
    (Module.length_le_of_injective (LinearMap.range r).subtype (Submodule.injective_subtype _))
    (Module.length_le_of_injective (descendLeft ρ σ χ S) (descendLeft_injective ρ σ χ S))

end Langlands.InvariantBilinear

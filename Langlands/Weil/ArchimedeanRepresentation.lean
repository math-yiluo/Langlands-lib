import Langlands.Weil.Archimedean
import Langlands.Weil.Representation.Predicates
import Langlands.Representation.Twist.Definitions
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.Dimension.Finrank

/-!
# Concrete archimedean Weil representations

One-dimensional characters and a two-dimensional realization of induction from
the complex subgroup of the real Weil group. The latter is explicitly identified
with equivariant functions and right translation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Weil.Archimedean

@[simp] private theorem complexPart_ofComplex (z : ComplexWeil) :
    (RealWeil.ofComplex z).complexPart = z := rfl

@[simp] private theorem parity_ofComplex (z : ComplexWeil) :
    (RealWeil.ofComplex z).parity = false := rfl

private theorem ofComplex_mul_j (z : ComplexWeil) :
    RealWeil.ofComplex z * RealWeil.j = ((z, true) : RealWeil) := by
  change ((z * 1 * 1, true) : RealWeil) = (z, true)
  simp

private theorem continuous_bool_cases {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y]
    {b : X → Bool} {f g : X → Y} (hb : Continuous b)
    (hf : Continuous f) (hg : Continuous g) :
    Continuous (fun x ↦ if b x then f x else g x) := by
  have hc : IsClopen {x | b x = true} := (isClopen_discrete {true}).preimage hb
  exact Continuous.if (by simp [hc.frontier_eq]) hf hg

private theorem character_isContinuous {G : Type*} [Group G] [TopologicalSpace G]
    (χ : G →ₜ* ℂˣ) :
    FiniteRepresentation.IsContinuous
      (FiniteRepresentation.of (characterRepresentation χ.toMonoidHom)) := by
  let : TopologicalSpace (Module.End ℂ ℂ) := moduleTopology ℂ (Module.End ℂ ℂ)
  have hc : Continuous (fun z : ℂ ↦ z • (1 : Module.End ℂ ℂ)) :=
    continuous_id.smul continuous_const
  have h := hc.comp (Units.continuous_val.comp χ.continuous)
  change Continuous (characterRepresentation χ.toMonoidHom)
  exact h.congr fun _ ↦ rfl

/-- A continuous character of the complex Weil group, on the actual line `ℂ`. -/
def complexCharacter (χ : ComplexWeil →ₜ* ℂˣ) :
    FiniteRepresentation.ContinuousObjects ComplexWeil :=
  ⟨FiniteRepresentation.of (characterRepresentation χ.toMonoidHom),
    character_isContinuous χ⟩

@[simp]
theorem complexCharacter_rank (χ : ComplexWeil →ₜ* ℂˣ) :
    (complexCharacter χ).val.rank = 1 := by
  exact CommSemiring.finrank_self ℂ

@[simp]
theorem complexCharacter_apply (χ : ComplexWeil →ₜ* ℂˣ) (z : ComplexWeil) (v : ℂ) :
    (complexCharacter χ).val.representation z v = (χ z : ℂ) * v := rfl

/-- Pullback of a real quasi-character along the constructed real abelian coordinate. -/
def realCharacter (χ : ℝˣ →ₜ* ℂˣ) :
    FiniteRepresentation.ContinuousObjects RealWeil :=
  ⟨FiniteRepresentation.of
    (characterRepresentation (χ.comp RealWeil.abelianCoordinate).toMonoidHom),
    character_isContinuous (χ.comp RealWeil.abelianCoordinate)⟩

@[simp]
theorem realCharacter_rank (χ : ℝˣ →ₜ* ℂˣ) :
    (realCharacter χ).val.rank = 1 := by
  exact CommSemiring.finrank_self ℂ

@[simp]
theorem realCharacter_apply (χ : ℝˣ →ₜ* ℂˣ) (w : RealWeil) (v : ℂ) :
    (realCharacter χ).val.representation w v =
      (χ (RealWeil.abelianCoordinate w) : ℂ) * v := rfl

@[simp]
theorem realCharacter_ofComplex (χ : ℝˣ →ₜ* ℂˣ) (z : ComplexWeil) (v : ℂ) :
    (realCharacter χ).val.representation (RealWeil.ofComplex z) v =
      (χ (complexNorm z) : ℂ) * v := by simp

@[simp]
theorem realCharacter_j (χ : ℝˣ →ₜ* ℂˣ) (v : ℂ) :
    (realCharacter χ).val.representation RealWeil.j v = (χ (-1) : ℂ) * v := by simp

/-- The actual equivariant functions used for finite-index induction. -/
def inducedFunctions (χ : ComplexWeil →ₜ* ℂˣ) : Submodule ℂ (RealWeil → ℂ) where
  carrier := {f | ∀ z w, f (RealWeil.ofComplex z * w) = (χ z : ℂ) * f w}
  zero_mem' := by simp
  add_mem' := by
    intro f g hf hg z w
    simp only [Pi.add_apply, hf z w, hg z w, mul_add]
  smul_mem' := by
    intro c f hf z w
    change c * f (RealWeil.ofComplex z * w) = (χ z : ℂ) * (c * f w)
    rw [hf z w]
    ring

/-- Right translation on the genuine induced-function space. -/
def inductionRightAction (χ : ComplexWeil →ₜ* ℂˣ) :
    Representation ℂ RealWeil (inducedFunctions χ) where
  toFun g := {
    toFun := fun f ↦ ⟨fun x ↦ f.val (x * g), by
      intro z x
      simpa only [mul_assoc] using f.property z (x * g)⟩
    map_add' := by intros; rfl
    map_smul' := by intros; rfl }
  map_one' := by
    ext f x
    change f.val (x * 1) = f.val x
    rw [mul_one]
  map_mul' g h := by
    ext f x
    change f.val (x * (g * h)) = f.val ((x * g) * h)
    rw [mul_assoc]

/-- Evaluation on the coset representatives `1,j`, with an explicit inverse. -/
def inductionCoordinates (χ : ComplexWeil →ₜ* ℂˣ) :
    inducedFunctions χ ≃ₗ[ℂ] ℂ × ℂ where
  toFun f := (f.val 1, f.val RealWeil.j)
  invFun v := ⟨fun w ↦ (χ w.complexPart : ℂ) *
    (if w.parity then v.2 else v.1), by
      rintro z ⟨w, b⟩
      cases b
      · change (χ (z * w * 1) : ℂ) * v.1 =
          (χ z : ℂ) * ((χ w : ℂ) * v.1)
        simp [mul_assoc]
      · change (χ (z * w * 1) : ℂ) * v.2 =
          (χ z : ℂ) * ((χ w : ℂ) * v.2)
        simp [mul_assoc]⟩
  left_inv f := by
    apply Subtype.ext
    funext w
    rcases w with ⟨z, b⟩
    cases b
    · have h := (f.property z 1).symm
      rw [mul_one] at h
      exact h
    · have h := (f.property z RealWeil.j).symm
      rw [ofComplex_mul_j] at h
      exact h
  right_inv v := by
    change ((χ 1 : ℂ) * v.1, (χ 1 : ℂ) * v.2) = v
    simp
  map_add' := by intros; rfl
  map_smul' := by intros; rfl

/-- Every equivariant function is continuous; there is no extra regularity assumption. -/
theorem inducedFunctions_continuous (χ : ComplexWeil →ₜ* ℂˣ)
    (f : inducedFunctions χ) : Continuous f.val := by
  have hc : Continuous (fun w : RealWeil ↦ (χ w.complexPart : ℂ)) :=
    Units.continuous_val.comp (χ.continuous.comp RealWeil.continuous_complexPart)
  have h := hc.mul (continuous_bool_cases RealWeil.continuous_parity
    (continuous_const (y := f.val RealWeil.j)) (continuous_const (y := f.val 1)))
  convert h using 1
  exact (congrArg Subtype.val ((inductionCoordinates χ).symm_apply_apply f)).symm

/-- The two-dimensional action transported from actual induced functions. -/
def twoDimensionalAction (χ : ComplexWeil →ₜ* ℂˣ) :
    Representation ℂ RealWeil (ℂ × ℂ) :=
  (inductionCoordinates χ).conjRingEquiv.toMonoidHom.comp (inductionRightAction χ)

/-- The coordinate map is an intertwining equivalence, not only a dimension count. -/
def inductionEquiv (χ : ComplexWeil →ₜ* ℂˣ) :
    (inductionRightAction χ).Equiv (twoDimensionalAction χ) where
  toLinearEquiv := inductionCoordinates χ
  isIntertwining' g := by
    apply LinearMap.ext
    intro f
    change inductionCoordinates χ (inductionRightAction χ g f) =
      inductionCoordinates χ (inductionRightAction χ g
        ((inductionCoordinates χ).symm (inductionCoordinates χ f)))
    rw [LinearEquiv.symm_apply_apply]

theorem twoDimensionalAction_apply (χ : ComplexWeil →ₜ* ℂˣ)
    (w : RealWeil) (v : ℂ × ℂ) :
    twoDimensionalAction χ w v =
      if w.parity then
        ((χ w.complexPart : ℂ) * v.2,
          (χ (star w.complexPart) : ℂ) * (χ (-1) : ℂ) * v.1)
      else
        ((χ w.complexPart : ℂ) * v.1, (χ (star w.complexPart) : ℂ) * v.2) := by
  change ((χ (1 * w).complexPart : ℂ) *
      (if (1 * w).parity then v.2 else v.1),
    (χ (RealWeil.j * w).complexPart : ℂ) *
      (if (RealWeil.j * w).parity then v.2 else v.1)) = _
  rw [one_mul]
  rcases w with ⟨z, b⟩
  cases b
  · change ((χ z : ℂ) * v.1, (χ (1 * star z * 1) : ℂ) * v.2) = _
    simp [RealWeil.complexPart, RealWeil.parity]
  · change ((χ z : ℂ) * v.2, (χ (1 * star z * (-1)) : ℂ) * v.1) =
      ((χ z : ℂ) * v.2, (χ (star z) : ℂ) * (χ (-1) : ℂ) * v.1)
    rw [one_mul, map_mul, Units.val_mul]

@[simp]
theorem twoDimensionalAction_ofComplex (χ : ComplexWeil →ₜ* ℂˣ)
    (z : ComplexWeil) (v : ℂ × ℂ) :
    twoDimensionalAction χ (RealWeil.ofComplex z) v =
      ((χ z : ℂ) * v.1, (χ (star z) : ℂ) * v.2) := by
  simpa only [complexPart_ofComplex, parity_ofComplex, Bool.false_eq_true, ite_false] using
    twoDimensionalAction_apply χ (RealWeil.ofComplex z) v

@[simp]
theorem twoDimensionalAction_j (χ : ComplexWeil →ₜ* ℂˣ) (v : ℂ × ℂ) :
    twoDimensionalAction χ RealWeil.j v = (v.2, (χ (-1) : ℂ) * v.1) := by
  simp [twoDimensionalAction_apply, RealWeil.j, RealWeil.complexPart, RealWeil.parity]

/-- Pullback of a complex quasi-character by complex conjugation. -/
def conjugateCharacter (χ : ComplexWeil →ₜ* ℂˣ) : ComplexWeil →ₜ* ℂˣ where
  toFun z := χ (star z)
  map_one' := by simp
  map_mul' z w := by simp
  continuous_toFun := χ.continuous.comp continuous_star

/-- Restriction is the genuine direct product of the two character actions. -/
theorem twoDimensionalAction_restrict (χ : ComplexWeil →ₜ* ℂˣ) :
    (twoDimensionalAction χ).comp RealWeil.ofComplex.toMonoidHom =
      (characterRepresentation χ.toMonoidHom).prod
        (characterRepresentation (conjugateCharacter χ).toMonoidHom) := by
  apply MonoidHom.ext
  intro z
  apply LinearMap.ext
  intro v
  exact twoDimensionalAction_ofComplex χ z v

theorem twoDimensionalAction_j_twice (χ : ComplexWeil →ₜ* ℂˣ) (v : ℂ × ℂ) :
    twoDimensionalAction χ RealWeil.j (twoDimensionalAction χ RealWeil.j v) =
      ((χ (-1) : ℂ) * v.1, (χ (-1) : ℂ) * v.2) := by simp

private def diagonalCoefficients : (ℂ × ℂ) →ₗ[ℂ] Module.End ℂ (ℂ × ℂ) where
  toFun a := {
    toFun v := (a.1 * v.1, a.2 * v.2)
    map_add' := by intros; ext <;> dsimp <;> ring
    map_smul' := by intros; ext <;> dsimp <;> ring }
  map_add' := by intros; apply LinearMap.ext; intro v; ext <;> dsimp <;> ring
  map_smul' := by intros; apply LinearMap.ext; intro v; ext <;> dsimp <;> ring

private def oddCoefficients (c : ℂ) : (ℂ × ℂ) →ₗ[ℂ] Module.End ℂ (ℂ × ℂ) where
  toFun a := {
    toFun v := (a.1 * v.2, a.2 * c * v.1)
    map_add' := by intros; ext <;> dsimp <;> ring
    map_smul' := by intros; ext <;> dsimp <;> ring }
  map_add' := by intros; apply LinearMap.ext; intro v; ext <;> dsimp <;> ring
  map_smul' := by intros; apply LinearMap.ext; intro v; ext <;> dsimp <;> ring

/-- Continuity in the usual finite-dimensional complex endomorphism topology. -/
theorem twoDimensionalAction_isContinuous (χ : ComplexWeil →ₜ* ℂˣ) :
    FiniteRepresentation.IsContinuous (FiniteRepresentation.of (twoDimensionalAction χ)) := by
  let : TopologicalSpace (Module.End ℂ (ℂ × ℂ)) :=
    moduleTopology ℂ (Module.End ℂ (ℂ × ℂ))
  let : ContinuousAdd (Module.End ℂ (ℂ × ℂ)) := IsModuleTopology.toContinuousAdd ℂ _
  have hc : Continuous (fun w : RealWeil ↦
      ((χ w.complexPart : ℂ), (χ (star w.complexPart) : ℂ))) :=
    (Units.continuous_val.comp (χ.continuous.comp RealWeil.continuous_complexPart)).prodMk
      (Units.continuous_val.comp (χ.continuous.comp RealWeil.continuous_complexPart.star))
  have hd := (IsModuleTopology.continuous_of_linearMap diagonalCoefficients).comp hc
  have ho := (IsModuleTopology.continuous_of_linearMap
    (oddCoefficients (χ (-1) : ℂ))).comp hc
  have h := continuous_bool_cases RealWeil.continuous_parity ho hd
  change Continuous (twoDimensionalAction χ)
  apply h.congr
  intro w
  apply LinearMap.ext
  intro v
  rw [twoDimensionalAction_apply]
  cases w.parity <;> rfl

/-- The actual continuous two-dimensional induced representation, on `ℂ × ℂ`. -/
def realInducedCharacter (χ : ComplexWeil →ₜ* ℂˣ) :
    FiniteRepresentation.ContinuousObjects RealWeil :=
  ⟨FiniteRepresentation.of (twoDimensionalAction χ), twoDimensionalAction_isContinuous χ⟩

@[simp]
theorem realInducedCharacter_rank (χ : ComplexWeil →ₜ* ℂˣ) :
    (realInducedCharacter χ).val.rank = 2 := by
  simp [realInducedCharacter, FiniteRepresentation.rank, Module.finrank_prod]

end Langlands.Weil.Archimedean

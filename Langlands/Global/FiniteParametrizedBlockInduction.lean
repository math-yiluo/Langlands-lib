import Langlands.Global.AdelicBlockDeterminantCharacter
import Langlands.Global.ArchimedeanCompact
import Langlands.Representation.Induction.BlockFactors

/-! Normalized finite adelic induction with a common stabilizer across the
standard compact parameters at infinity. -/

noncomputable section
set_option autoImplicit false

namespace Langlands.Global.FiniteParametrizedBlockInduction

open GeneralLinear Induction _root_.Representation

universe u uV

variable (F : Type u) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- The finite group acts on the second argument of a parametrized section. -/
abbrev Arguments := standardInfiniteCompact F n × FiniteAdelicGL F n

abbrev finiteEmbedding : FiniteAdelicGL F n →* Arguments F (n := n) :=
  MonoidHom.inr _ _

/-- The covariance subgroup acts only on the finite argument. -/
def parabolic : Subgroup (Arguments F (n := n)) :=
  (⊥ : Subgroup (standardInfiniteCompact F n)).prod (B.parabolic (FiniteAdeles F))

/-- The projection of the covariance subgroup onto the finite parabolic. -/
def parabolicProjection : parabolic F B →* AdelicBlockParabolic.Finite F B where
  toFun p := ⟨p.val.2, p.property.2⟩
  map_one' := rfl
  map_mul' _ _ := rfl

/-- The finite half-modulus obtained by restriction of the adelic half-modulus. -/
def finiteHalfCharacter : AdelicBlockParabolic.Finite F B →* ℂˣ :=
  (AdelicBlockDeterminantCharacter.parabolicHalfCharacter F B).toMonoidHom.comp
    (AdelicBlockParabolic.ofFinite F B).toMonoidHom

variable {V : Fin B.length → Type uV} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]
  (σ : ∀ i, Representation ℂ (FiniteAdelicGL F (B.size i)) (V i))

/-- Twist the finite block tensor by the finite parabolic half-modulus. -/
def finiteCoefficient : Representation ℂ (AdelicBlockParabolic.Finite F B) (PiTensorProduct ℂ V) :=
  twist (finiteHalfCharacter F B) ((B.blockTensor σ).comp (B.leviProjection (FiniteAdeles F)))

/-- Coefficients for the parabolic acting on the product of arguments. -/
abbrev coefficient := (finiteCoefficient F B σ).comp (parabolicProjection F B)

/-- Right action of the finite adelic group on all covariant sections. -/
abbrev rightAction :=
  (equivariantAction (parabolic F B) (coefficient F B σ)).comp (finiteEmbedding F)

/-- The covariant sections sharing one open finite stabilizer, uniform in the parameter. -/
abbrev Sections := smoothVectors (rightAction F B σ)

/-- Normalized induction in the finite variable with standard compact parameters. -/
def induced : Representation ℂ (FiniteAdelicGL F n) (Sections F B σ) :=
  smoothPart (rightAction F B σ)

/-- Evaluation at a standard compact parameter and a finite matrix. -/
def evaluate (f : Sections F B σ) (k : standardInfiniteCompact F n) (g : FiniteAdelicGL F n) :
    PiTensorProduct ℂ V :=
  f.val.val (k, g)

@[simp] theorem evaluate_induced (f : Sections F B σ) (k : standardInfiniteCompact F n)
    (g h : FiniteAdelicGL F n) :
    evaluate F B σ (induced F B σ h f) k g = evaluate F B σ f k (g * h) := by
  change f.val.val (k * 1, g * h) = _
  rw [mul_one]
  rfl

/-- Build a section from pointwise covariance and an open stabilizer uniform in `k` and `g`. -/
def sectionOf (f : standardInfiniteCompact F n → FiniteAdelicGL F n → PiTensorProduct ℂ V)
    (hcov : ∀ k (p : AdelicBlockParabolic.Finite F B) g,
      f k (p.val * g) = finiteCoefficient F B σ p (f k g))
    (L : OpenSubgroup (FiniteAdelicGL F n))
    (hL : ∀ (l : L) k g, f k (g * (l : FiniteAdelicGL F n)) = f k g) : Sections F B σ :=
  ⟨⟨fun x => f x.1 x.2, by
      intro p x
      have hp : p.val.1 = 1 := Subgroup.mem_bot.mp p.property.1
      change f (p.val.1 * x.1) (p.val.2 * x.2) =
        finiteCoefficient F B σ (parabolicProjection F B p) (f x.1 x.2)
      rw [hp, one_mul]
      exact hcov x.1 (parabolicProjection F B p) x.2⟩, L, by
    intro l
    apply Subtype.ext
    funext x
    change f (x.1 * 1) (x.2 * (l : FiniteAdelicGL F n)) = f x.1 x.2
    rw [mul_one]
    exact hL l _ _⟩

@[simp] theorem evaluate_sectionOf
    (f : standardInfiniteCompact F n → FiniteAdelicGL F n → PiTensorProduct ℂ V)
    (hcov : ∀ k (p : AdelicBlockParabolic.Finite F B) g,
      f k (p.val * g) = finiteCoefficient F B σ p (f k g))
    (L : OpenSubgroup (FiniteAdelicGL F n))
    (hL : ∀ (l : L) k g, f k (g * (l : FiniteAdelicGL F n)) = f k g)
    (k : standardInfiniteCompact F n) (g : FiniteAdelicGL F n) :
    evaluate F B σ (sectionOf F B σ f hcov L hL) k g = f k g := rfl

/-- Evaluation at all pairs detects a section. -/
theorem sections_ext {f f' : Sections F B σ}
    (h : ∀ k g, evaluate F B σ f k g = evaluate F B σ f' k g) : f = f' := by
  apply Subtype.ext
  apply Subtype.ext
  exact funext fun x => h x.1 x.2

end Langlands.Global.FiniteParametrizedBlockInduction

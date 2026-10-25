import Langlands.Representation.Archimedean.GeneralLinear
import Langlands.Representation.Shahidi.Induction
import Langlands.Representation.Shahidi.IntertwiningIntegral
import Langlands.Representation.Shahidi.JacquetIntegral
import Langlands.Representation.Shahidi.CoordinateMeasures

/-!
# Induced representations, intertwining and Jacquet integrals over `ℝ` and `ℂ`

For `F = ℝ` or `ℂ` and a Banach representation `σ` of `GL_m(F) × GL_n(F)`, the smooth
vectors of the normalized induction `I(s, σ)` from the standard parabolic of type
`(m, n)` are the smooth functions `f` on `GL_{m+n}(F)` with
`f(diag(h₁, h₂) u g) = |det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2) σ(h₁, h₂) f(g)`; the group
acts by right translation. The target `I(-s, σ̃)` is induced from the parabolic of type
`(n, m)` from the exchanged representation `σ̃(h₂, h₁) = σ(h₁, h₂)`.

The intertwining integral `A f(g) = ∫ f(w u'(a) g) da` and the two Jacquet integrals use
the Library's field-general integrands of Shahidi's (0.1) and (0.2), as absolutely
convergent Bochner integrals for a Haar measure on `F` placed on every matrix entry. The
Jacquet integral `λ'` of `I(-s, σ̃)` converges only in a left half-plane; at other `s`
it is the value of its entire continuation along a flat family of sections. Shahidi's
relation `λ(f) = C λ'(A f)` is stated with two scalars, so that it also covers the
multiplied form `a λ(f) = b λ'(A f)`.
-/

noncomputable section

open scoped Manifold ContDiff Matrix.Norms.Operator NNReal
open MeasureTheory

namespace Langlands.Archimedean

open Langlands.HarmonicAnalysis

-- As in `GeneralLinear`: the charts on units need reduction through the normed-ring
-- instances of matrices.
set_option backward.isDefEq.respectTransparency false

universe uF uE u𝔩 uHL uL uX

variable (F : Type uF) [RCLike F]

/-! ## The normalized absolute value and determinant characters -/

/-- The normalized absolute value `|x|_F = ‖x‖^[F:ℝ]` on units: `|x|` over `ℝ` and
`|x|²` over `ℂ`. -/
def normalizedAbsUnits : Fˣ →* ℝ≥0ˣ :=
  Units.map ((powMonoidHom (Module.finrank ℝ F)).comp (nnnormHom : F →*₀ ℝ≥0).toMonoidHom)

@[simp]
theorem normalizedAbsUnits_apply (x : Fˣ) :
    ((normalizedAbsUnits F x : ℝ≥0) : ℝ) = ‖(x : F)‖ ^ Module.finrank ℝ F := by
  simp [normalizedAbsUnits]

/-- `g ↦ |det g|_F` on `GL_n(F)`. -/
def normalizedDeterminantAbs (n : ℕ) : Langlands.GeneralLinear n F →* ℝ≥0ˣ :=
  (normalizedAbsUnits F).comp GeneralLinear.determinant

@[simp]
theorem normalizedDeterminantAbs_apply (n : ℕ) (g : Langlands.GeneralLinear n F) :
    ((normalizedDeterminantAbs F n g : ℝ≥0) : ℝ) =
      ‖Matrix.det (g : Matrix (Fin n) (Fin n) F)‖ ^ Module.finrank ℝ F :=
  normalizedAbsUnits_apply F _

/-- The covariance character of `I(s, σ)` on `GL_m × GL_n`:
`(h₁, h₂) ↦ |det h₁|^((s+n)/2) |det h₂|^(-(s+m)/2)`, the product of the twist
`|det h₁|^(s/2) |det h₂|^(-s/2)` and the half modulus `δ_P^(1/2)`. -/
def sourceCharacter (m n : ℕ) (s : ℂ) :
    Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →* ℂˣ :=
  MonoidHom.coprod (Shahidi.complexPower (normalizedDeterminantAbs F m) ((s + n) / 2))
    (Shahidi.complexPower (normalizedDeterminantAbs F n) (-((s + m) / 2)))

@[simp]
theorem sourceCharacter_apply (m n : ℕ) (s : ℂ)
    (h : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F) :
    (sourceCharacter F m n s h : ℂ) =
      (((normalizedDeterminantAbs F m h.1 : ℝ≥0) : ℝ) : ℂ) ^ ((s + n) / 2) *
        (((normalizedDeterminantAbs F n h.2 : ℝ≥0) : ℝ) : ℂ) ^ (-((s + m) / 2)) :=
  rfl

/-- The covariance character of `I(-s, σ̃)` on `GL_n × GL_m`:
`(h₂, h₁) ↦ |det h₂|^((m-s)/2) |det h₁|^((s-n)/2)`, the product of the twist
`|det h₂|^(-s/2) |det h₁|^(s/2)` and the half modulus of the parabolic of type `(n, m)`. -/
def targetCharacter (m n : ℕ) (s : ℂ) :
    Langlands.GeneralLinear n F × Langlands.GeneralLinear m F →* ℂˣ :=
  MonoidHom.coprod (Shahidi.complexPower (normalizedDeterminantAbs F n) ((m - s) / 2))
    (Shahidi.complexPower (normalizedDeterminantAbs F m) ((s - n) / 2))

@[simp]
theorem targetCharacter_apply (m n : ℕ) (s : ℂ)
    (h : Langlands.GeneralLinear n F × Langlands.GeneralLinear m F) :
    (targetCharacter F m n s h : ℂ) =
      (((normalizedDeterminantAbs F n h.1 : ℝ≥0) : ℝ) : ℂ) ^ ((m - s) / 2) *
        (((normalizedDeterminantAbs F m h.2 : ℝ≥0) : ℝ) : ℂ) ^ ((s - n) / 2) :=
  rfl

/-! ## Smooth sections of induced representations -/

section Sections

variable {r : ℕ}
variable {𝔩 : Type u𝔩} [NormedAddCommGroup 𝔩] [NormedSpace ℝ 𝔩]
  {HL : Type uHL} [TopologicalSpace HL] (IL : ModelWithCorners ℝ 𝔩 HL)
  {L : Type uL} [Group L] [TopologicalSpace L] [ChartedSpace HL L] {X : Type uX}
  {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The smooth sections of the representation induced from `P = ι(L) u(X)`: real `C^∞`
functions `f : GL_r(F) → E` with values in the smooth vectors of `σ` and
`f(ι(h) u(x) g) = χ(h) σ(h) f(g)`. -/
def inducedSpace (ι : L →* Langlands.GeneralLinear r F) (u : X → Langlands.GeneralLinear r F)
    (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ) : Submodule ℂ (Langlands.GeneralLinear r F → E) where
  carrier := {f | ContMDiff (matrixModel F r) 𝓘(ℝ, E) ∞ f ∧
    (∀ g, f g ∈ smoothVectors IL σ) ∧
    ∀ (h : L) (x : X) (g : Langlands.GeneralLinear r F),
      f (ι h * u x * g) = (χ h : ℂ) • σ h (f g)}
  zero_mem' := ⟨contMDiff_const, fun _ => (smoothVectors IL σ).zero_mem, fun _ _ _ => by simp⟩
  add_mem' {f₁ f₂} hf₁ hf₂ :=
    ⟨hf₁.1.add hf₂.1, fun g => (smoothVectors IL σ).add_mem (hf₁.2.1 g) (hf₂.2.1 g),
      fun h x g => by
        change f₁ _ + f₂ _ = (χ h : ℂ) • σ h (f₁ g + f₂ g)
        rw [hf₁.2.2 h x g, hf₂.2.2 h x g, map_add, smul_add]⟩
  smul_mem' c f hf :=
    ⟨((c • ContinuousLinearMap.id ℂ E).restrictScalars ℝ).contDiff.contMDiff.comp hf.1,
      fun g => (smoothVectors IL σ).smul_mem c (hf.2.1 g),
      fun h x g => by
        change c • f _ = (χ h : ℂ) • σ h (c • f g)
        rw [hf.2.2 h x g, map_smul, smul_comm]⟩

variable {IL}

theorem mem_inducedSpace_iff (ι : L →* Langlands.GeneralLinear r F)
    (u : X → Langlands.GeneralLinear r F) (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ)
    (f : Langlands.GeneralLinear r F → E) :
    f ∈ inducedSpace F IL ι u σ χ ↔
      ContMDiff (matrixModel F r) 𝓘(ℝ, E) ∞ f ∧ (∀ g, f g ∈ smoothVectors IL σ) ∧
        ∀ (h : L) (x : X) (g : Langlands.GeneralLinear r F),
          f (ι h * u x * g) = (χ h : ℂ) • σ h (f g) :=
  Iff.rfl

variable (IL)

/-- The values of a section, as smooth vectors of `σ`. -/
def sectionValues (ι : L →* Langlands.GeneralLinear r F) (u : X → Langlands.GeneralLinear r F)
    (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ) :
    inducedSpace F IL ι u σ χ →ₗ[ℂ] (Langlands.GeneralLinear r F → smoothVectors IL σ) where
  toFun f g := ⟨f.val g, f.property.2.1 g⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
theorem sectionValues_apply (ι : L →* Langlands.GeneralLinear r F)
    (u : X → Langlands.GeneralLinear r F) (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ)
    (f : inducedSpace F IL ι u σ χ) (g : Langlands.GeneralLinear r F) :
    (sectionValues F IL ι u σ χ f g : E) = f.val g :=
  rfl

/-- The induced representation: `GL_r(F)` acts on sections by right translation. -/
def inducedRepresentation (ι : L →* Langlands.GeneralLinear r F)
    (u : X → Langlands.GeneralLinear r F) (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ) :
    Representation ℂ (Langlands.GeneralLinear r F) (inducedSpace F IL ι u σ χ) where
  toFun g :=
    { toFun f := ⟨fun x => f.val (x * g),
        ⟨f.property.1.comp (contMDiff_id.mul contMDiff_const),
          fun x => f.property.2.1 (x * g),
          fun h y x => by
            change f.val (ι h * u y * x * g) = (χ h : ℂ) • σ h (f.val (x * g))
            rw [mul_assoc (ι h * u y) x g]
            exact f.property.2.2 h y (x * g)⟩⟩
      map_add' _ _ := rfl
      map_smul' _ _ := rfl }
  map_one' := by
    ext f x
    exact congrArg f.val (mul_one x)
  map_mul' g h := by
    ext f x
    exact congrArg f.val (mul_assoc x g h).symm

@[simp]
theorem inducedRepresentation_apply (ι : L →* Langlands.GeneralLinear r F)
    (u : X → Langlands.GeneralLinear r F) (σ : L →* (E →L[ℂ] E)) (χ : L →* ℂˣ)
    (g x : Langlands.GeneralLinear r F) (f : inducedSpace F IL ι u σ χ) :
    (inducedRepresentation F IL ι u σ χ g f).val x = f.val (x * g) :=
  rfl

end Sections

/-! ## The two induced representations of Shahidi's pair -/

section Pair

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E] (m n : ℕ)

/-- The block-diagonal Levi `diag(h₁, h₂)` of the parabolic of type `(m, n)`. -/
abbrev sourceLevi : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →*
    Langlands.GeneralLinear (m + n) F :=
  GeneralLinear.blockSum

/-- The Levi `diag(h₂, h₁)` of the parabolic of type `(n, m)`, transported to the same
group `GL_{m+n}(F)`. -/
abbrev targetLevi : Langlands.GeneralLinear n F × Langlands.GeneralLinear m F →*
    Langlands.GeneralLinear (m + n) F :=
  (Shahidi.swapRank m n F).toMonoidHom.comp GeneralLinear.blockSum

/-- The exchanged representation `σ̃(h₂, h₁) = σ(h₁, h₂)` of `GL_n × GL_m`. -/
def exchange (σ : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →* (E →L[ℂ] E)) :
    Langlands.GeneralLinear n F × Langlands.GeneralLinear m F →* (E →L[ℂ] E) :=
  σ.comp (MulEquiv.prodComm : Langlands.GeneralLinear n F × Langlands.GeneralLinear m F ≃*
    Langlands.GeneralLinear m F × Langlands.GeneralLinear n F).toMonoidHom

@[simp]
theorem exchange_apply
    (σ : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →* (E →L[ℂ] E))
    (h : Langlands.GeneralLinear n F × Langlands.GeneralLinear m F) :
    exchange F m n σ h = σ (h.2, h.1) :=
  rfl

variable (σ : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →* (E →L[ℂ] E))
  (s : ℂ)

/-- The smooth sections of `I(s, σ)`: covariance under `diag(h₁, h₂)` and the upper radical
`[[I_m, a], [0, I_n]]` with the character `sourceCharacter`. -/
abbrev sourceSpace : Submodule ℂ (Langlands.GeneralLinear (m + n) F → E) :=
  inducedSpace F (pairModel F m n) (sourceLevi F m n) (Shahidi.upper m n F) σ
    (sourceCharacter F m n s)

/-- `I(s, σ)` as a representation by right translation. -/
abbrev sourceRepresentation :
    Representation ℂ (Langlands.GeneralLinear (m + n) F) (sourceSpace F m n σ s) :=
  inducedRepresentation F (pairModel F m n) (sourceLevi F m n) (Shahidi.upper m n F) σ
    (sourceCharacter F m n s)

/-- The smooth sections of `I(-s, σ̃)`: covariance under the Levi of type `(n, m)` and the
radical `U'` of the intertwining integral, with the character `targetCharacter`. -/
abbrev targetSpace : Submodule ℂ (Langlands.GeneralLinear (m + n) F → E) :=
  inducedSpace F (pairModel F n m) (targetLevi F m n) (Shahidi.intertwiningUnipotent m n F)
    (exchange F m n σ) (targetCharacter F m n s)

/-- `I(-s, σ̃)` as a representation by right translation. -/
abbrev targetRepresentation :
    Representation ℂ (Langlands.GeneralLinear (m + n) F) (targetSpace F m n σ s) :=
  inducedRepresentation F (pairModel F n m) (targetLevi F m n)
    (Shahidi.intertwiningUnipotent m n F) (exchange F m n σ) (targetCharacter F m n s)

end Pair

/-! ## The intertwining and Jacquet integrals -/

section Integrals

variable [MeasurableSpace F] (μ : AdditiveHaarMeasure F)
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- The measure `∏ da_{ij}` on rectangular coordinates, with the Haar measure `μ` on every
entry. -/
abbrev entryMeasure (p q : ℕ) : Measure (Matrix (Fin p) (Fin q) F) :=
  Shahidi.matrixCoordinateMeasure fun _ _ => μ

variable (m n : ℕ)
  (σ : Langlands.GeneralLinear m F × Langlands.GeneralLinear n F →* (E →L[ℂ] E)) (s : ℂ)

/-- The intertwining integral `A f(g) = ∫ f(w u'(a) g) da` of `f ∈ I(s, σ)` converges
absolutely at every `g`, and its values form the section `A ∈ I(-s, σ̃)`. -/
def HasIntertwiningIntegral [CompleteSpace E] (f : sourceSpace F m n σ s)
    (A : targetSpace F m n σ s) : Prop :=
  ∀ g : Langlands.GeneralLinear (m + n) F,
    Integrable (Shahidi.intertwiningIntegrand m n g f.val) (entryMeasure F μ n m) ∧
      ∫ a, Shahidi.intertwiningIntegrand m n g f.val a ∂(entryMeasure F μ n m) = A.val g

/-- The section `A` of `HasIntertwiningIntegral` is unique. -/
theorem hasIntertwiningIntegral_unique [CompleteSpace E] {f : sourceSpace F m n σ s}
    {A A' : targetSpace F m n σ s} (h : HasIntertwiningIntegral F μ m n σ s f A)
    (h' : HasIntertwiningIntegral F μ m n σ s f A') : A = A' :=
  Subtype.ext (funext fun g => (h g).2.symm.trans (h' g).2)

end Integrals

section Jacquet

variable [MeasurableSpace F] (μ : AdditiveHaarMeasure F)
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable (m n : ℕ) (s : ℂ) (ψ : UnitaryAdditiveCharacter F)
  (σ : Langlands.GeneralLinear (m + 1) F × Langlands.GeneralLinear (n + 1) F →* (E →L[ℂ] E))

/-- The Jacquet integral `λ(f) = ∫ χ̄(u'(a)) ℓ(f(w u'(a))) da` of `f ∈ I(s, σ)` converges
absolutely to `z`. -/
def HasJacquetIntegral (ℓ : smoothVectors (pairModel F (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ)
    (f : sourceSpace F (m + 1) (n + 1) σ s) (z : ℂ) : Prop :=
  Integrable (Shahidi.jacquetIntegrand m n ψ ℓ
      (sectionValues F (pairModel F (m + 1) (n + 1)) _ _ σ _ f))
      (entryMeasure F μ (n + 1) (m + 1)) ∧
    ∫ a, Shahidi.jacquetIntegrand m n ψ ℓ
      (sectionValues F (pairModel F (m + 1) (n + 1)) _ _ σ _ f) a
        ∂(entryMeasure F μ (n + 1) (m + 1)) = z

/-- The Jacquet integral `λ'(f') = ∫ χ̄(u(a)) ℓ'(f'(w⁻¹ u(a))) da` of `f' ∈ I(-s, σ̃)`
converges absolutely to `z`. -/
def HasSwappedJacquetIntegral
    (ℓ' : smoothVectors (pairModel F (n + 1) (m + 1)) (exchange F (m + 1) (n + 1) σ) →ₗ[ℂ] ℂ)
    (f' : targetSpace F (m + 1) (n + 1) σ s) (z : ℂ) : Prop :=
  Integrable (Shahidi.swappedJacquetIntegrand m n ψ ℓ'
      (sectionValues F (pairModel F (n + 1) (m + 1)) _ _ _ _ f'))
      (entryMeasure F μ (m + 1) (n + 1)) ∧
    ∫ a, Shahidi.swappedJacquetIntegrand m n ψ ℓ'
      (sectionValues F (pairModel F (n + 1) (m + 1)) _ _ _ _ f') a
        ∂(entryMeasure F μ (m + 1) (n + 1)) = z

/-- The value of an absolutely convergent Jacquet integral is unique. -/
theorem hasJacquetIntegral_unique {ℓ : smoothVectors (pairModel F (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ}
    {f : sourceSpace F (m + 1) (n + 1) σ s} {z z' : ℂ}
    (h : HasJacquetIntegral F μ m n s ψ σ ℓ f z) (h' : HasJacquetIntegral F μ m n s ψ σ ℓ f z') :
    z = z' :=
  h.2.symm.trans h'.2

/-- The value of an absolutely convergent swapped Jacquet integral is unique. -/
theorem hasSwappedJacquetIntegral_unique
    {ℓ' : smoothVectors (pairModel F (n + 1) (m + 1)) (exchange F (m + 1) (n + 1) σ) →ₗ[ℂ] ℂ}
    {f' : targetSpace F (m + 1) (n + 1) σ s} {z z' : ℂ}
    (h : HasSwappedJacquetIntegral F μ m n s ψ σ ℓ' f' z)
    (h' : HasSwappedJacquetIntegral F μ m n s ψ σ ℓ' f' z') : z = z' :=
  h.2.symm.trans h'.2

/-- A flat family of sections `φ(t) ∈ I(-t, σ̃)`, `t ∈ ℂ`: all of them restrict to the same
function on the unitary group `K = O(m+n+2)` or `U(m+n+2)` (the compact picture). -/
def IsFlatTargetFamily (φ : (t : ℂ) → targetSpace F (m + 1) (n + 1) σ t) : Prop :=
  ∀ (t t' : ℂ) (k : unitaryCompact F (m + 1 + (n + 1))), (φ t).val k = (φ t').val k

/-- The value at `f' ∈ I(-s, σ̃)` of the analytic continuation of the Jacquet integral
`λ'`: along a flat family through `f'`, the integrals converge absolutely in a left
half-plane `Re t < a` to the values of an entire function `J`, and `z = J(s)`. -/
def HasContinuedSwappedJacquetIntegral
    (ℓ' : smoothVectors (pairModel F (n + 1) (m + 1)) (exchange F (m + 1) (n + 1) σ) →ₗ[ℂ] ℂ)
    (f' : targetSpace F (m + 1) (n + 1) σ s) (z : ℂ) : Prop :=
  ∃ (φ : (t : ℂ) → targetSpace F (m + 1) (n + 1) σ t) (J : ℂ → ℂ) (a : ℝ),
    IsFlatTargetFamily F m n σ φ ∧ φ s = f' ∧ Differentiable ℂ J ∧
      (∀ t : ℂ, t.re < a → HasSwappedJacquetIntegral F μ m n t ψ σ ℓ' (φ t) (J t)) ∧
      J s = z

/-- Shahidi's relation between the Jacquet integrals of `f` and of `A f`, with two
scalars: the integrals `A f` and `λ(f)` converge absolutely, `λ'(A f)` is the analytic
continuation of the Jacquet integral, and `a λ(f) = b λ'(A f)`. -/
def SatisfiesLocalCoefficientRelation [CompleteSpace E]
    (ℓ : smoothVectors (pairModel F (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ)
    (ℓ' : smoothVectors (pairModel F (n + 1) (m + 1)) (exchange F (m + 1) (n + 1) σ) →ₗ[ℂ] ℂ)
    (f : sourceSpace F (m + 1) (n + 1) σ s) (a b : ℂ) : Prop :=
  ∃ (A : targetSpace F (m + 1) (n + 1) σ s) (z z' : ℂ),
    HasIntertwiningIntegral F μ (m + 1) (n + 1) σ s f A ∧
      HasJacquetIntegral F μ m n s ψ σ ℓ f z ∧
      HasContinuedSwappedJacquetIntegral F μ m n s ψ σ ℓ' A z' ∧
      a * z = b * z'

/-- `c` is the local coefficient at `s`: `λ(f) = c λ'(A f)` for every section `f` of
`I(s, σ)`, with `A f` and `λ(f)` absolutely convergent and `λ'` continued. -/
def IsLocalCoefficientAt [CompleteSpace E]
    (ℓ : smoothVectors (pairModel F (m + 1) (n + 1)) σ →ₗ[ℂ] ℂ)
    (ℓ' : smoothVectors (pairModel F (n + 1) (m + 1)) (exchange F (m + 1) (n + 1) σ) →ₗ[ℂ] ℂ)
    (c : ℂ) : Prop :=
  ∀ f : sourceSpace F (m + 1) (n + 1) σ s,
    SatisfiesLocalCoefficientRelation F μ m n s ψ σ ℓ ℓ' f 1 c

end Jacquet

end Langlands.Archimedean

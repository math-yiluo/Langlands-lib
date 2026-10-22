import Langlands.Automorphic.Ambient
import Langlands.Global.AdeleQuotientStatement
import Langlands.Group.GL.BlockUnipotent
import Mathlib.MeasureTheory.Measure.Haar.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Constant terms along maximal block parabolics and cuspidality

For `a + b = n`, the unipotent radical of the standard upper block parabolic of
`GL_n` with blocks `(a, b)` is `X ↦ [[1, X], [0, 1]]`, `X` an `a × b` matrix. Over the
adeles, `N(K) \ N(𝔸_K)` is the compact group of `a × b` matrices over `𝔸_K / K`, given
here its normalized Haar probability measure. The constant term of a continuous
rational-left-invariant function `f` is `g ↦ ∫ f(u(X) g) dX` over that quotient, and `f` is
cuspidal when every constant term along a nontrivial split `a, b ≥ 1` vanishes
identically (Borel–Jacquet 1979, §3.3). Compactness of `𝔸_K / K` is an instance
parameter. See `ConstantTerm.md`.
-/

noncomputable section

universe u

open MeasureTheory

namespace Langlands.Global

variable (K : Type u) [Field K] [NumberField K]

/-- The normalized Haar probability measure on the compact group `𝔸_K / K`, for its Borel
σ-algebra (which is not made an instance). -/
def adeleQuotientHaar [CompactSpace (AdeleQuotient K)] :
    @Measure (AdeleQuotient K) (borel (AdeleQuotient K)) :=
  letI : MeasurableSpace (AdeleQuotient K) := borel (AdeleQuotient K)
  haveI : BorelSpace (AdeleQuotient K) := ⟨rfl⟩
  Measure.addHaarMeasure ⊤

theorem adeleQuotientHaar_univ [CompactSpace (AdeleQuotient K)] :
    adeleQuotientHaar K Set.univ = 1 := by
  let : MeasurableSpace (AdeleQuotient K) := borel (AdeleQuotient K)
  have : BorelSpace (AdeleQuotient K) := ⟨rfl⟩
  exact Measure.addHaarMeasure_self (K₀ := ⊤)

theorem adeleQuotientHaar_isAddHaarMeasure [CompactSpace (AdeleQuotient K)] :
    @Measure.IsAddHaarMeasure (AdeleQuotient K) _ _ (borel (AdeleQuotient K))
      (adeleQuotientHaar K) := by
  let : MeasurableSpace (AdeleQuotient K) := borel (AdeleQuotient K)
  have : BorelSpace (AdeleQuotient K) := ⟨rfl⟩
  exact Measure.isAddHaarMeasure_addHaarMeasure ⊤

instance [CompactSpace (AdeleQuotient K)] : IsProbabilityMeasure (adeleQuotientHaar K) :=
  ⟨adeleQuotientHaar_univ K⟩

variable {K}

/-- Entrywise reduction of an adelic matrix modulo `K`. -/
def matrixQuotientMap {a b : ℕ} (X : Matrix (Fin a) (Fin b) (Adeles K)) :
    Matrix (Fin a) (Fin b) (AdeleQuotient K) :=
  X.map (adeleQuotientMap K)

/-- A chosen entrywise lift of a matrix over `𝔸_K / K` to a matrix over `𝔸_K`. -/
def matrixLift {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) :
    Matrix (Fin a) (Fin b) (Adeles K) :=
  X.map (Function.surjInv (QuotientAddGroup.mk_surjective (s := principalAdeles K)))

@[simp]
theorem matrixQuotientMap_matrixLift {a b : ℕ} (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) :
    matrixQuotientMap (matrixLift X) = X := by
  ext i j
  exact Function.surjInv_eq (QuotientAddGroup.mk_surjective (s := principalAdeles K)) (X i j)

/-- Two adelic matrices with the same reduction differ by a rational matrix. -/
theorem exists_rational_of_matrixQuotientMap_eq {a b : ℕ}
    {X Y : Matrix (Fin a) (Fin b) (Adeles K)}
    (hXY : matrixQuotientMap X = matrixQuotientMap Y) :
    ∃ C : Matrix (Fin a) (Fin b) K, Y = C.map (diagonal K) + X := by
  have hmem : ∀ i j, -X i j + Y i j ∈ principalAdeles K := fun i j =>
    QuotientAddGroup.eq.mp (congrFun (congrFun hXY i) j)
  choose C hC using fun i j => (hmem i j)
  refine ⟨Matrix.of fun i j => C i j, ?_⟩
  ext i j
  change Y i j = diagonal K (C i j) + X i j
  rw [show diagonal K (C i j) = -X i j + Y i j from hC i j]
  abel

theorem isOpenQuotientMap_matrixQuotientMap (a b : ℕ) :
    IsOpenQuotientMap (matrixQuotientMap (K := K) (a := a) (b := b)) :=
  IsOpenQuotientMap.piMap fun _ =>
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk

variable (K)

instance matrixAdeleQuotientCompactSpace [CompactSpace (AdeleQuotient K)] (a b : ℕ) :
    CompactSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) :=
  inferInstanceAs (CompactSpace (Fin a → Fin b → AdeleQuotient K))

/-- The normalized Haar probability measure on the compact group of `a × b` matrices over
`𝔸_K / K`, that is, on `N(K) \ N(𝔸_K)` for the unipotent radical `N` of the `(a, b)` block
parabolic, for its Borel σ-algebra (which is not made an instance). -/
def matrixQuotientHaar [CompactSpace (AdeleQuotient K)] (a b : ℕ) :
    @Measure (Matrix (Fin a) (Fin b) (AdeleQuotient K))
      (borel (Matrix (Fin a) (Fin b) (AdeleQuotient K))) :=
  letI : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  haveI : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  Measure.addHaarMeasure ⊤

theorem matrixQuotientHaar_univ [CompactSpace (AdeleQuotient K)] (a b : ℕ) :
    matrixQuotientHaar K a b Set.univ = 1 := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  exact Measure.addHaarMeasure_self (K₀ := ⊤)

theorem matrixQuotientHaar_isAddHaarMeasure [CompactSpace (AdeleQuotient K)] (a b : ℕ) :
    @Measure.IsAddHaarMeasure (Matrix (Fin a) (Fin b) (AdeleQuotient K)) _ _
      (borel (Matrix (Fin a) (Fin b) (AdeleQuotient K))) (matrixQuotientHaar K a b) := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  exact Measure.isAddHaarMeasure_addHaarMeasure ⊤

instance [CompactSpace (AdeleQuotient K)] (a b : ℕ) :
    IsProbabilityMeasure (matrixQuotientHaar K a b) :=
  ⟨matrixQuotientHaar_univ K a b⟩

end Langlands.Global

namespace Langlands.Automorphic

open Langlands.Global Langlands.GeneralLinear ContinuousRationalFunctions

variable (K : Type u) [Field K] [NumberField K] (n : ℕ)

variable {K n} in
/-- The rational unipotent matrices map to the adelic ones on reducing coefficients. -/
theorem rational_blockUnipotent {a b : ℕ} (h : a + b = n) (C : Matrix (Fin a) (Fin b) K) :
    AdelicGL.rational K n (blockUnipotent h C) = blockUnipotent h (C.map (diagonal K)) :=
  map_blockUnipotent _ h C

/-- The constant-term integrand `X ↦ f(u(X) g)` on `a × b` matrices over `𝔸_K / K`, computed
through a chosen lift of `X`; by rational invariance it does not depend on the lift
(`constantTermIntegrand_mk`). -/
def constantTermIntegrand {a b : ℕ} (h : a + b = n) (f : ContinuousRationalFunctions K n)
    (g : AdelicGL K n) (X : Matrix (Fin a) (Fin b) (AdeleQuotient K)) : ℂ :=
  evaluate K n f (blockUnipotent h (matrixLift X) * g)

variable {K n}

theorem constantTermIntegrand_mk {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions K n) (g : AdelicGL K n)
    (Y : Matrix (Fin a) (Fin b) (Adeles K)) :
    constantTermIntegrand K n h f g (matrixQuotientMap Y) =
      evaluate K n f (blockUnipotent h Y * g) := by
  obtain ⟨C, hC⟩ := exists_rational_of_matrixQuotientMap_eq
    (matrixQuotientMap_matrixLift (matrixQuotientMap Y)).symm
  unfold constantTermIntegrand
  rw [hC, blockUnipotent_add, ← rational_blockUnipotent, mul_assoc, evaluate_rational]

theorem continuous_constantTermIntegrand {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions K n) (g : AdelicGL K n) :
    Continuous (constantTermIntegrand K n h f g) := by
  rw [← (isOpenQuotientMap_matrixQuotientMap (K := K) a b).continuous_comp_iff]
  have hcomp : constantTermIntegrand K n h f g ∘ matrixQuotientMap =
      fun Y => evaluate K n f (blockUnipotent h Y * g) :=
    funext fun Y => constantTermIntegrand_mk h f g Y
  rw [hcomp]
  exact (continuous_evaluate K n f).comp
    ((continuous_blockUnipotent h).mul continuous_const)

theorem integrable_constantTermIntegrand [CompactSpace (AdeleQuotient K)] {a b : ℕ}
    (h : a + b = n) (f : ContinuousRationalFunctions K n) (g : AdelicGL K n) :
    Integrable (constantTermIntegrand K n h f g) (matrixQuotientHaar K a b) := by
  let : MeasurableSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := borel _
  have : BorelSpace (Matrix (Fin a) (Fin b) (AdeleQuotient K)) := ⟨rfl⟩
  have := matrixQuotientHaar_isAddHaarMeasure K a b
  exact (continuous_constantTermIntegrand h f g).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

variable (K n)

/-- The constant term of `f` along the standard `(a, b)` block parabolic:
`g ↦ ∫_{N(K) \ N(𝔸_K)} f(u g) du`, for the normalized Haar probability measure. -/
def constantTerm [CompactSpace (AdeleQuotient K)] {a b : ℕ} (h : a + b = n)
    (f : ContinuousRationalFunctions K n) (g : AdelicGL K n) : ℂ :=
  ∫ X, constantTermIntegrand K n h f g X ∂(matrixQuotientHaar K a b)

/-- A continuous rational-left-invariant function is cuspidal when its constant terms along
every standard maximal block parabolic (`a + b = n`, `a, b ≥ 1`) vanish identically. -/
def IsCuspidal [CompactSpace (AdeleQuotient K)] (f : ContinuousRationalFunctions K n) : Prop :=
  ∀ (a b : ℕ) (h : a + b = n), 0 < a → 0 < b → ∀ g : AdelicGL K n, constantTerm K n h f g = 0

variable {K n}

section Linear

variable [CompactSpace (AdeleQuotient K)] {a b : ℕ} (h : a + b = n)

theorem constantTerm_zero (g : AdelicGL K n) : constantTerm K n h 0 g = 0 := by
  simp [constantTerm, constantTermIntegrand, evaluate]

theorem constantTerm_add (f₁ f₂ : ContinuousRationalFunctions K n) (g : AdelicGL K n) :
    constantTerm K n h (f₁ + f₂) g = constantTerm K n h f₁ g + constantTerm K n h f₂ g :=
  integral_add (integrable_constantTermIntegrand h f₁ g) (integrable_constantTermIntegrand h f₂ g)

theorem constantTerm_smul (c : ℂ) (f : ContinuousRationalFunctions K n) (g : AdelicGL K n) :
    constantTerm K n h (c • f) g = c * constantTerm K n h f g :=
  integral_const_mul c _

theorem constantTerm_rightAction (f : ContinuousRationalFunctions K n) (g x : AdelicGL K n) :
    constantTerm K n h (continuousRightAction K n g f) x = constantTerm K n h f (x * g) := by
  unfold constantTerm constantTermIntegrand
  simp only [evaluate_rightAction, mul_assoc]

end Linear

/-- The cuspidal continuous rational-left-invariant functions, a subrepresentation for right
translation. -/
def cuspidalSubrepresentation [CompactSpace (AdeleQuotient K)] :
    Subrepresentation (continuousRightAction K n) where
  toSubmodule :=
    { carrier := {f | IsCuspidal K n f}
      zero_mem' := fun _ _ h _ _ g => constantTerm_zero h g
      add_mem' := by
        intro f₁ f₂ hf₁ hf₂ a b h ha hb g
        change constantTerm K n h (f₁ + f₂) g = 0
        rw [constantTerm_add h, hf₁ a b h ha hb g, hf₂ a b h ha hb g, add_zero]
      smul_mem' := by
        intro c f hf a b h ha hb g
        change constantTerm K n h (c • f) g = 0
        rw [constantTerm_smul h, hf a b h ha hb g, mul_zero] }
  apply_mem_toSubmodule g f hf a b h ha hb x := by
    rw [constantTerm_rightAction]
    exact hf a b h ha hb (x * g)

end Langlands.Automorphic

import Mathlib.Algebra.Homology.Functor
import Mathlib.Algebra.Homology.Single

/-!
# The functorial cokernel construction

Starting with a coaugmented endofunctor `η : 𝟭 A ⟶ T` of an abelian category,
iterate the cokernel of the coaugmentation and apply `T`. This constructs the
cochain complex used in the Godement construction, including its maps.
Exactness and acyclicity are not assumed in this construction.
-/

noncomputable section

namespace Langlands.Cohomology.CokernelComplex

open CategoryTheory CategoryTheory.Limits

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]
variable (T : A ⥤ A) (η : 𝟭 A ⟶ T)

/-- The successive residual functors, starting with the identity functor. -/
def residual : ℕ → A ⥤ A
  | 0 => 𝟭 A
  | n + 1 => cokernel (Functor.whiskerLeft (residual n) η)

/-- The degree-`n` term of the cokernel construction. -/
def term (n : ℕ) : A ⥤ A :=
  residual T η n ⋙ T

/-- The coaugmentation at the `n`th residual functor. -/
def inclusion (n : ℕ) : residual T η n ⟶ term T η n :=
  Functor.whiskerLeft (residual T η n) η

/-- The genuine categorical cokernel projection at stage `n`. -/
def quotient (n : ℕ) : term T η n ⟶ residual T η (n + 1) :=
  cokernel.π (inclusion T η n)

/-- The differential is a cokernel projection followed by coaugmentation. -/
def differential (n : ℕ) : term T η n ⟶ term T η (n + 1) :=
  quotient T η n ≫ inclusion T η (n + 1)

@[reassoc (attr := simp)]
theorem inclusion_quotient (n : ℕ) :
    inclusion T η n ≫ quotient T η n = 0 :=
  cokernel.condition _

@[reassoc (attr := simp)]
theorem differential_squared (n : ℕ) :
    differential T η n ≫ differential T η (n + 1) = 0 := by
  simp [differential, Category.assoc]

/-- A cochain complex in the category of endofunctors of `A`. -/
def complexOfFunctors : CochainComplex (A ⥤ A) ℕ :=
  CochainComplex.of (term T η) (differential T η) (differential_squared T η)

/-- The constructed cochain complex is functorial in the input object. -/
def functor : A ⥤ CochainComplex A ℕ :=
  (complexOfFunctors T η).asFunctor

/-- The resulting complex on an object `M`. -/
abbrev complex (M : A) : CochainComplex A ℕ :=
  (functor T η).obj M

@[simp]
theorem complex_X (M : A) (n : ℕ) :
    (complex T η M).X n = T.obj ((residual T η n).obj M) :=
  rfl

@[simp]
theorem complex_d (M : A) (n : ℕ) :
    (complex T η M).d n (n + 1) = (differential T η n).app M :=
  NatTrans.congr_app (CochainComplex.of_d (term T η) (differential T η) n) M

/-- The degree-zero coaugmentation from the original object. -/
def augmentation (M : A) : M ⟶ (complex T η M).X 0 :=
  η.app M

@[reassoc (attr := simp)]
theorem augmentation_d (M : A) :
    augmentation T η M ≫ (complex T η M).d 0 1 = 0 := by
  rw [complex_d]
  change (inclusion T η 0 ≫ differential T η 0).app M = 0
  simp [differential]

end Langlands.Cohomology.CokernelComplex

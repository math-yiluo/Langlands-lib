import Langlands.HarmonicAnalysis.Distribution.Basic
import Langlands.Representation.Induction.PermutationDual
import Mathlib.Algebra.Group.Action.End
import Mathlib.Topology.Algebra.ContinuousMonoidHom
import Mathlib.Topology.Algebra.ConstMulAction

/-! # Concrete function, test-function and distribution actions -/

noncomputable section

namespace Langlands.HarmonicAnalysis.GroupAction

open Langlands.Hecke

universe uH uX uG

section Homeomorphisms

variable {H : Type uH} [Group H] {X : Type uX} [TopologicalSpace X]

/-- Inverse pullback on all scalar functions for the actual point action. -/
def functions (α : H →* (X ≃ₜ X)) : Representation ℂ H (X → ℂ) :=
  letI := MulAction.compHom X α
  Langlands.Induction.functionRepresentation (Representation.trivial ℂ H ℂ) X

@[simp] theorem functions_apply (α : H →* (X ≃ₜ X)) (h : H) (f : X → ℂ) (x : X) :
    functions α h f x = f (α h⁻¹ x) := rfl

/-- The restriction of inverse pullback to the existing test-function space. -/
def tests (α : H →* (X ≃ₜ X)) : Representation ℂ H (SchwartzBruhat X) where
  toFun h := (TestFunction.pullback (α h⁻¹)).toLinearMap
  map_one' := by
    ext f x
    simp
  map_mul' h k := by
    ext f x
    simp [mul_inv_rev]

@[simp] theorem tests_apply (α : H →* (X ≃ₜ X)) (h : H)
    (f : SchwartzBruhat X) (x : X) :
    tests α h f x = f (α h⁻¹ x) := rfl

/-- Inclusion into the actual scalar-function space intertwines the two actions. -/
theorem coe_tests (α : H →* (X ≃ₜ X)) (h : H) (f : SchwartzBruhat X) :
    (tests α h f : X → ℂ) = functions α h (f : X → ℂ) := rfl

/-- The actual algebraic-dual representation. -/
def distributions (α : H →* (X ≃ₜ X)) : Representation ℂ H (Distribution X) :=
  (tests α).dual

@[simp] theorem distributions_apply (α : H →* (X ≃ₜ X)) (h : H)
    (D : Distribution X) (f : SchwartzBruhat X) :
    distributions α h D f = D (TestFunction.pullback (α h) f) := by
  change D (TestFunction.pullback (α h⁻¹⁻¹) f) = _
  rw [inv_inv]

/-- Dual inverse pullback is exactly forward pushforward. -/
theorem distributions_eq_pushforward (α : H →* (X ≃ₜ X)) (h : H) :
    distributions α h = (Distribution.pushforward (α h)).toLinearMap := by
  ext D f
  exact distributions_apply α h D f

end Homeomorphisms

section AlgebraicGroup

variable {G : Type uG} [Group G]

/-- All algebraic automorphisms act on scalar functions, with no topology. -/
def automorphismFunctions : Representation ℂ (MulAut G) (G → ℂ) :=
  Langlands.Induction.functionRepresentation
    (Representation.trivial ℂ (MulAut G) ℂ) G

@[simp] theorem automorphismFunctions_apply (a : MulAut G) (f : G → ℂ) (x : G) :
    automorphismFunctions a f x = f (a⁻¹ x) := rfl

/-- Inner automorphisms act through Mathlib's actual conjugation homomorphism. -/
def innerFunctions : Representation ℂ G (G → ℂ) :=
  automorphismFunctions.comp MulAut.conj

theorem innerFunctions_eq_automorphism (g : G) :
    innerFunctions g = automorphismFunctions (MulAut.conj g) := rfl

@[simp] theorem innerFunctions_apply (g : G) (f : G → ℂ) (x : G) :
    innerFunctions g f x = f (g⁻¹ * x * g) := by
  change f ((MulAut.conj g)⁻¹ x) = _
  rw [← map_inv]
  simp

/-- The left point action as actual permutations. -/
def leftPermutations : G →* Equiv.Perm G where
  toFun := Equiv.mulLeft
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp

/-- The right point action has the inverse in its point map. -/
def rightPermutations : G →* Equiv.Perm G where
  toFun g := Equiv.mulRight g⁻¹
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_assoc]

/-- The source's left action on all functions. -/
def leftFunctions : Representation ℂ G (G → ℂ) :=
  letI := MulAction.compHom G (leftPermutations (G := G))
  Langlands.Induction.functionRepresentation (Representation.trivial ℂ G ℂ) G

/-- The source's right action on all functions. -/
def rightFunctions : Representation ℂ G (G → ℂ) :=
  letI := MulAction.compHom G (rightPermutations (G := G))
  Langlands.Induction.functionRepresentation (Representation.trivial ℂ G ℂ) G

@[simp] theorem leftFunctions_apply (g : G) (f : G → ℂ) (x : G) :
    leftFunctions g f x = f (g⁻¹ * x) := rfl

@[simp] theorem rightFunctions_apply (g : G) (f : G → ℂ) (x : G) :
    rightFunctions g f x = f (x * g) := by
  change f (x * g⁻¹⁻¹) = _
  rw [inv_inv]

theorem innerFunctions_eq_left_right (g : G) (f : G → ℂ) :
    innerFunctions g f = leftFunctions g (rightFunctions g f) := by
  ext x
  simp

theorem leftFunctions_rightFunctions (g h : G) (f : G → ℂ) :
    leftFunctions g (rightFunctions h f) = rightFunctions h (leftFunctions g f) := by
  ext x
  simp [mul_assoc]

/-- Unweighted source inversion on all scalar functions. -/
def inversionFunctions : (G → ℂ) ≃ₗ[ℂ] (G → ℂ) where
  toFun f x := f x⁻¹
  invFun f x := f x⁻¹
  left_inv f := by ext x; simp
  right_inv f := by ext x; simp
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem inversionFunctions_apply (f : G → ℂ) (x : G) :
    inversionFunctions f x = f x⁻¹ := rfl

@[simp] theorem inversionFunctions_inversionFunctions (f : G → ℂ) :
    inversionFunctions (inversionFunctions f) = f := by
  ext x
  simp

theorem inversionFunctions_leftFunctions (g : G) (f : G → ℂ) :
    inversionFunctions (leftFunctions g f) = rightFunctions g (inversionFunctions f) := by
  ext x
  simp

theorem inversionFunctions_rightFunctions (g : G) (f : G → ℂ) :
    inversionFunctions (rightFunctions g f) = leftFunctions g (inversionFunctions f) := by
  ext x
  simp

end AlgebraicGroup

section ContinuousAutomorphisms

variable {G : Type uG} [Group G] [TopologicalSpace G]

/-- An actual continuous automorphism specializes the homeomorphism-group action. -/
def continuousAutomorphismTests (a : G ≃ₜ* G) :
    Module.End ℂ (SchwartzBruhat G) :=
  tests (MonoidHom.id (G ≃ₜ G)) a.toHomeomorph

@[simp] theorem continuousAutomorphismTests_apply (a : G ≃ₜ* G)
    (f : SchwartzBruhat G) (x : G) :
    continuousAutomorphismTests a f x = f (a.symm x) := rfl

theorem coe_continuousAutomorphismTests (a : G ≃ₜ* G) (f : SchwartzBruhat G) :
    (continuousAutomorphismTests a f : G → ℂ) =
      automorphismFunctions a.toMulEquiv (f : G → ℂ) := rfl

/-- The same specialization on the actual algebraic distributions. -/
def continuousAutomorphismDistributions (a : G ≃ₜ* G) :
    Module.End ℂ (Distribution G) :=
  distributions (MonoidHom.id (G ≃ₜ G)) a.toHomeomorph

theorem continuousAutomorphismDistributions_eq_pushforward (a : G ≃ₜ* G) :
    continuousAutomorphismDistributions a =
      (Distribution.pushforward a.toHomeomorph).toLinearMap :=
  distributions_eq_pushforward (MonoidHom.id (G ≃ₜ G)) a.toHomeomorph

@[simp] theorem continuousAutomorphismDistributions_apply (a : G ≃ₜ* G)
    (D : Distribution G) (f : SchwartzBruhat G) :
    continuousAutomorphismDistributions a D f =
      D (TestFunction.pullback a.toHomeomorph f) :=
  distributions_apply (MonoidHom.id (G ≃ₜ G)) a.toHomeomorph D f

end ContinuousAutomorphisms

section TopologicalGroup

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The left point action by actual homeomorphisms. -/
def leftHomeomorphisms : G →* (G ≃ₜ G) where
  toFun := Homeomorph.mulLeft
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_assoc]

/-- The right point action uses multiplication by the inverse parameter. -/
def rightHomeomorphisms : G →* (G ≃ₜ G) where
  toFun g := Homeomorph.mulRight g⁻¹
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_assoc]

/-- Actual inner automorphisms form a homeomorphism-valued homomorphism. -/
def innerHomeomorphisms : G →* (G ≃ₜ G) where
  toFun := Distribution.conjugationHomeomorph
  map_one' := by ext x; simp
  map_mul' g h := by ext x; simp [mul_assoc]

@[simp] theorem leftHomeomorphisms_apply (g x : G) :
    leftHomeomorphisms g x = g * x := rfl

@[simp] theorem rightHomeomorphisms_apply (g x : G) :
    rightHomeomorphisms g x = x * g⁻¹ := rfl

@[simp] theorem innerHomeomorphisms_apply (g x : G) :
    innerHomeomorphisms g x = g * x * g⁻¹ := rfl

theorem functions_leftHomeomorphisms (g : G) :
    functions leftHomeomorphisms g = leftFunctions g := by
  ext f x
  rfl

theorem functions_rightHomeomorphisms (g : G) :
    functions rightHomeomorphisms g = rightFunctions g := by
  ext f x
  rfl

theorem functions_innerHomeomorphisms (g : G) :
    functions innerHomeomorphisms g = innerFunctions g := by
  ext f x
  rw [functions_apply]
  change f (g⁻¹ * x * g⁻¹⁻¹) = _
  rw [inv_inv, innerFunctions_apply]

/-- Left translation on tests is an instance of the general construction. -/
def leftTests : Representation ℂ G (SchwartzBruhat G) :=
  tests leftHomeomorphisms

/-- Right translation on tests is an instance of the general construction. -/
def rightTests : Representation ℂ G (SchwartzBruhat G) :=
  tests rightHomeomorphisms

/-- The inner action on tests is an instance of the general construction. -/
def innerTests : Representation ℂ G (SchwartzBruhat G) :=
  tests innerHomeomorphisms

@[simp] theorem leftTests_apply (g : G) (f : SchwartzBruhat G) (x : G) :
    leftTests g f x = f (g⁻¹ * x) := rfl

@[simp] theorem rightTests_apply (g : G) (f : SchwartzBruhat G) (x : G) :
    rightTests g f x = f (x * g) := by
  change f (x * g⁻¹⁻¹) = _
  rw [inv_inv]

@[simp] theorem innerTests_apply (g : G) (f : SchwartzBruhat G) (x : G) :
    innerTests g f x = f (g⁻¹ * x * g) := by
  change f (g⁻¹ * x * g⁻¹⁻¹) = _
  rw [inv_inv]

theorem coe_leftTests (g : G) (f : SchwartzBruhat G) :
    (leftTests g f : G → ℂ) = leftFunctions g (f : G → ℂ) := rfl

theorem coe_rightTests (g : G) (f : SchwartzBruhat G) :
    (rightTests g f : G → ℂ) = rightFunctions g (f : G → ℂ) := rfl

theorem coe_innerTests (g : G) (f : SchwartzBruhat G) :
    (innerTests g f : G → ℂ) = innerFunctions g (f : G → ℂ) := by
  ext x
  simp

theorem leftTests_eq_leftTranslate (g : G) :
    leftTests g = (TestFunction.leftTranslate g).toLinearMap := rfl

theorem rightTests_eq_rightTranslate (g : G) :
    rightTests g = (TestFunction.rightTranslate g).toLinearMap := by
  ext f x
  simp

theorem innerTests_eq_left_right (g : G) (f : SchwartzBruhat G) :
    innerTests g f = leftTests g (rightTests g f) := by
  ext x
  simp

theorem leftTests_rightTests (g h : G) (f : SchwartzBruhat G) :
    leftTests g (rightTests h f) = rightTests h (leftTests g f) := by
  rw [leftTests_eq_leftTranslate, rightTests_eq_rightTranslate]
  exact TestFunction.leftTranslate_rightTranslate g h f

/-- The left action on distributions, obtained by algebraic duality. -/
def leftDistributions : Representation ℂ G (Distribution G) :=
  distributions leftHomeomorphisms

/-- The right action on distributions, obtained by algebraic duality. -/
def rightDistributions : Representation ℂ G (Distribution G) :=
  distributions rightHomeomorphisms

/-- The inner action on distributions, obtained by algebraic duality. -/
def innerDistributions : Representation ℂ G (Distribution G) :=
  distributions innerHomeomorphisms

theorem leftDistributions_eq_pushforward (g : G) :
    leftDistributions g =
      (Distribution.pushforward (Homeomorph.mulLeft g)).toLinearMap :=
  distributions_eq_pushforward leftHomeomorphisms g

theorem rightDistributions_eq_pushforward (g : G) :
    rightDistributions g =
      (Distribution.pushforward (Homeomorph.mulRight g⁻¹)).toLinearMap :=
  distributions_eq_pushforward rightHomeomorphisms g

theorem innerDistributions_eq_pushforward (g : G) :
    innerDistributions g =
      (Distribution.pushforward (Distribution.conjugationHomeomorph g)).toLinearMap :=
  distributions_eq_pushforward innerHomeomorphisms g

@[simp] theorem leftDistributions_apply (g : G) (D : Distribution G)
    (f : SchwartzBruhat G) :
    leftDistributions g D f = D (leftTests g⁻¹ f) := rfl

@[simp] theorem rightDistributions_apply (g : G) (D : Distribution G)
    (f : SchwartzBruhat G) :
    rightDistributions g D f = D (rightTests g⁻¹ f) := rfl

@[simp] theorem innerDistributions_apply (g : G) (D : Distribution G)
    (f : SchwartzBruhat G) :
    innerDistributions g D f = D (innerTests g⁻¹ f) := rfl

theorem isConjugationInvariant_iff_fixed (D : Distribution G) :
    Distribution.IsConjugationInvariant D ↔ ∀ g : G, innerDistributions g D = D := by
  simp only [Distribution.IsConjugationInvariant, innerDistributions_eq_pushforward,
    LinearEquiv.coe_toLinearMap]

end TopologicalGroup

section Inversion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- Source inversion restricted to the actual test functions. -/
abbrev inversionTests : SchwartzBruhat G ≃ₗ[ℂ] SchwartzBruhat G :=
  TestFunction.inversion

@[simp] theorem inversionTests_apply (f : SchwartzBruhat G) (x : G) :
    inversionTests f x = f x⁻¹ := rfl

/-- The restriction has exactly the underlying scalar inversion. -/
theorem coe_inversionTests (f : SchwartzBruhat G) :
    (inversionTests f : G → ℂ) = inversionFunctions (f : G → ℂ) := rfl

/-- Inversion is also the value at inversion of the homeomorphism-group action. -/
theorem inversionTests_eq_tests :
    (inversionTests (G := G)).toLinearMap =
      tests (MonoidHom.id (G ≃ₜ G)) (Homeomorph.inv G) := by
  ext f x
  rfl

@[simp] theorem inversionTests_inversionTests (f : SchwartzBruhat G) :
    inversionTests (inversionTests f) = f :=
  TestFunction.inversion_inversion f

theorem inversionTests_leftTranslate (g : G) (f : SchwartzBruhat G) :
    inversionTests (TestFunction.leftTranslate g f) =
      TestFunction.rightTranslate g (inversionTests f) := by
  ext x
  simp

theorem inversionTests_rightTranslate (g : G) (f : SchwartzBruhat G) :
    inversionTests (TestFunction.rightTranslate g f) =
      TestFunction.leftTranslate g (inversionTests f) := by
  ext x
  simp

theorem inversionTests_leftTests (g : G) (f : SchwartzBruhat G) :
    inversionTests (leftTests g f) = rightTests g (inversionTests f) := by
  rw [leftTests_eq_leftTranslate, rightTests_eq_rightTranslate]
  exact inversionTests_leftTranslate g f

theorem inversionTests_rightTests (g : G) (f : SchwartzBruhat G) :
    inversionTests (rightTests g f) = leftTests g (inversionTests f) := by
  rw [leftTests_eq_leftTranslate, rightTests_eq_rightTranslate]
  exact inversionTests_rightTranslate g f

/-- Source inversion on distributions, using the existing forward pushforward. -/
abbrev inversionDistributions : Distribution G ≃ₗ[ℂ] Distribution G :=
  Distribution.pushforward (Homeomorph.inv G)

theorem inversionDistributions_eq_distributions :
    (inversionDistributions (G := G)).toLinearMap =
      distributions (MonoidHom.id (G ≃ₜ G)) (Homeomorph.inv G) :=
  (distributions_eq_pushforward (MonoidHom.id (G ≃ₜ G)) (Homeomorph.inv G)).symm

@[simp] theorem inversionDistributions_apply (D : Distribution G)
    (f : SchwartzBruhat G) :
    inversionDistributions D f = D (inversionTests f) := rfl

@[simp] theorem inversionDistributions_inversionDistributions (D : Distribution G) :
    inversionDistributions (inversionDistributions D) = D := by
  ext f
  change D (TestFunction.inversion (TestFunction.inversion f)) = D f
  rw [TestFunction.inversion_inversion]

theorem inversionDistributions_pushforward_mulLeft (g : G) (D : Distribution G) :
    inversionDistributions (Distribution.pushforward (Homeomorph.mulLeft g) D) =
      Distribution.pushforward (Homeomorph.mulRight g⁻¹)
        (inversionDistributions D) := by
  ext f
  change D (TestFunction.pullback (Homeomorph.mulLeft g) (inversionTests f)) =
    D (inversionTests (TestFunction.pullback (Homeomorph.mulRight g⁻¹) f))
  congr 1
  ext x
  simp

theorem inversionDistributions_pushforward_mulRight (g : G) (D : Distribution G) :
    inversionDistributions
        (Distribution.pushforward (Homeomorph.mulRight g⁻¹) D) =
      Distribution.pushforward (Homeomorph.mulLeft g)
        (inversionDistributions D) := by
  ext f
  change D (TestFunction.pullback (Homeomorph.mulRight g⁻¹) (inversionTests f)) =
    D (inversionTests (TestFunction.pullback (Homeomorph.mulLeft g) f))
  congr 1
  ext x
  simp

theorem inversionDistributions_leftDistributions (g : G) (D : Distribution G) :
    inversionDistributions (leftDistributions g D) =
      rightDistributions g (inversionDistributions D) := by
  rw [leftDistributions_eq_pushforward, rightDistributions_eq_pushforward]
  exact inversionDistributions_pushforward_mulLeft g D

theorem inversionDistributions_rightDistributions (g : G) (D : Distribution G) :
    inversionDistributions (rightDistributions g D) =
      leftDistributions g (inversionDistributions D) := by
  rw [leftDistributions_eq_pushforward, rightDistributions_eq_pushforward]
  exact inversionDistributions_pushforward_mulRight g D

end Inversion

end Langlands.HarmonicAnalysis.GroupAction

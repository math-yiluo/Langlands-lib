import Langlands.AllFieldBZ.Group.GL.BlockIwahoriDefinitions
import Langlands.AllFieldBZ.Representation.Induction.Parabolic
import Langlands.Representation.Induction.ConjugateParabolic

/-!
# All-field port of `Langlands.Representation.Induction.ConjugateParabolic`

Mechanical port of the field-dependent declarations of the p-adic module
`Langlands.Representation.Induction.ConjugateParabolic` to an arbitrary nonarchimedean local field
(`Langlands.AllFieldBZ.LocalFieldPackage`). See the paired Markdown.
-/
noncomputable section
open CategoryTheory
open scoped NNReal
namespace Langlands.AllFieldBZ.Induction
open Langlands.Induction
universe uR uG uV

variable {R : Type uR} {G : Type uG} {V : Type uV}
variable [CommRing R] [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable [AddCommGroup V] [Module R V]
variable {P Q : Subgroup G} {σ : Representation R P V} {τ : Representation R Q V}

omit [TopologicalSpace G] [IsTopologicalGroup G] in
/-- Inner conjugation by `c` on subgroups, in the inverse direction. -/
private theorem _root_.Langlands.Induction.conjugate_symm_apply (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (q : Q) :
    (e.symm q : G) = c⁻¹ * q * c := by
  have h := he (e.symm q)
  rw [MulEquiv.apply_symm_apply] at h
  rw [h]
  simp [mul_assoc]

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem _root_.Langlands.Induction.conjugate_apply_inv (c : G) (e : P ≃* Q)
    (he : ∀ p : P, (e p : G) = c * p * c⁻¹) (p : P) :
    (e p : G) = c⁻¹⁻¹ * p * c⁻¹ := by
  rw [inv_inv]
  exact he p

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem _root_.Langlands.Induction.conjugate_symm_rep (e : P ≃* Q) (hστ : ∀ p : P, τ (e p) = σ p) (q : Q) :
    σ (e.symm q) = τ q := by
  rw [← hστ, MulEquiv.apply_symm_apply]

end Langlands.AllFieldBZ.Induction
namespace Langlands.AllFieldBZ.Exponents.ConjugateBlockPair
open Langlands.Exponents.ConjugateBlockPair
universe uR

variable {n : ℕ} {R : Type uR} [CommRing R] (P : Langlands.Exponents.ConjugateBlockPair n R)

section Topology
variable [TopologicalSpace R] [IsTopologicalRing R]

end Topology
section Induction
universe uF uV uW uX

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable (Q : Langlands.Exponents.ConjugateBlockPair n F)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

end Induction
end Langlands.AllFieldBZ.Exponents.ConjugateBlockPair
namespace Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
universe uF uV uW uX

variable {F : LocalFieldPackage.{uF}}
variable (T : F.TopologicalData) {n : ℕ} (P : Exponents.ConjugateBlockPair n F.Carrier)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The positive half `δ_B^(1/2)` of the published upper block modulus, transported
to the actual conjugate parabolic along its Levi projection. -/
def conjugateParabolicHalfModulus : P.parabolic →* ℂˣ :=
  (T.leviHalfModulus P.shape).comp P.leviProjection

@[simp]
theorem conjugateParabolicHalfModulus_apply (g : P.parabolic) :
    T.conjugateParabolicHalfModulus P g = T.leviHalfModulus P.shape (P.leviProjection g) := rfl

@[simp]
theorem conjugateParabolicHalfModulus_parabolicEquiv (g : P.shape.parabolic F.Carrier) :
    T.conjugateParabolicHalfModulus P (P.parabolicEquiv g) = T.parabolicHalfModulus P.shape g := by
  simp

@[simp]
theorem conjugateParabolicHalfModulus_section (m : P.shape.Levi F.Carrier) :
    T.conjugateParabolicHalfModulus P (P.leviInParabolic m) = T.leviHalfModulus P.shape m := by
  simp

/-- Normalized induction from the actual conjugate parabolic for an actual p-adic
field: smooth induction by right translation of the transported `δ_B^(1/2) ⊗ σ`. -/
def normalizedConjugateParabolicInduced (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.normalizedInducedOf (T.leviHalfCharacter P.shape) σ

/-- The conjugate induced representation acts by right translation. -/
@[simp]
theorem normalizedConjugateParabolicInduced_apply
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        (T.normalizedConjugateParabolicInduced P σ g f) x =
      Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)) f (x * g) := rfl

/-- The induced map of an actual Levi intertwiner. -/
def normalizedConjugateParabolicInducedMap {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedConjugateParabolicInduced P σ).IntertwiningMap
      (T.normalizedConjugateParabolicInduced P τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.normalizedInducedOfMap (T.leviHalfCharacter P.shape) f

/-- The induced map is postcomposition with the given Levi intertwiner. -/
@[simp]
theorem normalizedConjugateParabolicInducedMap_apply
    {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W} (f : σ.IntertwiningMap τ)
    (φ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (τ.comp P.leviProjection))
        (T.normalizedConjugateParabolicInducedMap P f φ) x =
      f (Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)) φ x) := rfl

@[simp]
theorem normalizedConjugateParabolicInducedMap_id
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedConjugateParabolicInducedMap P (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (T.normalizedConjugateParabolicInduced P σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.normalizedInducedOfMap_id (T.leviHalfCharacter P.shape) σ

@[simp]
theorem normalizedConjugateParabolicInducedMap_comp
    {σ : Representation ℂ (P.shape.Levi F.Carrier) V}
    {τ : Representation ℂ (P.shape.Levi F.Carrier) W}
    {υ : Representation ℂ (P.shape.Levi F.Carrier) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedConjugateParabolicInducedMap P (g.comp f) =
      (T.normalizedConjugateParabolicInducedMap P g).comp
        (T.normalizedConjugateParabolicInducedMap P f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact P.normalizedInducedOfMap_comp (T.leviHalfCharacter P.shape) f g

/-- Left translation `f ↦ (x ↦ f (c⁻¹ * x))` from standard normalized parabolic
induction to normalized induction from the actual conjugate parabolic. -/
def conjugateParabolicInducedEquiv (σ : Representation ℂ (P.shape.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced P.shape σ).Equiv (T.normalizedConjugateParabolicInduced P σ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  P.conjugateInducedEquiv (T.leviHalfCharacter P.shape) σ

@[simp]
theorem conjugateParabolicInducedEquiv_eval (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        (T.conjugateParabolicInducedEquiv P σ f) x =
      Induction.eval (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
        f (P.conjugator⁻¹ * x) := rfl

@[simp]
theorem conjugateParabolicInducedEquiv_symm_eval
    (σ : Representation ℂ (P.shape.Levi F.Carrier) V)
    (h : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection)))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (P.shape.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus P.shape) (σ.comp (P.shape.leviProjection F.Carrier)))
        ((T.conjugateParabolicInducedEquiv P σ).symm h) x =
      Induction.eval P.parabolic
        (twist (T.conjugateParabolicHalfModulus P) (σ.comp P.leviProjection))
        h (P.conjugator * x) := rfl

end Langlands.AllFieldBZ.LocalFieldPackage.TopologicalData
namespace Langlands.AllFieldBZ.LocalFieldPackage
universe uF uV

variable (F : LocalFieldPackage.{uF})
variable {n : ℕ} (P : Exponents.ConjugateBlockPair n F.Carrier)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

end Langlands.AllFieldBZ.LocalFieldPackage

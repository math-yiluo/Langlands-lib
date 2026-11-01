import Langlands.Global.AdelicParabolicInduction
import Langlands.Global.AdelicBlockHeckeCharacter

/-!
# Half-twisted adelic sections induced from actual block Hecke characters
-/

noncomputable section

universe uF

namespace Langlands.Global.AdelicHeckeInduction

open NumberField IsDedekindDomain
open Langlands.GeneralLinear AdelicBlockParabolic

variable (F : Type uF) [Field F] [NumberField F] {n : ℕ} (B : BlockShape n)

/-- The actual continuous covariance character, with the positive half twist. -/
def inducingCharacter (χ : Fin B.length → HeckeCharacter F) : Full F B →ₜ* ℂˣ :=
  AdelicBlockDeterminantCharacter.parabolicHalfCharacter F B *
    AdelicBlockHeckeCharacter.parabolicCharacter F B χ

@[simp]
theorem inducingCharacter_rational (χ : Fin B.length → HeckeCharacter F)
    (p : Rational F B) :
    inducingCharacter F B χ (AdelicBlockParabolic.rational F B p) = 1 := by
  simp [inducingCharacter]

@[simp]
theorem inducingCharacter_unipotent (χ : Fin B.length → HeckeCharacter F)
    (u : B.unipotentRadical (Adeles F)) : inducingCharacter F B χ u = 1 := by
  simp [inducingCharacter]

@[simp]
theorem inducingCharacter_scalar (χ : Fin B.length → HeckeCharacter F) (z : Ideles F) :
    inducingCharacter F B χ (AdelicBlockCenter.scalarParabolic F B z) =
      (AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles z := by
  change AdelicBlockDeterminantCharacter.leviHalfCharacter F B
      (B.leviProjection (Adeles F) (AdelicBlockCenter.scalarParabolic F B z)) *
    AdelicBlockHeckeCharacter.leviCharacter F B χ
      (B.leviProjection (Adeles F) (AdelicBlockCenter.scalarParabolic F B z)) = _
  rw [AdelicBlockCenter.leviProjection_scalar]
  change AdelicBlockDeterminantCharacter.leviHalfCharacter F B
      (fun i => AdelicGL.scalar F (B.size i) z) *
    AdelicBlockHeckeCharacter.leviCharacter F B χ
      (fun i => AdelicGL.scalar F (B.size i) z) = _
  rw [AdelicBlockDeterminantCharacter.leviHalfCharacter_scalar,
    AdelicBlockHeckeCharacter.leviCharacter_scalar, one_mul]

/-- The generic inducing action is multiplication by this concrete character. -/
theorem inducingRepresentation_apply (χ : Fin B.length → HeckeCharacter F)
    (p : Full F B) (v : ℂ) :
    AdelicParabolicInduction.inducingRepresentation F B
      (AdelicBlockHeckeCharacter.leviRepresentation F B χ) p v =
        (inducingCharacter F B χ p : ℂ) * v := by
  change (AdelicBlockDeterminantCharacter.parabolicHalfCharacter F B p : ℂ) *
      ((AdelicBlockHeckeCharacter.parabolicCharacter F B χ p : ℂ) * v) =
    ((AdelicBlockDeterminantCharacter.parabolicHalfCharacter F B p : ℂ) *
      (AdelicBlockHeckeCharacter.parabolicCharacter F B χ p : ℂ)) * v
  exact (mul_assoc _ _ _).symm

/-- Actual covariant complex valued functions, with no regularity imposed yet. -/
abbrev Sections (χ : Fin B.length → HeckeCharacter F) :=
  AdelicParabolicInduction.Sections F B (AdelicBlockHeckeCharacter.leviRepresentation F B χ)

/-- Actual sections with one common open stabilizer in the finite factor. -/
abbrev FiniteSmoothSections (χ : Fin B.length → HeckeCharacter F) :=
  AdelicParabolicInduction.FiniteSmoothSections F B
    (AdelicBlockHeckeCharacter.leviRepresentation F B χ)

/-- Actual sections with smooth archimedean slices and a common finite stabilizer. -/
abbrev SmoothSections (χ : Fin B.length → HeckeCharacter F) :=
  AdelicParabolicInduction.SmoothSections F B
    (AdelicBlockHeckeCharacter.leviRepresentation F B χ)

theorem covariance (χ : Fin B.length → HeckeCharacter F)
    (f : Sections F B χ) (p : Full F B) (g : AdelicGL F n) :
    f.val (p.val * g) = (inducingCharacter F B χ p : ℂ) * f.val g :=
  (f.property p g).trans (inducingRepresentation_apply F B χ p _)

/-- Rational parabolic invariance follows from the actual product formula and Hecke descent. -/
theorem rationalParabolic_invariance (χ : Fin B.length → HeckeCharacter F)
    (f : Sections F B χ) (p : Rational F B) (g : AdelicGL F n) :
    f.val ((AdelicBlockParabolic.rational F B p).val * g) = f.val g := by
  rw [covariance, inducingCharacter_rational, Units.val_one, one_mul]

/-- The supplied scalar Levi action has the actual rank-weighted Hecke character. -/
theorem leviRepresentation_scalar (χ : Fin B.length → HeckeCharacter F)
    (z : Ideles F) (v : ℂ) :
    AdelicBlockHeckeCharacter.leviRepresentation F B χ
      (AdelicBlockCenter.scalarLevi F B z) v =
        ((AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles z : ℂ) • v := by
  change (AdelicBlockHeckeCharacter.leviCharacter F B χ
    (fun i => AdelicGL.scalar F (B.size i) z) : ℂ) * v = _
  rw [AdelicBlockHeckeCharacter.leviCharacter_scalar]
  rfl

/-- The full adelic action on the actual finite-smooth Hecke-induced section space. -/
def finiteSmoothInduced (χ : Fin B.length → HeckeCharacter F) :
    Representation ℂ (AdelicGL F n) (FiniteSmoothSections F B χ) :=
  AdelicParabolicInduction.finiteSmoothInduced F B
    (AdelicBlockHeckeCharacter.leviRepresentation F B χ)

/-- The full adelic action on the actual smooth Hecke-induced section space. -/
def smoothInduced (χ : Fin B.length → HeckeCharacter F) :
    Representation ℂ (AdelicGL F n) (SmoothSections F B χ) :=
  AdelicParabolicInduction.smoothInduced F B
    (AdelicBlockHeckeCharacter.leviRepresentation F B χ)

@[simp]
theorem evaluate_smoothInduced (χ : Fin B.length → HeckeCharacter F)
    (g x : AdelicGL F n) (f : SmoothSections F B χ) :
    (smoothInduced F B χ g f).val.val x = f.val.val (x * g) := rfl

theorem finiteSmoothInduced_scalar (χ : Fin B.length → HeckeCharacter F)
    (z : Ideles F) (f : FiniteSmoothSections F B χ) :
    finiteSmoothInduced F B χ (AdelicGL.scalar F n z) f =
      ((AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles z : ℂ) • f :=
  AdelicParabolicInduction.finiteSmoothInduced_scalar F B _
    (AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles.toMonoidHom
    (leviRepresentation_scalar F B χ) z f

theorem smoothInduced_scalar (χ : Fin B.length → HeckeCharacter F)
    (z : Ideles F) (f : SmoothSections F B χ) :
    smoothInduced F B χ (AdelicGL.scalar F n z) f =
      ((AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles z : ℂ) • f :=
  AdelicParabolicInduction.smoothInduced_scalar F B _
    (AdelicBlockHeckeCharacter.centralCharacter F B χ).onIdeles.toMonoidHom
    (leviRepresentation_scalar F B χ) z f

end Langlands.Global.AdelicHeckeInduction

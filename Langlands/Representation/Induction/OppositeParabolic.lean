import Langlands.Group.GL.PadicOppositeBlocks
import Langlands.Representation.Induction.Parabolic
import Langlands.Representation.Category.Basic
import Langlands.Representation.Induction.Definitions

/-!
# Normalized induction from opposite block parabolics

A representation of the actual block Levi is inflated along the block projection
of the standard lower block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the inverse positive square root of the upper block modulus.
-/

noncomputable section

open CategoryTheory
open scoped NNReal

namespace Langlands.GeneralLinear.BlockShape

universe uF uV uW uX

variable {F : Type uF} [CommRing F] [TopologicalSpace F] [IsTopologicalRing F]
variable {n : ℕ} (B : BlockShape n)
variable {V : Type uV} {W : Type uW} {X : Type uX}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
variable [AddCommGroup X] [Module ℂ X]

/-- A smooth character of the actual Levi, inflated along the block projection. -/
def inflateOppositeCharacter (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    Induction.SmoothCharacter ℂ (B.oppositeParabolic F) where
  toMonoidHom := χ.toMonoidHom.comp (B.oppositeLeviProjection F)
  isOpen_ker := χ.isOpen_ker.preimage (B.oppositeLeviProjectionContinuous F).continuous

@[simp]
theorem inflateOppositeCharacter_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (p : B.oppositeParabolic F) :
    (B.inflateOppositeCharacter χ).toMonoidHom p = χ.toMonoidHom (B.oppositeLeviProjection F p) := rfl

/-- The inducing representation of the parabolic: the Levi action inflated along
the block projection and twisted by the inflated normalizing character. -/
abbrev oppositeInducingRepresentation (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) : Representation ℂ (B.oppositeParabolic F) V :=
  twist (B.inflateOppositeCharacter χ).toMonoidHom (σ.comp (B.oppositeLeviProjection F))

/-- Normalized parabolic induction for a supplied normalizing Levi character. -/
def normalizedOppositeInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ)) :=
  Induction.normalizedSmoothInduced (B.oppositeParabolic F) (B.inflateOppositeCharacter χ)
    (σ.comp (B.oppositeLeviProjection F))

/-- The defining covariance `f (p g) = χ (m p) • σ (m p) (f g)`, where `m` is the
actual Levi projection. -/
theorem normalizedOppositeInducedOf_covariant (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V)
    (f : Induction.SmoothFunctions (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ))
    (p : B.oppositeParabolic F) (g : GeneralLinear n F) :
    Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ) f ((p : GeneralLinear n F) * g) =
      (χ.toMonoidHom (B.oppositeLeviProjection F p) : ℂ) •
        σ (B.oppositeLeviProjection F p)
          (Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ) f g) :=
  f.1.2 p g

/-- The group acts by right translation. -/
@[simp]
theorem normalizedOppositeInducedOf_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) (g : GeneralLinear n F)
    (f : Induction.SmoothFunctions (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ)
        (B.normalizedOppositeInducedOf χ σ g f) x =
      Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ) f (x * g) := rfl

theorem isSmooth_normalizedOppositeInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    IsSmooth (B.normalizedOppositeInducedOf χ σ) :=
  Induction.smoothInduced_smooth _ _

/-- The compactly supported variant: smooth induced functions whose support is
compact modulo the parabolic, with the same normalizing character. -/
def normalizedOppositeCompactInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (GeneralLinear n F)
      (Induction.CompactFunctions (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ)) :=
  Induction.normalizedCompactInduced (B.oppositeParabolic F) (B.inflateOppositeCharacter χ)
    (σ.comp (B.oppositeLeviProjection F))

theorem isSmooth_normalizedOppositeCompactInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    IsSmooth (B.normalizedOppositeCompactInducedOf χ σ) :=
  Induction.compactInduced_smooth _ _

/-- The canonical inclusion of the compactly supported variant. -/
def normalizedOppositeCompactInclusionOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    (B.normalizedOppositeCompactInducedOf χ σ).IntertwiningMap (B.normalizedOppositeInducedOf χ σ) :=
  Induction.compactInclusion (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ)

/-- An actual Levi intertwiner, inflated and twisted to the inducing data. -/
def oppositeInducingMap (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (B.oppositeInducingRepresentation χ σ).IntertwiningMap (B.oppositeInducingRepresentation χ τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun p => f.isIntertwining' (B.oppositeLeviProjection F p) }

/-- Normalized parabolic induction of an actual Levi intertwiner, by postcomposition. -/
def normalizedOppositeInducedOfMap (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (B.normalizedOppositeInducedOf χ σ).IntertwiningMap (B.normalizedOppositeInducedOf χ τ) :=
  Induction.smoothInducedMap (B.oppositeParabolic F) (B.oppositeInducingMap χ f)

@[simp]
theorem normalizedOppositeInducedOfMap_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ)
    (φ : Induction.SmoothFunctions (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ τ)
        (B.normalizedOppositeInducedOfMap χ f φ) x =
      f (Induction.eval (B.oppositeParabolic F) (B.oppositeInducingRepresentation χ σ) φ x) := rfl

@[simp]
theorem normalizedOppositeInducedOfMap_id (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    B.normalizedOppositeInducedOfMap χ (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (B.normalizedOppositeInducedOf χ σ) := by
  ext φ x
  rfl

@[simp]
theorem normalizedOppositeInducedOfMap_comp (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    {υ : Representation ℂ (B.Levi F) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    B.normalizedOppositeInducedOfMap χ (g.comp f) =
      (B.normalizedOppositeInducedOfMap χ g).comp (B.normalizedOppositeInducedOfMap χ f) := by
  ext φ x
  rfl

/-- Normalized parabolic induction as a functor between the canonical smooth
categories of the actual Levi and the actual general linear group. -/
def normalizedOppositeInductionFunctorOf (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) where
  obj A := SmoothRep.of (B.normalizedOppositeInducedOf χ A.representation)
    (B.isSmooth_normalizedOppositeInducedOf χ A.representation)
  map f := SmoothRep.ofHom (B.normalizedOppositeInducedOfMap χ (SmoothRep.hom f))
  map_id A := by
    ext φ x
    rfl
  map_comp f g := by
    ext φ x
    rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
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

/-- The opposite induction half `δ_P^(-1/2)` of the upper block modulus. -/
def oppositeLeviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
  letI := T.leviTopology B
  ⟨Jacquet.inverseHalfCharacter (T.leviModulus B),
    Jacquet.isOpen_ker_inverseHalfCharacter _ (T.isOpen_ker_leviModulus B)⟩

@[simp]
theorem oppositeLeviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.oppositeLeviHalfCharacter B).toMonoidHom = (T.leviHalfModulus B)⁻¹ := rfl

/-- The inverse upper half modulus inflated to the actual opposite parabolic. -/
def oppositeParabolicHalfModulus : B.oppositeParabolic F.Carrier →* ℂˣ :=
  (Jacquet.inverseHalfCharacter (T.leviModulus B)).comp
    (B.oppositeLeviProjection F.Carrier)

@[simp]
theorem oppositeParabolicHalfModulus_apply (g : B.oppositeParabolic F.Carrier) :
    T.oppositeParabolicHalfModulus B g =
      (T.leviHalfModulus B (B.oppositeLeviProjection F.Carrier g))⁻¹ := rfl

@[simp]
theorem oppositeParabolicHalfModulus_section (m : B.Levi F.Carrier) :
    T.oppositeParabolicHalfModulus B (B.oppositeLeviInParabolic F.Carrier m) =
      (T.leviHalfModulus B m)⁻¹ := by
  simp

@[simp]
theorem oppositeParabolicHalfModulus_unipotent
    (u : B.oppositeUnipotentRadical F.Carrier) :
    T.oppositeParabolicHalfModulus B u = 1 := by
  have hu : B.oppositeLeviProjection F.Carrier u = 1 := u.property
  simp [hu]

theorem isOpen_ker_oppositeParabolicHalfModulus :
    letI := T.topology
    IsOpen ((T.oppositeParabolicHalfModulus B).ker :
      Set (B.oppositeParabolic F.Carrier)) := by
  let := T.topology
  exact (Jacquet.isOpen_ker_inverseHalfCharacter _
    (T.isOpen_ker_leviModulus B)).preimage (T.oppositeBlockLeviProjection B).continuous

/-- Normalized parabolic induction `i_(P̄)^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(-1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInducedOf (T.oppositeLeviHalfCharacter B) σ

/-- The covariance `f (p g) = δ_P(m)^(-1/2) σ(m) f(g)` with `m` the Levi part of `p`. -/
theorem normalizedOppositeParabolicInduced_covariant (σ : Representation ℂ (B.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier))))
    (g : B.oppositeParabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier)))
        f ((g : GeneralLinear n F.Carrier) * x) =
      (((NNReal.sqrt (T.leviModulus B (B.oppositeLeviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ))⁻¹ •
        σ (B.oppositeLeviProjection F.Carrier g)
          (Induction.eval (B.oppositeParabolic F.Carrier)
            (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier))) f x) :=
  by
    have h := f.1.2 g x
    change f.1.1 _ =
      (Jacquet.inverseHalfCharacter (T.leviModulus B)
        (B.oppositeLeviProjection F.Carrier g) : ℂ) •
        σ (B.oppositeLeviProjection F.Carrier g) (f.1.1 x) at h
    rw [Jacquet.inverseHalfCharacter_apply] at h
    exact h

/-- The opposite induced representation acts by right translation. -/
@[simp]
theorem normalizedOppositeParabolicInduced_apply
    (σ : Representation ℂ (B.Levi F.Carrier) V)
    (g : GeneralLinear n F.Carrier)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier)))
        (T.normalizedOppositeParabolicInduced B σ g f) x =
      Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))) f (x * g) := rfl

theorem isSmooth_normalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedOppositeInducedOf (T.oppositeLeviHalfCharacter B) σ

/-- The compactly supported variant of `normalizedOppositeParabolicInduced`. -/
def normalizedOppositeParabolicCompactInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.CompactFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B) (σ.comp (B.oppositeLeviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeCompactInducedOf (T.oppositeLeviHalfCharacter B) σ

/-- The canonical inclusion of the compactly supported variant. -/
def normalizedOppositeParabolicCompactInclusion (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedOppositeParabolicCompactInduced B σ).IntertwiningMap
      (T.normalizedOppositeParabolicInduced B σ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeCompactInclusionOf (T.oppositeLeviHalfCharacter B) σ

/-- The induced map of an actual Levi intertwiner. -/
def normalizedOppositeParabolicInducedMap {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedOppositeParabolicInduced B σ).IntertwiningMap (T.normalizedOppositeParabolicInduced B τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInducedOfMap (T.oppositeLeviHalfCharacter B) f

/-- The induced map is postcomposition with the given Levi intertwiner. -/
@[simp]
theorem normalizedOppositeParabolicInducedMap_apply
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ)
    (φ : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))))
    (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (τ.comp (B.oppositeLeviProjection F.Carrier)))
        (T.normalizedOppositeParabolicInducedMap B f φ) x =
      f (Induction.eval (B.oppositeParabolic F.Carrier)
        (twist (T.oppositeParabolicHalfModulus B)
          (σ.comp (B.oppositeLeviProjection F.Carrier))) φ x) := rfl

@[simp]
theorem normalizedOppositeParabolicInducedMap_id
    (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedOppositeParabolicInducedMap B (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (T.normalizedOppositeParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.normalizedOppositeInducedOfMap_id (T.oppositeLeviHalfCharacter B) σ

@[simp]
theorem normalizedOppositeParabolicInducedMap_comp
    {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W}
    {υ : Representation ℂ (B.Levi F.Carrier) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    T.normalizedOppositeParabolicInducedMap B (g.comp f) =
      (T.normalizedOppositeParabolicInducedMap B g).comp
        (T.normalizedOppositeParabolicInducedMap B f) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.normalizedOppositeInducedOfMap_comp (T.oppositeLeviHalfCharacter B) f g

/-- Normalized parabolic induction as a functor of canonical smooth categories. -/
def normalizedOppositeParabolicInductionFunctor :
    letI := T.leviTopology B
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedOppositeInductionFunctorOf (T.oppositeLeviHalfCharacter B)

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Normalized parabolic induction for the canonical realization of every
algebraic p-adic field. -/
abbrev canonicalNormalizedOppositeParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :=
  F.canonicalTopologicalData.normalizedOppositeParabolicInduced B σ

/-- The canonical normalized parabolic induction functor. -/
abbrev canonicalNormalizedOppositeParabolicInductionFunctor :
    letI := F.canonicalLeviTopology B
    letI := F.canonicalGeneralLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.normalizedOppositeParabolicInductionFunctor B

end Langlands.PadicField

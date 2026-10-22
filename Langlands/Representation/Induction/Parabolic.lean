import Langlands.Group.GL.BlockModulus
import Langlands.Representation.Category.Basic
import Langlands.Representation.Induction.Definitions

/-!
# Normalized parabolic induction from standard block Levi subgroups

A representation of the actual block Levi is inflated along the block projection
of the standard upper block parabolic, twisted by the inflated normalizing
character, and smoothly induced by right translation. For p-adic fields the
normalizing character is the positive square root of the explicit block modulus.
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
def inflateCharacter (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    Induction.SmoothCharacter ℂ (B.parabolic F) where
  toMonoidHom := χ.toMonoidHom.comp (B.leviProjection F)
  isOpen_ker := χ.isOpen_ker.preimage (B.leviProjectionContinuous F).continuous

@[simp]
theorem inflateCharacter_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (p : B.parabolic F) :
    (B.inflateCharacter χ).toMonoidHom p = χ.toMonoidHom (B.leviProjection F p) := rfl

/-- The inducing representation of the parabolic: the Levi action inflated along
the block projection and twisted by the inflated normalizing character. -/
abbrev inducingRepresentation (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) : Representation ℂ (B.parabolic F) V :=
  twist (B.inflateCharacter χ).toMonoidHom (σ.comp (B.leviProjection F))

/-- Normalized parabolic induction for a supplied normalizing Levi character. -/
def normalizedInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (GeneralLinear n F)
      (Induction.SmoothFunctions (B.parabolic F) (B.inducingRepresentation χ σ)) :=
  Induction.normalizedSmoothInduced (B.parabolic F) (B.inflateCharacter χ)
    (σ.comp (B.leviProjection F))

/-- The defining covariance `f (p g) = χ (m p) • σ (m p) (f g)`, where `m` is the
actual Levi projection. -/
theorem normalizedInducedOf_covariant (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V)
    (f : Induction.SmoothFunctions (B.parabolic F) (B.inducingRepresentation χ σ))
    (p : B.parabolic F) (g : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ σ) f ((p : GeneralLinear n F) * g) =
      (χ.toMonoidHom (B.leviProjection F p) : ℂ) •
        σ (B.leviProjection F p)
          (Induction.eval (B.parabolic F) (B.inducingRepresentation χ σ) f g) :=
  f.1.2 p g

/-- The group acts by right translation. -/
@[simp]
theorem normalizedInducedOf_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) (g : GeneralLinear n F)
    (f : Induction.SmoothFunctions (B.parabolic F) (B.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ σ)
        (B.normalizedInducedOf χ σ g f) x =
      Induction.eval (B.parabolic F) (B.inducingRepresentation χ σ) f (x * g) := rfl

theorem isSmooth_normalizedInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    IsSmooth (B.normalizedInducedOf χ σ) :=
  Induction.smoothInduced_smooth _ _

/-- The compactly supported variant: smooth induced functions whose support is
compact modulo the parabolic, with the same normalizing character. -/
def normalizedCompactInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    Representation ℂ (GeneralLinear n F)
      (Induction.CompactFunctions (B.parabolic F) (B.inducingRepresentation χ σ)) :=
  Induction.normalizedCompactInduced (B.parabolic F) (B.inflateCharacter χ)
    (σ.comp (B.leviProjection F))

theorem isSmooth_normalizedCompactInducedOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    IsSmooth (B.normalizedCompactInducedOf χ σ) :=
  Induction.compactInduced_smooth _ _

/-- The canonical inclusion of the compactly supported variant. -/
def normalizedCompactInclusionOf (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    (B.normalizedCompactInducedOf χ σ).IntertwiningMap (B.normalizedInducedOf χ σ) :=
  Induction.compactInclusion (B.parabolic F) (B.inducingRepresentation χ σ)

/-- An actual Levi intertwiner, inflated and twisted to the inducing data. -/
def inducingMap (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (B.inducingRepresentation χ σ).IntertwiningMap (B.inducingRepresentation χ τ) :=
  twistIntertwining _
    { toLinearMap := f.toLinearMap
      isIntertwining' := fun p => f.isIntertwining' (B.leviProjection F p) }

/-- Normalized parabolic induction of an actual Levi intertwiner, by postcomposition. -/
def normalizedInducedOfMap (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ) :
    (B.normalizedInducedOf χ σ).IntertwiningMap (B.normalizedInducedOf χ τ) :=
  Induction.smoothInducedMap (B.parabolic F) (B.inducingMap χ f)

@[simp]
theorem normalizedInducedOfMap_apply (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    (f : σ.IntertwiningMap τ)
    (φ : Induction.SmoothFunctions (B.parabolic F) (B.inducingRepresentation χ σ))
    (x : GeneralLinear n F) :
    Induction.eval (B.parabolic F) (B.inducingRepresentation χ τ)
        (B.normalizedInducedOfMap χ f φ) x =
      f (Induction.eval (B.parabolic F) (B.inducingRepresentation χ σ) φ x) := rfl

@[simp]
theorem normalizedInducedOfMap_id (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    (σ : Representation ℂ (B.Levi F) V) :
    B.normalizedInducedOfMap χ (Representation.IntertwiningMap.id σ) =
      Representation.IntertwiningMap.id (B.normalizedInducedOf χ σ) := by
  ext φ x
  rfl

@[simp]
theorem normalizedInducedOfMap_comp (χ : Induction.SmoothCharacter ℂ (B.Levi F))
    {σ : Representation ℂ (B.Levi F) V} {τ : Representation ℂ (B.Levi F) W}
    {υ : Representation ℂ (B.Levi F) X}
    (f : σ.IntertwiningMap τ) (g : τ.IntertwiningMap υ) :
    B.normalizedInducedOfMap χ (g.comp f) =
      (B.normalizedInducedOfMap χ g).comp (B.normalizedInducedOfMap χ f) := by
  ext φ x
  rfl

/-- Normalized parabolic induction as a functor between the canonical smooth
categories of the actual Levi and the actual general linear group. -/
def normalizedInductionFunctorOf (χ : Induction.SmoothCharacter ℂ (B.Levi F)) :
    SmoothRep.{0, uF, uV} ℂ (B.Levi F) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F) where
  obj A := SmoothRep.of (B.normalizedInducedOf χ A.representation)
    (B.isSmooth_normalizedInducedOf χ A.representation)
  map f := SmoothRep.ofHom (B.normalizedInducedOfMap χ (SmoothRep.hom f))
  map_id A := by
    ext φ x
    rfl
  map_comp f g := by
    ext φ x
    rfl

end Langlands.GeneralLinear.BlockShape

namespace Langlands.PadicField.TopologicalData

universe uF uV uW

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
variable (T : F.TopologicalData) {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} {W : Type uW}
variable [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

private theorem isTopologicalRing :
    letI := T.topology
    IsTopologicalRing F.Carrier := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  infer_instance

/-- The positive half `δ_P^(1/2)` of the explicit block modulus, as a smooth Levi
character for the selected realization. -/
def leviHalfCharacter :
    letI := T.leviTopology B
    Induction.SmoothCharacter ℂ (B.Levi F.Carrier) :=
  letI := T.leviTopology B
  ⟨T.leviHalfModulus B, T.isOpen_ker_leviHalfModulus B⟩

@[simp]
theorem leviHalfCharacter_toMonoidHom :
    letI := T.leviTopology B
    (T.leviHalfCharacter B).toMonoidHom = T.leviHalfModulus B := rfl

/-- Normalized parabolic induction `i_P^G σ` for an actual p-adic field: smooth
induction by right translation of `δ_P^(1/2) ⊗ σ`, inflated to the parabolic. -/
def normalizedParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The covariance `f (p g) = δ_P(m)^(1/2) σ(m) f(g)` with `m` the Levi part of `p`. -/
theorem normalizedParabolicInduced_covariant (σ : Representation ℂ (B.Levi F.Carrier) V)
    (f : letI := T.topology
      letI := T.generalLinearTopologicalGroup n
      Induction.SmoothFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))))
    (g : B.parabolic F.Carrier) (x : GeneralLinear n F.Carrier) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Induction.eval (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))
        f ((g : GeneralLinear n F.Carrier) * x) =
      ((NNReal.sqrt (T.leviModulus B (B.leviProjection F.Carrier g) : ℝ≥0) : ℝ) : ℂ) •
        σ (B.leviProjection F.Carrier g)
          (Induction.eval (B.parabolic F.Carrier)
            (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier))) f x) :=
  f.1.2 g x

theorem isSmooth_normalizedParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    IsSmooth (T.normalizedParabolicInduced B σ) := by
  let := T.topology
  let := T.isTopologicalRing
  exact B.isSmooth_normalizedInducedOf (T.leviHalfCharacter B) σ

/-- The compactly supported variant of `normalizedParabolicInduced`. -/
def normalizedParabolicCompactInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    Representation ℂ (GeneralLinear n F.Carrier)
      (Induction.CompactFunctions (B.parabolic F.Carrier)
        (twist (T.parabolicHalfModulus B) (σ.comp (B.leviProjection F.Carrier)))) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedCompactInducedOf (T.leviHalfCharacter B) σ

/-- The canonical inclusion of the compactly supported variant. -/
def normalizedParabolicCompactInclusion (σ : Representation ℂ (B.Levi F.Carrier) V) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicCompactInduced B σ).IntertwiningMap
      (T.normalizedParabolicInduced B σ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedCompactInclusionOf (T.leviHalfCharacter B) σ

/-- The induced map of an actual Levi intertwiner. -/
def normalizedParabolicInducedMap {σ : Representation ℂ (B.Levi F.Carrier) V}
    {τ : Representation ℂ (B.Levi F.Carrier) W} (f : σ.IntertwiningMap τ) :
    letI := T.topology
    letI := T.generalLinearTopologicalGroup n
    (T.normalizedParabolicInduced B σ).IntertwiningMap (T.normalizedParabolicInduced B τ) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInducedOfMap (T.leviHalfCharacter B) f

/-- Normalized parabolic induction as a functor of canonical smooth categories. -/
def normalizedParabolicInductionFunctor :
    letI := T.leviTopology B
    letI := T.generalLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  letI := T.topology
  letI := T.isTopologicalRing
  B.normalizedInductionFunctorOf (T.leviHalfCharacter B)

end Langlands.PadicField.TopologicalData

namespace Langlands.PadicField

universe uF uV

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)
variable {n : ℕ} (B : GeneralLinear.BlockShape n)
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Normalized parabolic induction for the canonical realization of every
algebraic p-adic field. -/
abbrev canonicalNormalizedParabolicInduced (σ : Representation ℂ (B.Levi F.Carrier) V) :=
  F.canonicalTopologicalData.normalizedParabolicInduced B σ

/-- The canonical normalized parabolic induction functor. -/
abbrev canonicalNormalizedParabolicInductionFunctor :
    letI := F.canonicalLeviTopology B
    letI := F.canonicalGeneralLinearTopology n
    SmoothRep.{0, uF, uV} ℂ (B.Levi F.Carrier) ⥤
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier) :=
  F.canonicalTopologicalData.normalizedParabolicInductionFunctor B

end Langlands.PadicField

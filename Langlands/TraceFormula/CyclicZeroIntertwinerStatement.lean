import Langlands.TraceFormula.CyclicInducedActionsStatement
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement

/-! # Global intertwining at zero for the discrete trace summands -/

noncomputable section

open AlgebraicGeometry CategoryTheory MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000

namespace Langlands.TraceFormula.NormOneLeviInduction

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.GroupScheme
open Langlands.Analysis.Meromorphic
open Langlands.Automorphic.GroupSchemeFunctions (innerAdelicPoint)
open scoped CoordinateLevi.Presentation

variable {F : Type} [Field F] [NumberField F] {n : ℕ} {L : CoordinateLevi n}
variable {P : L.Presentation} (D : Model F P)

/-- The root chamber and conjugation on the actual Levi for an ambient rational representative. -/
structure WeylIntertwiningData (F : Type) [Field F] (P : L.Presentation)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (cyclicBaseGroup F n).X) where
  component : CommGroupScheme (Spec (CommRingCat.of F))
  inclusion : component.toGrp ⟶ P.levi F
  roots : ParabolicRootPresentation (P.parabolicInclusion F) (P.leviInclusion F) inclusion
  torus_mono : Mono roots.data.i.hom.hom.left
  weyl_fintype : Fintype (relativeWeylGroup roots.data.i)
  factor_mono : Mono (CommGroupScheme.groupHom roots.data.f).hom.hom.left
  component_split : IsSplitTorus component.toGrp
  torus_split : IsSplitTorus roots.data.T.toGrp
  conjugation : P.levi F ⟶ P.levi F
  represents_weyl : IsWeylConjugation (P.parabolicInclusion F) (P.leviInclusion F)
    (P.parabolicInclusion F) (P.leviInclusion F) w conjugation

namespace WeylIntertwiningData

variable {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ (cyclicBaseGroup F n).X}
variable (C : WeylIntertwiningData F P w)

/-- The global integral has a finite square-integrable expansion from the regular chamber
through the imaginary axis. The chamber in the expansion must be nonempty. -/
def HasExpansion (φ : AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ) : Prop :=
  let : Mono C.roots.data.i.hom.hom.left := C.torus_mono
  letI : Fintype (relativeWeylGroup C.roots.data.i) := C.weyl_fintype
  let : Mono (CommGroupScheme.groupHom C.roots.data.f).hom.hom.left := C.factor_mono
  let j := P.unipotentInclusion F ≫ P.parabolicInclusion F
  ∃ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F (cyclicBaseGroup F n) → ℂ)
      (coeff : Fin k → ComplexCharacterParameter F (P.parabolic F) → ℂ)
      (domain : Set (ComplexCharacterParameter F (P.parabolic F))),
    (∀ i, IsSquareIntegrableInducedForm D.compact D.iwasawa.isCompact (𝟙 (cyclicBaseGroup F n))
      D.smooth D.differential (P.parabolicInclusion F) (P.unipotentInclusion F)
      (P.leviInclusion F) (ψ i)) ∧
    Set.range (imaginaryParameter F (P.parabolic F)) ⊆ domain ∧
    (∀ i, IsMeromorphicInCoordinatesOn (coeff i) domain) ∧
    ∃ R : ℝ, (∃ lam, C.roots.IsRegularParameter C.component_split C.torus_split R lam) ∧
      ∀ lam, C.roots.IsRegularParameter C.component_split C.torus_split R lam → ∀ g,
        Integrable (D.iwasawa.intertwiningIntegrand (P.unipotentInclusion F) j w φ lam g)
          (intertwiningMeasure F (P.parabolicInclusion F) (P.unipotentInclusion F) j
            (innerAdelicPoint F (cyclicBaseGroup F n) w)) ∧
        D.iwasawa.intertwiningOperator D.iwasawa (P.unipotentInclusion F) (P.leviInclusion F)
          (P.unipotentInclusion F) C.conjugation (P.leviProjection F) w φ lam g =
          ∑ i, coeff i lam * ψ i g

/-- The family has the values of the holomorphic continuation of the global
intertwining integral at the imaginary parameters. -/
def IsImaginaryFamily
    (family : (Fin D.parameterDimension → ℝ) → D.ambientInduction →L[ℂ] D.ambientInduction) : Prop :=
  let : Mono C.roots.data.i.hom.hom.left := C.torus_mono
  letI : Fintype (relativeWeylGroup C.roots.data.i) := C.weyl_fintype
  let : Mono (CommGroupScheme.groupHom C.roots.data.f).hom.hom.left := C.factor_mono
  IsImaginaryIntertwiningOperator D.iwasawa D.iwasawa (𝟙 (cyclicBaseGroup F n))
    D.smooth D.differential (P.unipotentInclusion F) (P.leviInclusion F)
    C.inclusion C.roots C.component_split C.torus_split (P.unipotentInclusion F)
    (P.leviInclusion F) (P.leviProjection F) w C.conjugation D.leviHaar D.leviHaar
    D.coordinates D.coordinates D.cutoff D.cutoff family

end WeylIntertwiningData

/-- The zero value of a global family restricted between two supported slices. The
comparison is in their common compact-picture Hilbert space. -/
def IsRestrictedZeroValue
    (family : (Fin D.parameterDimension → ℝ) → D.ambientInduction →L[ℂ] D.ambientInduction)
    {V W : Submodule ℂ (LeviL2 F P)} {t : ℝ}
    (operator : D.hilbertSliceWithSupport V t →L[ℂ] D.hilbertSliceWithSupport W t) : Prop :=
  ∀ v : D.hilbertSliceWithSupport V t,
    (operator v).val = (family 0 (Submodule.inclusion (D.hilbertSliceWithSupport_le V t) v)).val

/-- A regular summand uses the analytic continuation for the specified rational
Weyl representative and its zero value on the full discrete Hilbert slice. -/
def IsRegularZeroIntertwiner (s : CoordinateLevi.Presentation.RegularWeyl L) (t : ℝ)
    (operator : D.hilbertSlice t →L[ℂ] D.hilbertSlice t) : Prop :=
  ∃ (C : WeylIntertwiningData F P (P.weylPoint F s))
    (family : (Fin D.parameterDimension → ℝ) → D.ambientInduction →L[ℂ] D.ambientInduction),
    C.IsImaginaryFamily D family ∧
    (∀ φ, D.IsSectionWithSupport D.leviDiscrete φ → HasImaginaryInfinitesimalNorm F n φ t →
      C.HasExpansion D φ) ∧
    IsRestrictedZeroValue D family operator ∧ (s.val = 1 → operator = 1)

/-- Existence of the global zero operator of (9.2) on the full discrete slice,
with the identity operator for the identity Weyl element. -/
def CyclicZeroIntertwinerStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (n : ℕ), 0 < n →
    ∀ (L : CoordinateLevi n) (P : L.Presentation) (D : Model F P), D.IsStandardCompactPicture →
    ∀ (s : CoordinateLevi.Presentation.RegularWeyl L) (t : ℝ), 0 ≤ t →
    ∃ operator : D.hilbertSlice t →L[ℂ] D.hilbertSlice t, IsRegularZeroIntertwiner D s t operator

end Langlands.TraceFormula.NormOneLeviInduction

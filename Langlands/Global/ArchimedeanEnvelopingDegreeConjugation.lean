import Langlands.Algebra.UniversalEnvelopingFilteredMaps
import Langlands.Global.ArchimedeanEnvelopingFiltration
import Langlands.Global.ArchimedeanAdjoint
import Mathlib.RepresentationTheory.Basic

/-! # Conjugation on actual enveloping degree pieces -/

noncomputable section
universe u
set_option autoImplicit false

namespace Langlands.Global.ArchimedeanGL

variable (K : Type u) [Field K] (n : ℕ)

/-- Every actual archimedean group element preserves each enveloping degree. -/
theorem envelopingConjugation_mem_degreeFiltration (g : InfiniteAdelicGL K n)
    {d : ℕ} {a : EnvelopingAlgebra K n}
    (ha : a ∈ envelopingDegreeFiltration K n d) :
    envelopingConjugation K n g a ∈ envelopingDegreeFiltration K n d := by
  apply Langlands.Algebra.UniversalEnveloping.algHom_mem_degreeFiltration
    ℂ (ComplexLieAlgebra K n) (ComplexLieAlgebra K n)
    (envelopingConjugation K n g).toAlgHom _ ha
  intro X
  change envelopingConjugation K n g (envelopingGenerator K n X) ∈
    envelopingDegreeOne K n
  rw [envelopingConjugation_generator]
  exact Langlands.Algebra.UniversalEnveloping.generator_mem_degreeOne ℂ
    (ComplexLieAlgebra K n) _

@[simp]
theorem envelopingConjugation_mem_degreeFiltration_iff (g : InfiniteAdelicGL K n)
    (d : ℕ) (a : EnvelopingAlgebra K n) :
    envelopingConjugation K n g a ∈ envelopingDegreeFiltration K n d ↔
      a ∈ envelopingDegreeFiltration K n d := by
  constructor
  · intro ha
    simpa using envelopingConjugation_mem_degreeFiltration K n g⁻¹ ha
  · exact envelopingConjugation_mem_degreeFiltration K n g

/-- Restriction of actual conjugation to one degree piece. -/
def envelopingDegreeConjugation (d : ℕ) (g : InfiniteAdelicGL K n) :
    envelopingDegreeFiltration K n d ≃ₗ[ℂ] envelopingDegreeFiltration K n d where
  toFun a := ⟨envelopingConjugation K n g a.val,
    envelopingConjugation_mem_degreeFiltration K n g a.property⟩
  invFun a := ⟨envelopingConjugation K n g⁻¹ a.val,
    envelopingConjugation_mem_degreeFiltration K n g⁻¹ a.property⟩
  left_inv a := Subtype.ext (by simp)
  right_inv a := Subtype.ext (by simp)
  map_add' a b := Subtype.ext (map_add (envelopingConjugation K n g) a.val b.val)
  map_smul' c a := Subtype.ext (map_smul (envelopingConjugation K n g) c a.val)

@[simp]
theorem envelopingDegreeConjugation_coe (d : ℕ) (g : InfiniteAdelicGL K n)
    (a : envelopingDegreeFiltration K n d) :
    (envelopingDegreeConjugation K n d g a : EnvelopingAlgebra K n) =
      envelopingConjugation K n g a.val := rfl

@[simp]
theorem envelopingDegreeConjugation_one (d : ℕ) :
    envelopingDegreeConjugation K n d 1 = LinearEquiv.refl ℂ _ := by
  apply LinearEquiv.ext
  intro a
  apply Subtype.ext
  simp

theorem envelopingDegreeConjugation_mul (d : ℕ) (g h : InfiniteAdelicGL K n) :
    envelopingDegreeConjugation K n d (g * h) =
      (envelopingDegreeConjugation K n d h).trans
        (envelopingDegreeConjugation K n d g) := by
  apply LinearEquiv.ext
  intro a
  apply Subtype.ext
  exact congrArg (fun e => e a.val) (envelopingConjugation_mul K n g h)

@[simp]
theorem envelopingDegreeConjugation_inv (d : ℕ) (g : InfiniteAdelicGL K n) :
    envelopingDegreeConjugation K n d g⁻¹ =
      (envelopingDegreeConjugation K n d g).symm := by
  apply LinearEquiv.ext
  intro a
  rfl

/-- The algebraic full-group representation on a degree piece. -/
def envelopingDegreeRepresentation (d : ℕ) :
    _root_.Representation ℂ (InfiniteAdelicGL K n) (envelopingDegreeFiltration K n d) where
  toFun g := (envelopingDegreeConjugation K n d g).toLinearMap
  map_one' := by
    ext a : 1
    simp
  map_mul' g h := by
    ext a : 1
    exact LinearEquiv.congr_fun (envelopingDegreeConjugation_mul K n d g h) a

/-- The complex linear span of the full actual conjugation orbit. -/
def envelopingConjugationOrbitSpan (a : EnvelopingAlgebra K n) :
    Submodule ℂ (EnvelopingAlgebra K n) :=
  Submodule.span ℂ (Set.range fun g : InfiniteAdelicGL K n => envelopingConjugation K n g a)

theorem envelopingConjugationOrbitSpan_le_degreeFiltration {d : ℕ}
    {a : EnvelopingAlgebra K n} (ha : a ∈ envelopingDegreeFiltration K n d) :
    envelopingConjugationOrbitSpan K n a ≤ envelopingDegreeFiltration K n d := by
  apply Submodule.span_le.mpr
  rintro b ⟨g, rfl⟩
  exact envelopingConjugation_mem_degreeFiltration K n g ha

section NumberField

variable [NumberField K]

/-- Full-group conjugation is algebraically locally finite on the actual algebra. -/
instance envelopingConjugationOrbitSpan_finite (a : EnvelopingAlgebra K n) :
    Module.Finite ℂ (envelopingConjugationOrbitSpan K n a) := by
  obtain ⟨d, hd⟩ := exists_mem_envelopingDegreeFiltration K n a
  exact Submodule.finiteDimensional_of_le
    (envelopingConjugationOrbitSpan_le_degreeFiltration K n hd)

end NumberField

end Langlands.Global.ArchimedeanGL

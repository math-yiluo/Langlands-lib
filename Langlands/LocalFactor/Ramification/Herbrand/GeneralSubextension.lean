import Langlands.LocalFactor.Ramification.Herbrand.GeneralFinite
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.FieldTheory.Normal.Closure

/-!
# Relative inverse Herbrand functions

The same finite Galois field in a common ambient extension supplies the
two finite Herbrand functions. For a finite intermediate field of a
separable closure, use its finite Galois normal closure.
-/

noncomputable section

namespace Langlands.Ramification.Local

universe u₀ uK uE uΩ

section Rebase

variable {K : Type uK} {E : Type uE} {Ω : Type uΩ}
  [Field K] [Field E] [Field Ω] [Algebra K E] [Algebra E Ω] [Algebra K Ω]
  [IsScalarTower K E Ω]

/-- A finite Galois field over `K` containing the image of `E`, viewed over `E`. -/
def extendFiniteGalois {M : FiniteGaloisIntermediateField K Ω}
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) :
    FiniteGaloisIntermediateField E Ω :=
  have : FiniteDimensional K (M.toIntermediateField.toSubfield.toIntermediateField h) :=
    M.finiteDimensional
  have : IsGalois K (M.toIntermediateField.toSubfield.toIntermediateField h) := M.isGalois
  { toIntermediateField := M.toIntermediateField.toSubfield.toIntermediateField h
    finiteDimensional := Module.Finite.of_restrictScalars_finite K _ _
    isGalois := IsGalois.tower_top_of_isGalois K E _ }

/-- The identity of the two carriers as a `K`-algebra equivalence. -/
def extendFiniteGaloisEquiv {M : FiniteGaloisIntermediateField K Ω}
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) :
    M ≃ₐ[K] extendFiniteGalois h where
  toFun x := ⟨x, x.property⟩
  invFun x := ⟨x, x.property⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl
  map_add' _ _ := rfl
  commutes' _ := rfl

end Rebase

section RelativeIndex

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (K : Type uK) {E : Type uE} {Ω : Type uΩ}
  [Field K] [Field E] [Field Ω] [Algebra K₀ K] [FiniteDimensional K₀ K]
  [Algebra K E] [Algebra E Ω] [Algebra K Ω] [IsScalarTower K E Ω]
  [Algebra K₀ E] [Algebra K₀ Ω] [IsScalarTower K₀ K Ω] [IsScalarTower K₀ E Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)

/-- The relative index `φ_{M/E} ∘ ψ_{M/K}`, using one realization of `M` over `K₀`. -/
def relativeIndex (M : FiniteGaloisIntermediateField K Ω)
    (h : ∀ x : E, algebraMap E Ω x ∈ M.toIntermediateField) (v : ℝ) : ℝ :=
  let N := extendFiniteGalois h
  have : FiniteDimensional K N := M.finiteDimensional
  have : IsScalarTower K₀ K N := IsScalarTower.of_algebraMap_eq fun a => Subtype.ext
    (IsScalarTower.algebraMap_apply K₀ K Ω a)
  have : FiniteDimensional K₀ N := FiniteDimensional.trans K₀ K N
  let T := LocalField.canonicalTopologicalData K₀ N hbase
  herbrandPhi T E (herbrandPsi T K v)

end RelativeIndex

section NormalClosure

variable {K : Type uK} {Ω : Type uΩ} [Field K] [Field Ω] [Algebra K Ω]
  [IsSepClosure K Ω] (E : IntermediateField K Ω) [FiniteDimensional K E]

/-- The finite Galois normal closure of `E/K` in the given separable closure. -/
def galoisClosure : FiniteGaloisIntermediateField K Ω :=
  have : IsGalois K Ω := IsSepClosure.isGalois
  { toIntermediateField := IntermediateField.normalClosure K E Ω
    finiteDimensional := normalClosure.is_finiteDimensional K E Ω
    isGalois := IsGalois.normalClosure K E Ω }

/-- The image of the finite intermediate field lies in its normal closure. -/
theorem algebraMap_mem_galoisClosure (x : E) :
    algebraMap E Ω x ∈ (galoisClosure E).toIntermediateField :=
  IntermediateField.le_normalClosure E x.property

end NormalClosure

section RelativePsi

variable (K₀ : Type u₀) [NontriviallyNormedField K₀] [IsUltrametricDist K₀]
  [CompleteSpace K₀] [ValuativeRel K₀] [LocallyCompactSpace K₀]
  (K : Type uK) [Field K] [Algebra K₀ K] [FiniteDimensional K₀ K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  [Algebra K₀ Ω] [IsScalarTower K₀ K Ω]
  (hbase : ∀ a b : K₀, ‖a‖ ≤ ‖b‖ ↔ ValuativeRel.vle a b)
  (E : IntermediateField K Ω) [FiniteDimensional K E]

/-- The relative inverse Herbrand function in the finite Galois normal closure of `E/K`. -/
def relativeHerbrandPsi (v : ℝ) : ℝ :=
  have : IsScalarTower K₀ E Ω := IsScalarTower.of_algebraMap_eq fun _ => rfl
  relativeIndex K₀ K hbase (galoisClosure E) (algebraMap_mem_galoisClosure E) v

end RelativePsi

section LocalField

variable (K : Type uK) [Field K] [ValuativeRel K] [TopologicalSpace K]
  [IsNonarchimedeanLocalField K]
  (Ω : Type uΩ) [Field Ω] [Algebra K Ω] [IsSepClosure K Ω]
  (E : IntermediateField K Ω) [FiniteDimensional K E]

/-- The relative inverse Herbrand function over a nonarchimedean local field. -/
def localRelativeHerbrandPsi (v : ℝ) : ℝ := by
  letI := LocalGalois.localNormedField K
  letI := LocalGalois.localNormedField_ultrametric K
  letI := LocalGalois.localNormedField_complete K
  exact relativeHerbrandPsi K K Ω
    (fun a b => (LocalGalois.localNormedField_le K a b).trans
      (Valuation.Compatible.vle_iff_le a b).symm) E v

end LocalField

end Langlands.Ramification.Local

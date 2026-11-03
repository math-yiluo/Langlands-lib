import Langlands.Representation.Aubert.General.SemidirectHaarModulus
import Mathlib.MeasureTheory.Group.ModularCharacter
import Langlands.Cohomology.Continuous.InnerConjugation

/-! # Modular characters in continuous semidirect coordinates -/

noncomputable section

open MeasureTheory MeasureTheory.Measure
open scoped NNReal

universe u

namespace Langlands.Aubert.General

section Conjugation

variable {H : Type u} [Group H] [TopologicalSpace H] [IsTopologicalGroup H]

/-- Inner conjugation as a continuous multiplicative equivalence. -/
def innerConjugation (g : H) : H ≃ₜ* H :=
  Langlands.Continuous.innerConjugationEquiv g

variable [LocallyCompactSpace H]

local instance instSemidirectModularCharacter1 : MeasurableSpace H := borel H
local instance instSemidirectModularCharacter2 : BorelSpace H := ⟨rfl⟩

/-- Mathlib's modular character is the Haar modulus of inner conjugation,
with the same orientation as the Library's normalizer character. -/
theorem modularCharacter_eq_innerConjugation (g : H) :
    modularCharacter g = mulEquivHaarChar (innerConjugation g) := by
  let μ : Measure H := haar
  let e := innerConjugation g
  have hmap : μ.map e.symm = μ.map (· * g) := by
    change μ.map ((fun x : H => x * g) ∘ (fun x : H => g⁻¹ * x)) = _
    rw [← Measure.map_map (measurable_mul_const g) (measurable_const_mul g⁻¹),
      map_mul_left_eq_self]
  have hscale : mulEquivHaarChar e • μ = μ.map (· * g) := by
    rw [mulEquivHaarChar_smul_eq_comap μ e]
    let em := e.toHomeomorph.toMeasurableEquiv
    change μ.comap em = _
    rw [← em.map_symm]
    exact hmap
  change modularCharacterFun g = _
  rw [modularCharacterFun_eq_haarScalarFactor μ g]
  rw! [← hscale]
  simp [haarScalarFactor_smul, e]

end Conjugation

namespace IsSemidirectDecomposition

variable {G : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SecondCountableTopology G]
  {P M U : Subgroup G} (h : IsSemidirectDecomposition P M U)
  (hp : Continuous h.projection)
  [LocallyCompactSpace M] [LocallyCompactSpace U] [LocallyCompactSpace P]

local instance modularSubgroupMeasurableSpace (H : Subgroup G) : MeasurableSpace H := borel H
local instance modularSubgroupBorelSpace (H : Subgroup G) : BorelSpace H := ⟨rfl⟩
local instance modularSubgroupSecondCountable (H : Subgroup G) : SecondCountableTopology H :=
  TopologicalSpace.Subtype.secondCountableTopology (H : Set G)
local instance modularProductBorelSpace : BorelSpace (M × U) := Prod.borelSpace

include hp

/-- Right translation by a radical element acts only on the second coordinate,
so the ambient modular character restricts to the radical modular character. -/
theorem modularCharacter_unipotent (u : U) :
    modularCharacter (⟨u, h.unipotent_le u.property⟩ : P) =
      modularCharacter u := by
  let μM : Measure M := haar
  let μU : Measure U := haar
  let μ : Measure (M × U) := μM.prod μU
  let e := h.coordinates hp
  let ν : Measure P := μ.map e
  let pu : P := ⟨u, h.unipotent_le u.property⟩
  let r : M × U → M × U := Prod.map id (fun v : U => v * u)
  have : ν.IsHaarMeasure := h.coordinates_isHaarMeasure hp μM μU
  have he : Measurable (e : M × U → P) := e.continuous.measurable
  have hr : Measurable r := measurable_id.prodMap (measurable_mul_const u)
  have hprod : μ.map r = modularCharacter u • μ := by
    change (μM.prod μU).map (Prod.map id (fun v : U => v * u)) =
      modularCharacter u • μM.prod μU
    rw [← Measure.map_prod_map μM μU measurable_id (measurable_mul_const u),
      Measure.map_id, map_right_mul_eq_modularCharacterFun_smul μU,
      Measure.prod_smul_right]
    rfl
  have hcoord : (fun q : P => q * pu) ∘ e = e ∘ r := by
    funext x
    apply Subtype.ext
    change ((x.1 : G) * (x.2 : G)) * (u : G) =
      (x.1 : G) * ((x.2 : G) * (u : G))
    exact mul_assoc _ _ _
  have hscale : ν.map (fun q : P => q * pu) = modularCharacter u • ν := by
    calc
      _ = (μ.map r).map e := by
        change (μ.map e).map (fun q : P => q * pu) = _
        rw [Measure.map_map (measurable_mul_const pu) he, hcoord,
          ← Measure.map_map he hr]
      _ = _ := by rw [hprod, Measure.map_smul _ he.aemeasurable]
  change modularCharacterFun pu = _
  rw [modularCharacterFun_eq_haarScalarFactor ν]
  rw! [hscale]
  simp [haarScalarFactor_smul]

/-- On the Levi factor, the parabolic modular character is the product of the
Levi modular character and its action modulus on the radical. -/
theorem modularCharacter_levi (m : M) :
    modularCharacter (⟨m, h.levi_le m.property⟩ : P) =
      modularCharacter m *
        (HaarModulus.restrictCharacter U M h.levi_le_normalizer m : ℝ≥0) := by
  rw [modularCharacter_eq_innerConjugation, modularCharacter_eq_innerConjugation]
  change mulEquivHaarChar (innerConjugation (⟨m, h.levi_le m.property⟩ : P)) =
    mulEquivHaarChar (innerConjugation m) *
      mulEquivHaarChar (HaarModulus.normalizerConj U
        ⟨m, h.levi_le_normalizer m.property⟩)
  apply h.haarChar_eq_mul hp
  intro m' u
  apply Subtype.ext
  simp [innerConjugation, HaarModulus.normalizerConj, mul_assoc]

/-- Equality on both factors identifies the modular character on the whole
semidirect product. The radical hypotheses are stated inside the actual `P`. -/
theorem modularCharacter_eq_restrictCharacter
    (hM : ∀ m : M, modularCharacter m = 1)
    (hU : ∀ u : U, modularCharacter (⟨u, h.unipotent_le u.property⟩ : P) = 1)
    (hδU : ∀ u : U, HaarModulus.normalizerCharacter U
      ⟨u, Subgroup.le_normalizer u.property⟩ = 1)
    (p : P) :
    modularCharacter p =
      (HaarModulus.restrictCharacter U P h.le_normalizer p : ℝ≥0) := by
  let m := h.projection p
  let u : U := ⟨(m : G)⁻¹ * (p : G), h.projection_inv_mul_mem p⟩
  have hpu : p = (⟨m, h.levi_le m.property⟩ : P) *
      ⟨u, h.unipotent_le u.property⟩ := by
    apply Subtype.ext
    simp [u]
  rw [hpu, map_mul, map_mul, Units.val_mul,
    h.modularCharacter_levi hp, hM, hU, one_mul, mul_one]
  have hu : HaarModulus.restrictCharacter U P h.le_normalizer
      ⟨u, h.unipotent_le u.property⟩ = 1 := hδU u
  rw [hu, Units.val_one, mul_one]
  rfl

/-- For unimodular factors, the semidirect modular character is exactly the
normalizer Haar modulus on the radical. -/
theorem modularCharacter_eq_restrictCharacter_of_unimodular
    (hM : ∀ m : M, modularCharacter m = 1)
    (hδU : ∀ u : U, HaarModulus.normalizerCharacter U
      ⟨u, Subgroup.le_normalizer u.property⟩ = 1)
    (p : P) :
    modularCharacter p =
      (HaarModulus.restrictCharacter U P h.le_normalizer p : ℝ≥0) := by
  apply h.modularCharacter_eq_restrictCharacter hp hM ?_ hδU p
  intro u
  rw [h.modularCharacter_unipotent hp, modularCharacter_eq_innerConjugation]
  have he : innerConjugation u =
      HaarModulus.normalizerConj U ⟨u, Subgroup.le_normalizer u.property⟩ := by
    ext v
    rfl
  rw [he]
  exact congrArg Units.val (hδU u)

end IsSemidirectDecomposition

end Langlands.Aubert.General

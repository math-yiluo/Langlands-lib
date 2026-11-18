import Langlands.BushnellKutzko.SubfieldIntegerArithmetic
import Langlands.BushnellKutzko.SubfieldIntegers
import Langlands.Galois.Local.SpectralProof
import Langlands.LocalField.FiniteExtension

/-! # The integer ring of the field acting on a lattice chain -/

noncomputable section

open Module ValuativeRel Langlands.LocalField

namespace Langlands.BushnellKutzko

universe uF uE

variable (F : Type uF) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  (E : Type uE) [Field E] [Algebra F E] [FiniteDimensional F E]

open LocalGalois in
/-- The integral closure in a finite extension is the closed unit ball for its spectral norm. -/
theorem mem_subfieldIntegers_iff_norm_le_one (x : E) :
    letI := Langlands.LocalField.FiniteExtension.normedField F E
    x ∈ subfieldIntegers F E ↔ ‖x‖ ≤ 1 := by
  let := localNormedField F
  let := localNormedField_ultrametric F
  let := localNormedField_complete F
  let := Langlands.LocalField.FiniteExtension.normedField F E
  let e : baseIntegers F ≃+* 𝒪[F] := RingEquiv.subringCongr (localNormedField_integer F)
  change IsIntegral 𝒪[F] x ↔ ‖x‖ ≤ 1
  rw [← show IsIntegral (baseIntegers F) x ↔ ‖x‖ ≤ 1 from
    integral_iff_mem_spectralIntegers F E x]
  constructor
  · intro hx
    exact IsIntegral.map_of_comp_eq e.symm.toRingHom (RingHom.id E)
      (by ext y; rfl) hx
  · intro hx
    exact IsIntegral.map_of_comp_eq e.toRingHom (RingHom.id E)
      (by ext y; rfl) hx

open Langlands.LocalField.FiniteExtension in
/-- The published integral closure and the spectral valuation ring have the same elements. -/
def subfieldIntegersEquiv :
    letI := FiniteExtension.valuativeRel F E
    subfieldIntegers F E ≃+* 𝒪[E] :=
  subfieldIntegerEquiv F E

attribute [instance] subfieldIntegers_isDiscreteValuationRing subfieldIntegers_isFractionRing

open Langlands.LocalField.FiniteExtension in
/-- A nonzero base scalar can move any element of the extension into its integer ring. -/
theorem exists_smul_mem_subfieldIntegers (x : E) :
    ∃ a : F, a ≠ 0 ∧ a • x ∈ subfieldIntegers F E := by
  let := LocalGalois.localNormedField F
  let := normedField F E
  let := normedAlgebra F E
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm F ‖x‖
  have ha' : 0 < ‖a‖ := (norm_nonneg x).trans_lt ha
  use a⁻¹, inv_ne_zero (norm_pos_iff.mp ha')
  rw [mem_subfieldIntegers_iff_norm_le_one F E, norm_smul, norm_inv, ← div_eq_inv_mul]
  exact (div_le_one₀ ha').mpr ha.le

open Langlands.LocalField.FiniteExtension in
/-- The integer ring is a finite module over the base integers, including for inseparable extensions. -/
instance subfieldIntegers_finite : Module.Finite 𝒪[F] (subfieldIntegers F E) := by
  let := LocalGalois.localNormedField F
  let := LocalGalois.localNormedField_complete F
  let := LocalGalois.localNormedField_ultrametric F
  let := normedField F E
  let := normedAlgebra F E
  let b := Module.finBasis F E
  let f := b.equivFunL.toContinuousLinearMap
  obtain ⟨a, ha⟩ := NormedField.exists_lt_norm F ‖f‖
  have ha' : 0 < ‖a‖ := (norm_nonneg _).trans_lt ha
  let g := a⁻¹ • f.toLinearMap
  have hbase (y : F) : y ∈ (valuation F).integer ↔ ‖y‖ ≤ 1 := by
    rw [← LocalGalois.localNormedField_integer F]
    rfl
  have hg (x : subfieldIntegers F E) (i : Fin (finrank F E)) :
      g (x : E) i ∈ (valuation F).integer := by
    apply (hbase _).mpr
    change ‖a⁻¹ * f (x : E) i‖ ≤ 1
    rw [norm_mul, norm_inv, ← div_eq_inv_mul, div_le_iff₀ ha', one_mul]
    have hx : ‖(x : E)‖ ≤ 1 :=
      (mem_subfieldIntegers_iff_norm_le_one F E (x : E)).mp x.property
    calc
      ‖f (x : E) i‖ ≤ ‖f (x : E)‖ := norm_le_pi_norm (f (x : E)) i
      _ ≤ ‖f‖ * ‖(x : E)‖ := f.le_opNorm (x : E)
      _ ≤ ‖f‖ := mul_le_of_le_one_right (norm_nonneg f) hx
      _ ≤ ‖a‖ := ha.le
  let h : subfieldIntegers F E →ₗ[𝒪[F]] Fin (finrank F E) → 𝒪[F] :=
    { toFun := fun x i => ⟨g (x : E) i, hg x i⟩
      map_add' := by
        intro x y
        funext i
        apply Subtype.ext
        exact congrFun (g.map_add (x : E) (y : E)) i
      map_smul' := by
        intro c x
        funext i
        apply Subtype.ext
        exact congrFun (g.map_smul (c : F) (x : E)) i }
  apply Module.Finite.of_injective h
  intro x y hxy
  apply Subtype.ext
  apply b.equivFunL.injective
  apply smul_right_injective (Fin (finrank F E) → F)
    (inv_ne_zero (norm_pos_iff.mp ha'))
  funext i
  exact congrArg (fun z : 𝒪[F] => (z : F)) (congrFun hxy i)

end Langlands.BushnellKutzko

import Langlands.Global.Arithmetic.IdeleSUnits
import Langlands.Global.Adelic
import Mathlib.Topology.Algebra.RestrictedProduct.Units

/-! # The actual product topology on S-unit ideles -/

noncomputable section

universe u

namespace Langlands.Global.Arithmetic.SUnitIdeleTopology

open NumberField IsDedekindDomain
open Langlands.ClassField.Global IdeleSUnits
open scoped RestrictedProduct

variable (K : Type u) [Field K] [NumberField K]

/-- The unrestricted local unit group at a place of `S`, and valuation units elsewhere. -/
def localFactor (S : Finset (FinitePlace K)) (v : FinitePlace K) :
    Subgroup (FiniteCompletion K v)ˣ := by
  classical
  exact if v ∈ S then ⊤ else localUnits v

theorem mem_localFactor_iff (S : Finset (FinitePlace K)) (v : FinitePlace K)
    (x : (FiniteCompletion K v)ˣ) :
    x ∈ localFactor K S v ↔ v ∉ S → Valued.v (x : FiniteCompletion K v) = 1 := by
  classical
  by_cases hv : v ∈ S
  · simp [localFactor, hv]
  · simp [localFactor, hv, mem_localUnits_iff]

/-- The product of the finite local factors, with the product topology. -/
abbrev finiteModel (S : Finset (FinitePlace K)) := (v : FinitePlace K) → localFactor K S v

/-- The whole infinite factor together with the finite local factors. -/
abbrev model (S : Finset (FinitePlace K)) := (InfiniteAdeles K)ˣ × finiteModel K S

private theorem factor_integral (S : Finset (FinitePlace K)) (v : FinitePlace K)
    (hv : v ∉ S) (x : localFactor K S v) :
    ((x : (FiniteCompletion K v)ˣ) : FiniteCompletion K v) ∈ v.adicCompletionIntegers K := by
  change Valued.v (x.1 : FiniteCompletion K v) ≤ 1
  exact ((mem_localFactor_iff K S v x.1).1 x.2 hv).le

private def stageValue (S : Finset (FinitePlace K)) (x : finiteModel K S) :
    Πʳ v : FinitePlace K, [FiniteCompletion K v, v.adicCompletionIntegers K]_[
      Filter.principal (S : Set (FinitePlace K))ᶜ] :=
  ⟨fun v => ((x v : (FiniteCompletion K v)ˣ) : FiniteCompletion K v),
    fun v hv => factor_integral K S v hv (x v)⟩

private theorem continuous_stageValue (S : Finset (FinitePlace K)) :
    Continuous (stageValue K S) := by
  apply RestrictedProduct.continuous_rng_of_principal.mpr
  exact continuous_pi fun v =>
    Units.continuous_val.comp (continuous_subtype_val.comp (continuous_apply v))

omit [NumberField K] in
private theorem stageFilter (S : Finset (FinitePlace K)) :
    Filter.cofinite ≤ Filter.principal (S : Set (FinitePlace K))ᶜ :=
  Filter.le_principal_iff.2 S.finite_toSet.compl_mem_cofinite

private def finiteValue (S : Finset (FinitePlace K)) (x : finiteModel K S) :
    FiniteAdeles K :=
  RestrictedProduct.inclusion _ _ (stageFilter K S) (stageValue K S x)

private theorem continuous_finiteValue (S : Finset (FinitePlace K)) :
    Continuous (finiteValue K S) :=
  (RestrictedProduct.continuous_inclusion (stageFilter K S)).comp (continuous_stageValue K S)

/-- Assemble the finite coordinates into a unit of the actual finite adele ring. -/
def finiteAssemble (S : Finset (FinitePlace K)) : finiteModel K S →* FiniteIdeles K where
  toFun x :=
    { val := finiteValue K S x
      inv := finiteValue K S x⁻¹
      val_inv := RestrictedProduct.ext _ _ fun v => Units.mul_inv (x v).1
      inv_val := RestrictedProduct.ext _ _ fun v => Units.inv_mul (x v).1 }
  map_one' := by apply Units.ext; ext v; rfl
  map_mul' x y := by apply Units.ext; ext v; rfl

theorem continuous_finiteAssemble (S : Finset (FinitePlace K)) :
    Continuous (finiteAssemble K S) :=
  Units.continuous_iff.2
    ⟨continuous_finiteValue K S, (continuous_finiteValue K S).comp continuous_inv⟩

/-- Assemble all coordinates into the actual idele group. -/
def assemble (S : Finset (FinitePlace K)) : model K S →* Ideles K :=
  (ideleProductEquiv K).symm.toMonoidHom.comp
    ((MonoidHom.id (InfiniteAdeles K)ˣ).prodMap (finiteAssemble K S))

theorem continuous_assemble (S : Finset (FinitePlace K)) :
    Continuous (assemble K S) :=
  (ideleProductEquiv K).symm.continuous.comp
    (continuous_id.prodMap (continuous_finiteAssemble K S))

@[simp] theorem finiteIdeleProjection_assemble (S : Finset (FinitePlace K))
    (x : model K S) (v : FinitePlace K) :
    finiteIdeleProjection K v (assemble K S x) = (x.2 v).1 := rfl

theorem assemble_mem_sUnitIdeles (S : Finset (FinitePlace K)) (x : model K S) :
    assemble K S x ∈ sUnitIdeles K S := by
  apply mem_sUnitIdeles_iff.2
  intro v hv
  apply (ideleExponent_eq_one_iff v _).2
  exact (mem_localFactor_iff K S v (x.2 v).1).1 (x.2 v).2 hv

/-- Assemble directly into the subgroup of S-unit ideles. -/
def toSUnitIdeles (S : Finset (FinitePlace K)) : model K S →* sUnitIdeles K S :=
  (assemble K S).codRestrict _ (assemble_mem_sUnitIdeles K S)

theorem continuous_toSUnitIdeles (S : Finset (FinitePlace K)) :
    Continuous (toSUnitIdeles K S) :=
  (continuous_assemble K S).subtype_mk _

/-- Read the local coordinates of an actual S-unit idele. -/
def fromSUnitIdeles (S : Finset (FinitePlace K)) : sUnitIdeles K S →* model K S where
  toFun x := ((ideleProductEquiv K x.1).1, fun v =>
    ⟨finiteIdeleProjection K v x.1, (mem_localFactor_iff K S v _).2 fun hv =>
      (ideleExponent_eq_one_iff v x.1).1 (mem_sUnitIdeles_iff.1 x.2 v hv)⟩)
  map_one' := by apply Prod.ext <;> rfl
  map_mul' x y := by apply Prod.ext <;> rfl

theorem continuous_fromSUnitIdeles (S : Finset (FinitePlace K)) :
    Continuous (fromSUnitIdeles K S) := by
  apply Continuous.prodMk
  · exact (continuous_fst.comp (ideleProductEquiv K).continuous).comp continuous_subtype_val
  · apply continuous_pi
    intro v
    exact ((finiteIdeleProjection K v).continuous.comp continuous_subtype_val).subtype_mk _

/-- The product model is a topological group isomorphism for the actual subgroup topology. -/
def productEquiv (S : Finset (FinitePlace K)) : model K S ≃ₜ* sUnitIdeles K S where
  toFun := toSUnitIdeles K S
  invFun := fromSUnitIdeles K S
  left_inv x := by
    apply Prod.ext
    · rfl
    · funext v; rfl
  right_inv x := by
    apply Subtype.ext
    apply Units.ext
    apply Prod.ext
    · rfl
    · ext v; rfl
  map_mul' := (toSUnitIdeles K S).map_mul
  continuous_toFun := continuous_toSUnitIdeles K S
  continuous_invFun := continuous_fromSUnitIdeles K S

set_option backward.isDefEq.respectTransparency false in
/-- S-unit ideles are open in the units topology on the actual adele ring. -/
theorem isOpen_sUnitIdeles (S : Finset (FinitePlace K)) :
    IsOpen (sUnitIdeles K S : Set (Ideles K)) := by
  let U : Set (FiniteAdeles K) := {a | ∀ v : FinitePlace K, v ∉ S →
    a v ∈ v.adicCompletionIntegers K}
  have hU : IsOpen U := RestrictedProduct.isOpen_forall_imp_mem
    (fun v : FinitePlace K => Valued.isOpen_valuationSubring (v.adicCompletion K))
  have hval : Continuous (fun x : Ideles K => x.val.2) :=
    continuous_snd.comp Units.continuous_val
  have hinv : Continuous (fun x : Ideles K => x.inv.2) :=
    continuous_snd.comp Units.continuous_coe_inv
  convert (hU.preimage hval).inter (hU.preimage hinv) using 1
  ext x
  change (x ∈ sUnitIdeles K S) ↔
    (∀ v ∉ S, x.val.2 v ∈ v.adicCompletionIntegers K) ∧
    (∀ v ∉ S, x.inv.2 v ∈ v.adicCompletionIntegers K)
  rw [mem_sUnitIdeles_iff]
  constructor
  · intro hx
    constructor <;> intro v hv
    · change Valued.v (ideleCoordinate v x : v.adicCompletion K) ≤ 1
      exact ((ideleExponent_eq_one_iff v x).1 (hx v hv)).le
    · change Valued.v (((ideleCoordinate v x)⁻¹ : (v.adicCompletion K)ˣ) :
        v.adicCompletion K) ≤ 1
      rw [Units.val_inv_eq_inv_val, map_inv₀, (ideleExponent_eq_one_iff v x).1 (hx v hv),
        inv_one]
  · rintro ⟨hx, hi⟩ v hv
    apply (ideleExponent_eq_one_iff v x).2
    have ha := hx v hv
    have hb := hi v hv
    change Valued.v (ideleCoordinate v x : v.adicCompletion K) ≤ 1 at ha
    change Valued.v (((ideleCoordinate v x)⁻¹ : (v.adicCompletion K)ˣ) :
      v.adicCompletion K) ≤ 1 at hb
    rw [Units.val_inv_eq_inv_val, map_inv₀] at hb
    exact le_antisymm ha ((inv_le_one₀ (pos_iff_ne_zero.2
      ((Valuation.ne_zero_iff _).2 (Units.ne_zero _)))).1 hb)

end Langlands.Global.Arithmetic.SUnitIdeleTopology

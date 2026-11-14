import Langlands.FieldTheory.HenselianSeparableIntegerAddValuation
import Langlands.Geometry.Building.MaximalUnramifiedValuation
import Langlands.LocalField.AlgebraicExtensionValuation

/-! # Comparison of coordinate and geometric-character valuations -/

noncomputable section

universe u v w

namespace Langlands.FieldTheory

open IntermediateField

/-- An invariant additive valuation computes the field norm by the extension degree. -/
theorem addValuation_norm_of_invariant
    {K : Type u} [Field K] {Ω : Type v} [Field Ω] [Algebra K Ω] [IsGalois K Ω]
    (ν : AddValuation Ω (WithTop ℝ))
    (hν : ∀ (σ : Ω ≃ₐ[K] Ω) (x : Ω), ν (σ x) = ν x)
    {E : Type w} [Field E] [Algebra K E] [FiniteDimensional K E]
    [Algebra.IsSeparable K E] (f : E →ₐ[K] Ω) (x : E)
    (hs : ((minpoly K x).map (algebraMap K Ω)).Splits) :
    ν (algebraMap K Ω (Algebra.norm K x)) = Module.finrank K E • ν (f x) := by
  classical
  have hx := Algebra.IsSeparable.isIntegral K x
  have hval : ∀ y ∈ (minpoly K x).aroots Ω, ν y = ν (f x) := by
    intro y hy
    have hr : Polynomial.aeval y (minpoly K (f x)) = 0 := by
      rw [minpoly.algHom_eq f f.injective]
      exact (Polynomial.mem_aroots.mp hy).2
    obtain ⟨σ, hσ⟩ := minpoly.exists_algEquiv_of_root'
      (Algebra.IsAlgebraic.isAlgebraic (R := K) (f x)) hr
    rw [← hσ, hν]
  have hprod : ∀ s : Multiset Ω, (∀ y ∈ s, ν y = ν (f x)) →
      ν s.prod = s.card • ν (f x) := by
    intro s
    induction s using Multiset.induction_on with
    | empty => intro _; simp
    | @cons y s ih =>
        intro h
        rw [Multiset.prod_cons, AddValuation.map_mul, h y (by simp),
          ih (fun z hz => h z (by simp [hz])), Multiset.card_cons]
        simp [add_nsmul, add_comm]
  have hcard : ((minpoly K x).aroots Ω).card = Module.finrank K K⟮x⟯ := by
    rw [Polynomial.aroots_def, ← hs.natDegree_eq_card_roots,
      Polynomial.natDegree_map, adjoin.finrank hx]
  rw [Algebra.norm_eq_prod_roots Ω hs, AddValuation.map_pow, hprod _ hval, hcard,
    smul_smul, Nat.mul_comm, Module.finrank_mul_finrank]

end Langlands.FieldTheory

namespace Langlands.Geometry.Building.MaximalUnramified

open Langlands.LocalGalois.Separable

variable (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]

local instance : NontriviallyNormedField F := LocalGalois.localNormedField F
local instance : IsUltrametricDist F := LocalGalois.localNormedField_ultrametric F
local instance : CompleteSpace F := LocalGalois.localNormedField_complete F

/-- The geometric additive valuation has the exact normalized integer value on `F^ur`. -/
theorem geometricAddValuation_base {x : inertiaFixedField F} (hx : x ≠ 0) :
    LocalField.algebraicExtensionAddValuation F (SeparableClosure F)
        (algebraMap (inertiaFixedField F) (SeparableClosure F) x) =
      (((-WithZero.log (valuation F x) : ℤ) : ℝ) : WithTop ℝ) := by
  obtain ⟨a, ha⟩ := fixedFieldValuesFromBase F x
  have hb : fixedFieldValuation F x =
      fixedFieldValuation F (algebraMap F (inertiaFixedField F) a) := by
    rw [fixedFieldValuation_base]
    exact ha
  have hv := (valuation_isEquiv F).eq_iff.mpr hb
  have ha0 : a ≠ 0 := by
    intro h
    have : fixedFieldValuation F x = 0 := by simpa [h] using hb
    exact hx ((fixedFieldValuation F).zero_iff.mp this)
  have hg : LocalField.algebraicExtensionAddValuation F (SeparableClosure F)
        (algebraMap (inertiaFixedField F) (SeparableClosure F) x) =
      LocalField.algebraicExtensionAddValuation F (SeparableClosure F)
        (algebraMap F (SeparableClosure F) a) := by
    change LocalField.negativeLogValue _ (fixedFieldValuation F x) =
      LocalField.negativeLogValue _ _
    rw [hb]
    rfl
  rw [hg, hv, valuation_base]
  simpa only [Units.val_mk0, Plancherel.fieldOrderUnits_toAdd] using
    LocalField.algebraicExtensionAddValuation_base_unit F (SeparableClosure F)
      (Units.mk0 a ha0)

variable {F} {E : Type v} [Field E] [Algebra (inertiaFixedField F) E]

/-- The valuation on a coordinate field obtained from its geometric realization. -/
def geometricCoordinateAddValuation
    (f : E →ₐ[inertiaFixedField F] SeparableClosure F) :
    AddValuation E (WithTop ℝ) :=
  (LocalField.algebraicExtensionAddValuation F (SeparableClosure F)).comap f.toRingHom

variable (F) [FiniteDimensional (inertiaFixedField F) E]
  [Algebra.IsSeparable (inertiaFixedField F) E]

/-- Every geometric realization of a finite separable coordinate field preserves the
integer-normalized Henselian additive valuation, with no rescaling. -/
theorem geometricCoordinateAddValuation_eq
    (hH : HenselianLocalRing (valuation F).valuationSubring)
    (f : E →ₐ[inertiaFixedField F] SeparableClosure F) :
    geometricCoordinateAddValuation f =
      FieldTheory.henselianSeparableAddValuation (valuation F) hH E := by
  ext x
  by_cases hx : x = 0
  · simp [hx]
  let ν := LocalField.algebraicExtensionAddValuation F (SeparableClosure F)
  have hi : ∀ (σ : SeparableClosure F ≃ₐ[inertiaFixedField F] SeparableClosure F)
      (y : SeparableClosure F), ν (σ y) = ν y := by
    intro σ y
    exact LocalField.algebraicExtensionAddValuation_invariant F (SeparableClosure F)
      (σ.restrictScalars F) y
  have hs : ((minpoly (inertiaFixedField F) x).map
      (algebraMap (inertiaFixedField F) (SeparableClosure F))).Splits :=
    IsSepClosed.splits_codomain _
      (Algebra.IsSeparable.isSeparable (inertiaFixedField F) x)
  have hn := FieldTheory.addValuation_norm_of_invariant ν hi f x hs
  have hn' := FieldTheory.henselianSeparableAddValuation_norm (valuation F) hH E x
  have hn0 : Algebra.norm (inertiaFixedField F) x ≠ 0 :=
    Algebra.norm_ne_zero_iff.mpr hx
  rw [geometricAddValuation_base F hn0] at hn
  rw [FieldTheory.henselianSeparableAddValuation_base (valuation F) hH E hn0] at hn'
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp
    (ν.ne_top_iff.mpr ((map_ne_zero f).mpr hx))
  obtain ⟨b, hb⟩ := WithTop.ne_top_iff_exists.mp
    ((FieldTheory.henselianSeparableAddValuation (valuation F) hH E).ne_top_iff.mpr hx)
  have he := hn.symm.trans hn'
  rw [← ha, ← hb, ← WithTop.coe_nsmul, ← WithTop.coe_nsmul,
    WithTop.coe_inj, nsmul_eq_mul, nsmul_eq_mul] at he
  have hab : a = b := mul_left_cancel₀
    (Nat.cast_ne_zero.mpr (ne_of_gt
      (Module.finrank_pos (R := inertiaFixedField F) (M := E)))) he
  change ν (f x) = _
  rw [← ha, ← hb, hab]

/-- Pointwise form of the exact comparison for character and root coordinates. -/
theorem henselianSeparableAddValuation_eq_geometric
    (hH : HenselianLocalRing (valuation F).valuationSubring)
    (f : E →ₐ[inertiaFixedField F] SeparableClosure F) (x : E) :
    FieldTheory.henselianSeparableAddValuation (valuation F) hH E x =
      LocalField.algebraicExtensionAddValuation F (SeparableClosure F) (f x) :=
  (DFunLike.congr_fun (geometricCoordinateAddValuation_eq F hH f) x).symm

end Langlands.Geometry.Building.MaximalUnramified

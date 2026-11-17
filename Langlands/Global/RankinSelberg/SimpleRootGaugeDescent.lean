import Langlands.Global.RankinSelberg.TriangularSchwartzCompatibility
import Langlands.Global.RankinSelberg.CompactFactorDescent

/-! # Continuous simple-root functions on the full adelic group -/

noncomputable section
universe u
open NumberField
open scoped Classical RestrictedProduct
set_option autoImplicit false

namespace Langlands.Global.RankinSelbergGlobal.GaugeDescent

open Langlands.GeneralLinear

variable (F : Type u) [Field F] [NumberField F] {r : ℕ}

theorem continuous_gaugeSimpleRootRow :
    Continuous (gaugeSimpleRootRow F r) := by
  apply continuous_pi
  intro _
  apply continuous_pi
  intro i
  exact Units.continuous_val.comp
    ((continuous_apply i.castSucc).div' (continuous_apply i.succ))

theorem standardCompact_factor_surjective (n : ℕ) :
    Function.Surjective
      (fun p : upperTriangularSubgroup n (Adeles F) ×
        PrimitiveAdelicHeight.standardCompact F n => (p.1 : AdelicGL F n) * p.2) := by
  intro g
  obtain ⟨b, k, hg, hb, hk⟩ :=
    PrimitiveAdelicHeight.exists_isStandardIwasawaFactorization F n g
  exact ⟨(⟨b, hb⟩, ⟨k, hk⟩), hg.symm⟩

theorem triangularDiagonal_unipotent {A : Type*} [CommRing A] {n : ℕ}
    (v : Langlands.GeneralLinear.upperUnipotent n A) :
    triangularDiagonal n A ⟨v.val, v.property.1⟩ = 1 := by
  funext i
  apply Units.ext
  exact v.property.2 i

/-- A continuous simple-root function with the majorant's symmetries descends
to the full adelic general linear group and is invariant under the full left
unipotent subgroup and the right standard compact subgroup. -/
theorem exists_continuous_simpleRoot_extension
    (c : F) (Φ : RowVector F r → ℂ) (hΦ : Continuous Φ)
    (hsymm : HasSimpleRootCoordinateSymmetries F c Φ) :
    ∃ Γ : AdelicGL F (r + 1) → ℂ, Continuous Γ ∧
      (∀ (b : upperTriangularSubgroup (r + 1) (Adeles F))
        (k : PrimitiveAdelicHeight.standardCompact F (r + 1)),
        Γ ((b : AdelicGL F (r + 1)) * k) =
          Φ (gaugeSimpleRootRow F r (triangularDiagonal (r + 1) (Adeles F) b))) ∧
      (∀ (v : Langlands.GeneralLinear.upperUnipotent (r + 1) (Adeles F))
        (g : AdelicGL F (r + 1)), Γ ((v : AdelicGL F (r + 1)) * g) = Γ g) ∧
      (∀ (k : PrimitiveAdelicHeight.standardCompact F (r + 1))
        (g : AdelicGL F (r + 1)), Γ (g * (k : AdelicGL F (r + 1))) = Γ g) := by
  let : T2Space (InfiniteAdeles F) :=
    inferInstanceAs (T2Space ((v : NumberField.InfinitePlace F) → v.Completion))
  let : T2Space (FiniteAdeles F) :=
    inferInstanceAs (T2Space (Πʳ v : FinitePlace F,
      [FiniteCompletion F v, v.adicCompletionIntegers F]))
  let : T2Space (Adeles F) :=
    inferInstanceAs (T2Space (InfiniteAdeles F × FiniteAdeles F))
  let B := upperTriangularSubgroup (r + 1) (Adeles F)
  let K := PrimitiveAdelicHeight.standardCompact F (r + 1)
  let f : B → ℂ :=
    fun b => Φ (gaugeSimpleRootRow F r (triangularDiagonal (r + 1) (Adeles F) b))
  have hf : Continuous f :=
    hΦ.comp ((continuous_gaugeSimpleRootRow F).comp continuous_triangularDiagonal)
  have hcompat : ∀ b d : B, (b : AdelicGL F (r + 1))⁻¹ * d ∈ K → f b = f d := by
    intro b d hbd
    let z : B := b⁻¹ * d
    have hz : z.val ∈ K := hbd
    have hd : b * z = d := mul_inv_cancel_left b d
    dsimp only [f]
    rw [← hd, map_mul]
    exact (schwartzRoot_mul_triangularCompact F c Φ hsymm _ z hz).symm
  obtain ⟨Γ, hΓ, hformula⟩ := exists_continuous_compact_factor_descent B K
    isClosed_upperTriangular (PrimitiveAdelicHeight.isCompact_standardCompact F (r + 1))
    (standardCompact_factor_surjective F (r + 1)) f hf hcompat
  refine ⟨Γ, hΓ, hformula, ?_, ?_⟩
  · intro v g
    obtain ⟨⟨b, k⟩, hg⟩ := standardCompact_factor_surjective F (r + 1) g
    let v' : B := ⟨v.val, v.property.1⟩
    have he : (v : AdelicGL F (r + 1)) * g = ((v' * b : B) : AdelicGL F (r + 1)) * k := by
      rw [← hg]
      exact (mul_assoc _ _ _).symm
    rw [he, hformula, ← hg, hformula]
    change Φ (gaugeSimpleRootRow F r
      (triangularDiagonal (r + 1) (Adeles F) (v' * b))) = _
    rw [map_mul, triangularDiagonal_unipotent v, one_mul]
  · intro k g
    obtain ⟨⟨b, k'⟩, hg⟩ := standardCompact_factor_surjective F (r + 1) g
    have he : g * (k : AdelicGL F (r + 1)) =
        (b : AdelicGL F (r + 1)) * ((k' * k : K) : AdelicGL F (r + 1)) := by
      rw [← hg]
      exact mul_assoc _ _ _
    rw [he, hformula, ← hg, hformula]

end Langlands.Global.RankinSelbergGlobal.GaugeDescent

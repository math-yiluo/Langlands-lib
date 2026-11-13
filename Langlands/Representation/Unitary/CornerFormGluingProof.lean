import Langlands.LinearAlgebra.PositiveTraceForms
import Langlands.Representation.Unitary.CornerFormGluing
import Langlands.Representation.Unitary.CornerFormGluingStatement

/-!
# Proof of the corner-form gluing statement

The forms on the fixed spaces `ρ^K` are normalized at a nonzero vector `v₀ ∈ ρ^{K₀}`.
Uniqueness of corner-adjoint forms on finite-dimensional simple corner modules makes the
normalized forms compatible, and `isUnitarizable_of_compatibleCornerForms` glues them.
-/

noncomputable section

namespace Langlands

open MeasureTheory MeasureTheory.Measure
open scoped ComplexConjugate

universe uG uV uW uU

namespace CornerFormGluing

section Forms

variable {W : Type uW} [AddCommGroup W] [Module ℂ W]
variable {U : Type uU} [AddCommGroup U] [Module ℂ U]

/-- A positive real multiple of a positive definite Hermitian form. -/
abbrev scaleCore (b : InnerProductSpace.Core ℂ W) (r : ℝ) (hr : 0 < r) :
    InnerProductSpace.Core ℂ W where
  inner x y := (r : ℂ) * b.inner x y
  conj_inner_symm x y := by
    rw [map_mul, Complex.conj_ofReal, b.conj_inner_symm]
  re_inner_nonneg x := by
    change 0 ≤ ((r : ℂ) * b.inner x x).re
    rw [Complex.re_ofReal_mul]
    exact mul_nonneg hr.le (b.re_inner_nonneg x)
  add_left x y z := by
    change (r : ℂ) * b.inner (x + y) z = (r : ℂ) * b.inner x z + (r : ℂ) * b.inner y z
    rw [b.add_left, mul_add]
  smul_left x y c := by
    change (r : ℂ) * b.inner (c • x) y = conj c * ((r : ℂ) * b.inner x y)
    rw [b.smul_left]
    ring
  definite x hx := by
    have hr' : (r : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hr.ne'
    exact b.definite x ((mul_eq_zero.mp hx).resolve_left hr')

theorem scaleCore_inner (b : InnerProductSpace.Core ℂ W) (r : ℝ) (hr : 0 < r) (x y : W) :
    (scaleCore b r hr).inner x y = (r : ℂ) * b.inner x y := rfl

/-- Pull back a positive definite Hermitian form along an injective linear map. -/
abbrev comapCore (b : InnerProductSpace.Core ℂ W) (e : U →ₗ[ℂ] W)
    (he : Function.Injective e) : InnerProductSpace.Core ℂ U where
  inner x y := b.inner (e x) (e y)
  conj_inner_symm x y := b.conj_inner_symm (e x) (e y)
  re_inner_nonneg x := b.re_inner_nonneg (e x)
  add_left x y z := by
    change b.inner (e (x + y)) (e z) = b.inner (e x) (e z) + b.inner (e y) (e z)
    rw [map_add, b.add_left]
  smul_left x y c := by
    change b.inner (e (c • x)) (e y) = conj c * b.inner (e x) (e y)
    rw [map_smul, b.smul_left]
  definite x hx := he ((b.definite _ hx).trans (map_zero e).symm)

theorem comapCore_inner (b : InnerProductSpace.Core ℂ W) (e : U →ₗ[ℂ] W)
    (he : Function.Injective e) (x y : U) :
    (comapCore b e he).inner x y = b.inner (e x) (e y) := rfl

/-- The diagonal values of a Hermitian form are real. -/
theorem inner_self_eq_ofReal_re (b : InnerProductSpace.Core ℂ W) (x : W) :
    b.inner x x = ((b.inner x x).re : ℂ) := by
  have h := congrArg Complex.im (b.conj_inner_symm x x)
  rw [Complex.conj_im] at h
  exact Complex.ext rfl (by simp only [Complex.ofReal_im]; linarith)

/-- The diagonal values of a positive definite form at nonzero vectors are positive. -/
theorem re_inner_self_pos (b : InnerProductSpace.Core ℂ W) {x : W} (hx : x ≠ 0) :
    0 < (b.inner x x).re := by
  refine lt_of_le_of_ne (b.re_inner_nonneg x) fun hre => hx (b.definite x ?_)
  rw [inner_self_eq_ofReal_re b x, ← hre, Complex.ofReal_zero]

/-- The positive multiple of `b` that takes the value `1` at `(x, x)`. -/
abbrev normalizeCore (b : InnerProductSpace.Core ℂ W) {x : W} (hx : x ≠ 0) :
    InnerProductSpace.Core ℂ W :=
  scaleCore b (b.inner x x).re⁻¹ (inv_pos.mpr (re_inner_self_pos b hx))

theorem normalizeCore_inner (b : InnerProductSpace.Core ℂ W) {x : W} (hx : x ≠ 0)
    (y z : W) :
    (normalizeCore b hx).inner y z = (((b.inner x x).re⁻¹ : ℝ) : ℂ) * b.inner y z := rfl

theorem normalizeCore_inner_self (b : InnerProductSpace.Core ℂ W) {x : W} (hx : x ≠ 0) :
    (normalizeCore b hx).inner x x = 1 := by
  rw [normalizeCore_inner, inner_self_eq_ofReal_re b x, Complex.ofReal_re,
    Complex.ofReal_inv]
  exact inv_mul_cancel₀ (Complex.ofReal_ne_zero.mpr (re_inner_self_pos b hx).ne')

end Forms

section Corner

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsHaarMeasure]
  [μ.IsMulRightInvariant] [μ.IsInvInvariant]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)

omit [μ.IsMulRightInvariant] [μ.IsInvInvariant] in
/-- The involution commutes with the inclusion of a corner into a smaller-level corner. -/
theorem star_inclusion (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {L : OpenSubgroup G} (hL : IsCompact (L : Set G)) (hLK : L ≤ K)
    (f : Hecke.HeckeAlgebra.Corner μ K hK) :
    star (Hecke.HeckeAlgebra.Corner.inclusion μ K hK hL hLK f) =
      Hecke.HeckeAlgebra.Corner.inclusion μ K hK hL hLK (star f) :=
  Hecke.HeckeAlgebra.Corner.toHeckeAlgebra_injective μ L hL rfl

/-- A corner-adjoint form, viewed as a star-invariant form for the corner module. -/
def toStarInvariantForm (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (b : InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup))
    (hb : ∀ (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
      b.inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
        b.inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y)) :
    letI := Hecke.cornerModule μ ρ hρ K hK
    PositiveTraceForms.StarInvariantForm (Hecke.HeckeAlgebra.Corner μ K hK)
      (fixedVectors ρ K.toSubgroup) :=
  letI := Hecke.cornerModule μ ρ hρ K hK
  { toInnerProductCore := b
    adjoint := hb }

/-- Two corner-adjoint forms on a finite-dimensional simple fixed space are proportional. -/
theorem inner_mul_inner_eq (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    [FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)]
    (hsimple : letI := Hecke.cornerModule μ ρ hρ K hK
      IsSimpleModule (Hecke.HeckeAlgebra.Corner μ K hK) (fixedVectors ρ K.toSubgroup))
    (b b' : InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup))
    (hb : ∀ (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
      b.inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
        b.inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y))
    (hb' : ∀ (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
      b'.inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
        b'.inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y))
    (v₀ x w : fixedVectors ρ K.toSubgroup) :
    b.inner v₀ v₀ * b'.inner x w = b'.inner v₀ v₀ * b.inner x w := by
  let := Hecke.cornerModule μ ρ hρ K hK
  have := Hecke.cornerModule_isScalarTower μ ρ hρ K hK
  exact PositiveTraceForms.StarInvariantForm.inner_mul_inner_eq
    (toStarInvariantForm μ ρ hρ K hK b hb) (toStarInvariantForm μ ρ hρ K hK b' hb') v₀ x w

/-- The inclusion `ρ^K → ρ^L` of fixed spaces for `L ≤ K`. -/
def fixedInclusion {K L : OpenSubgroup G} (hLK : L ≤ K) :
    fixedVectors ρ K.toSubgroup →ₗ[ℂ] fixedVectors ρ L.toSubgroup :=
  Submodule.inclusion fun _ hv => mem_fixedVectors_of_le ρ hLK hv

omit [IsTopologicalGroup G] [MeasurableSpace G] [BorelSpace G] in
theorem fixedInclusion_injective {K L : OpenSubgroup G} (hLK : L ≤ K) :
    Function.Injective (fixedInclusion ρ hLK) :=
  Submodule.inclusion_injective _

omit [μ.IsMulRightInvariant] [μ.IsInvInvariant] in
/-- The restriction of an `L`-level corner-adjoint form to `ρ^K` is corner-adjoint for the
`K`-corner. -/
theorem comapCore_adjoint (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    {L : OpenSubgroup G} (hL : IsCompact (L : Set G)) (hLK : L ≤ K)
    (b : InnerProductSpace.Core ℂ (fixedVectors ρ L.toSubgroup))
    (hb : ∀ (f : Hecke.HeckeAlgebra.Corner μ L hL) (x y : fixedVectors ρ L.toSubgroup),
      b.inner (Hecke.cornerAction μ ρ hρ L hL f x) y =
        b.inner x (Hecke.cornerAction μ ρ hρ L hL (star f) y))
    (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup) :
    (comapCore b (fixedInclusion ρ hLK) (fixedInclusion_injective ρ hLK)).inner
        (Hecke.cornerAction μ ρ hρ K hK f x) y =
      (comapCore b (fixedInclusion ρ hLK) (fixedInclusion_injective ρ hLK)).inner x
        (Hecke.cornerAction μ ρ hρ K hK (star f) y) := by
  have hι : ∀ (f : Hecke.HeckeAlgebra.Corner μ K hK) (u : fixedVectors ρ K.toSubgroup),
      fixedInclusion ρ hLK (Hecke.cornerAction μ ρ hρ K hK f u) =
        Hecke.cornerAction μ ρ hρ L hL
          (Hecke.HeckeAlgebra.Corner.inclusion μ K hK hL hLK f) (fixedInclusion ρ hLK u) :=
    fun f u => Subtype.ext (Hecke.cornerAction_refinement μ ρ hρ K hK hL hLK f u).symm
  rw [comapCore_inner, comapCore_inner, hι, hb, star_inclusion, hι]

end Corner

/-- **Corner-form gluing.** Normalized corner-adjoint forms on the fixed spaces below `K₀`
glue to an invariant positive definite Hermitian form. -/
theorem cornerFormGluing : CornerFormGluingStatement.{uG, uV} := by
  intro G _ _ _ _ _ μ _ _ _ V _ _ ρ hρ K₀ hK₀ ⟨v₀, hv₀, hv₀ne⟩ hfin hsimple hform
  choose b hb using hform
  -- The vector `v₀` as a nonzero `K`-fixed vector for every `K ≤ K₀`.
  have hmem : ∀ {K : OpenSubgroup G}, K ≤ K₀ → v₀ ∈ fixedVectors ρ K.toSubgroup :=
    fun hKK₀ => mem_fixedVectors_of_le ρ hKK₀ hv₀
  have hne : ∀ {K : OpenSubgroup G} (hKK₀ : K ≤ K₀),
      (⟨v₀, hmem hKK₀⟩ : fixedVectors ρ K.toSubgroup) ≠ 0 :=
    fun _ h => hv₀ne (congrArg Subtype.val h)
  -- Normalize every form at `v₀`.
  let B : ∀ K : OpenSubgroup G, IsCompact (K : Set G) → K ≤ K₀ →
      InnerProductSpace.Core ℂ (fixedVectors ρ K.toSubgroup) :=
    fun K hK hKK₀ => normalizeCore (b K hK hKK₀) (hne hKK₀)
  have hB : ∀ (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (hKK₀ : K ≤ K₀)
      (f : Hecke.HeckeAlgebra.Corner μ K hK) (x y : fixedVectors ρ K.toSubgroup),
      (B K hK hKK₀).inner (Hecke.cornerAction μ ρ hρ K hK f x) y =
        (B K hK hKK₀).inner x (Hecke.cornerAction μ ρ hρ K hK (star f) y) := by
    intro K hK hKK₀ f x y
    simp only [B, normalizeCore_inner]
    rw [hb]
  apply isUnitarizable_of_compatibleCornerForms hρ hK₀ μ (b := B) hB
  intro K hK hKK₀ L hL hLK₀ hLK v w
  have := hfin K hK hKK₀
  have key := inner_mul_inner_eq μ ρ hρ K hK (hsimple K hK hKK₀) (B K hK hKK₀)
    (comapCore (B L hL hLK₀) (fixedInclusion ρ hLK) (fixedInclusion_injective ρ hLK))
    (hB K hK hKK₀) (comapCore_adjoint μ ρ hρ K hK hL hLK _ (hB L hL hLK₀))
    ⟨v₀, hmem hKK₀⟩ v w
  have h1 : (B K hK hKK₀).inner ⟨v₀, hmem hKK₀⟩ ⟨v₀, hmem hKK₀⟩ = 1 :=
    normalizeCore_inner_self _ _
  have h2 : (comapCore (B L hL hLK₀) (fixedInclusion ρ hLK)
      (fixedInclusion_injective ρ hLK)).inner ⟨v₀, hmem hKK₀⟩ ⟨v₀, hmem hKK₀⟩ = 1 :=
    normalizeCore_inner_self _ (hne hLK₀)
  rw [h1, h2, one_mul, one_mul] at key
  exact key

end CornerFormGluing

end Langlands

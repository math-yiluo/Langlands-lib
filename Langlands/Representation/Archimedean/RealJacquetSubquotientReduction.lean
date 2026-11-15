import Langlands.Representation.Archimedean.RealJacquetFiniteDimensional

/-!
# Harish-Chandra's subquotient theorem and the nonvanishing of the real Jacquet module

Wallach (1979, 4.13) remarks that the nonvanishing half of Casselman's algebraic theorem,
`V ≠ 𝔫V` for an admissible `(𝔤, K)`-module (for `GL_n(ℝ)` and irreducible `V`, the Library's
`RealJacquetNonvanishingStatement`), can be proved from Harish-Chandra's subquotient theorem
and Casselman's technique of asymptotics of matrix coefficients. This file states the two pieces:

* `RealPrincipalSeriesSubquotientStatement`: every irreducible admissible
  `(𝔤𝔩_n(ℝ), O(n))`-module is a quotient of a `(𝔤, K)`-stable space of `O(n)`-finite
  functions in one of the Library's principal series `realStandardModule n (cs.map
  RealBlock.character)`, by a surjective intertwiner (`IsRealSubquotientMap`);
* `RealJacquetNonvanishingSubquotientReductionStatement`: the subquotient theorem implies
  `RealJacquetNonvanishingStatement`.

It also proves that Casselman's subrepresentation theorem
`RealPrincipalSeriesSubrepresentationStatement` implies the subquotient statement
(`realPrincipalSeriesSubquotient_of_subrepresentation`), so the subquotient statement is no
stronger than the subrepresentation theorem.
-/

noncomputable section

open scoped TensorProduct Matrix

set_option autoImplicit false

namespace Langlands.Archimedean

attribute [local instance 100] LieRing.ofAssociativeRing

open Langlands.LocalFactor.Archimedean
open scoped Matrix.Norms.Operator

-- As in `GKModule`: the charts on units need reduction through the normed-ring instances of
-- matrices.
set_option backward.isDefEq.respectTransparency false

universe uV

variable (n : ℕ) {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- `T` is a `(𝔤, K)`-intertwiner from the space `W` of functions on `GL_n(ℝ)` into
`(ρ, π)`: for every `k ∈ O(n)` and every `w ∈ W`, the right translate of `w` by `k` is again in
`W` and `T` carries it to `ρ(k)(T w)`; for every real `X` and every `w ∈ W`, the right
derivative of `w` along `X` is again in `W` and `T` carries it to `π(1 ⊗ X)(T w)`. This is
`IsRealStandardIntertwiner` with the `O(n)`-finite functions of a standard module replaced by an
arbitrary space `W` of functions. -/
def IsRealSubquotientMap (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V)
    (W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ)) (T : W →ₗ[ℂ] V) : Prop :=
  (∀ (k : unitaryCompact ℝ n) (w : W),
    ∃ hw : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ W,
      T ⟨_, hw⟩ =
        ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ (T w)) ∧
  ∀ (X : Matrix (Fin n) (Fin n) ℝ) (w : W),
    ∃ hw : rightDerivative (matrixModel ℝ n) X (w : Langlands.GeneralLinear n ℝ → ℂ) ∈ W,
      T ⟨_, hw⟩ = π (1 ⊗ₜ X) (T w)

/-- Harish-Chandra's subquotient theorem for `GL_n(ℝ)` and the upper triangular Borel subgroup,
for `(𝔤, K)`-modules and the Library's principal series: every irreducible admissible
`(𝔤𝔩_n(ℝ), O(n))`-module `(ρ, π)` is a quotient `W/ker T` of a space `W` of `O(n)`-finite
functions in the principal series `realStandardModule n (cs.map RealBlock.character)` of some
list `cs` of `n` characters of `GL_1(ℝ)`, by a surjective intertwiner `T : W → V`. -/
def RealPrincipalSeriesSubquotientStatement : Prop :=
  ∀ (n : ℕ) (V : Type uV) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V)
    (π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V),
    IsRealGKModule n ρ π → IsIrreducibleGKModule ρ π → IsAdmissibleGKModule ρ →
      ∃ cs : List RealCharacterData, cs.length = n ∧
        ∃ W : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ),
          W ≤ kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
            (unitaryCompact ℝ n) ∧
          ∃ T : W →ₗ[ℂ] V, Function.Surjective T ∧ IsRealSubquotientMap n ρ π W T

/-- The subquotient theorem implies the nonvanishing of the real Jacquet module (Wallach 1979,
4.13: by the subquotient theorem and Casselman's technique of matrix coefficients). -/
def RealJacquetNonvanishingSubquotientReductionStatement : Prop :=
  RealPrincipalSeriesSubquotientStatement.{uV} → RealJacquetNonvanishingStatement.{uV}

/-! ## The subrepresentation theorem implies the subquotient theorem -/

section Consistency

variable {n}

/-- The kernel of a `(𝔤, K)`-equivariant map into functions is `(𝔤, K)`-stable, so for an
irreducible module a nonzero such map is injective. -/
theorem injective_of_isRealStandardEmbedding
    {ρ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) V}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ V} {ds : List RealBlock}
    {B : V →ₗ[ℂ] kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)}
    (hirr : IsIrreducibleGKModule ρ π) (hB0 : B ≠ 0)
    (hB : IsRealStandardEmbedding n ρ π ds B) : Function.Injective B := by
  have hρ : ∀ (k : Matrix.unitaryGroup (Fin n) ℝ), ∀ v ∈ LinearMap.ker B,
      ρ k v ∈ LinearMap.ker B := by
    intro k v hv
    rw [LinearMap.mem_ker] at hv ⊢
    let k' : unitaryCompact ℝ n := ⟨Unitary.toUnits k, k.2⟩
    have hk : (⟨((k' : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k'.2⟩ :
        Matrix.unitaryGroup (Fin n) ℝ) = k := Subtype.ext rfl
    apply Subtype.ext
    have h := hB.1 k' v
    rw [hk, hv] at h
    rw [h]
    funext g
    simp [Whittaker.rightTranslation]
  have hπ : ∀ (X : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ), ∀ v ∈ LinearMap.ker B,
      π X v ∈ LinearMap.ker B := by
    intro X v hv
    induction X using TensorProduct.inductionOn with
    | tmul c Y =>
      rw [LinearMap.mem_ker] at hv ⊢
      have hcY : (c ⊗ₜ[ℝ] Y : ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) = c • (1 ⊗ₜ Y) := by
        rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      rw [hcY, map_smul, LinearMap.smul_apply, map_smul]
      have h := hB.2 Y v
      rw [hv] at h
      have h0 : B (π (1 ⊗ₜ Y) v) = 0 := by
        apply Subtype.ext
        rw [h]
        funext g
        simp only [rightDerivative, ZeroMemClass.coe_zero, Pi.zero_apply, mfderiv_const]
        rfl
      rw [h0, smul_zero]
    | add X Y hX hY =>
      rw [map_add, LinearMap.add_apply]
      exact Submodule.add_mem _ hX hY
  rcases hirr.2 (LinearMap.ker B) hρ hπ with h | h
  · exact LinearMap.ker_eq_bot.1 h
  · exact absurd (LinearMap.ker_eq_top.1 h) hB0

/-- Casselman's subrepresentation theorem implies the subquotient theorem: the image of the
embedding is a `(𝔤, K)`-stable space of `O(n)`-finite functions, and the inverse of the
embedding is a surjective intertwiner from it onto the module. -/
theorem realPrincipalSeriesSubquotient_of_subrepresentation :
    RealPrincipalSeriesSubrepresentationStatement.{uV} →
      RealPrincipalSeriesSubquotientStatement.{uV} := by
  intro hsub n V _ _ ρ π hgk hirr hadm
  obtain ⟨cs, hlen, B, hB0, hB⟩ := hsub n V ρ π hgk hirr hadm
  have hinj : Function.Injective B := injective_of_isRealStandardEmbedding hirr hB0 hB
  let f : V →ₗ[ℂ] (Langlands.GeneralLinear n ℝ → ℂ) :=
    (kFiniteFunctions (realStandardModule n (cs.map RealBlock.character))
      (unitaryCompact ℝ n)).subtype ∘ₗ B
  have hf : Function.Injective f := Subtype.val_injective.comp hinj
  let e : V ≃ₗ[ℂ] LinearMap.range f := LinearEquiv.ofInjective f hf
  refine ⟨cs, hlen, LinearMap.range f, ?_, e.symm.toLinearMap, e.symm.surjective, ?_, ?_⟩
  · rintro _ ⟨v, rfl⟩
    exact (B v).2
  · intro k w
    obtain ⟨_, v, rfl⟩ := w
    have hv : Whittaker.rightTranslation ℂ (Langlands.GeneralLinear n ℝ)
        (k : Langlands.GeneralLinear n ℝ) (f v) =
          f (ρ ⟨((k : Langlands.GeneralLinear n ℝ) : Matrix (Fin n) (Fin n) ℝ), k.2⟩ v) :=
      (hB.1 k v).symm
    refine ⟨hv ▸ ⟨_, rfl⟩, ?_⟩
    apply e.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [hv]
    congr 1
    exact (e.symm_apply_apply v).symm ▸ rfl
  · intro X w
    obtain ⟨_, v, rfl⟩ := w
    have hv : rightDerivative (matrixModel ℝ n) X (f v) = f (π (1 ⊗ₜ X) v) :=
      (hB.2 X v).symm
    refine ⟨hv ▸ ⟨_, rfl⟩, ?_⟩
    apply e.injective
    simp only [LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply]
    apply Subtype.ext
    simp only [hv]
    congr 1
    exact (e.symm_apply_apply v).symm ▸ rfl

end Consistency

end Langlands.Archimedean

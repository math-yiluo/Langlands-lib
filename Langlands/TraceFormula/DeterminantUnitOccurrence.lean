import Langlands.Representation.CyclicRestriction
import Langlands.Global.CompletionPadic
import Langlands.Representation.Smooth.Schur.Proof
import Langlands.Group.GL.Basic

/-! # Occurrence up to a twist from an intertwiner on a cyclic kernel -/

noncomputable section

namespace Langlands.TraceFormula

open Representation CyclicRestriction

universe uG uV uW

variable {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module ℂ V]
  {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- Let `δ : G → ℤ` be surjective. If one positive-degree element acts by scalars in both
representations, a nonzero map intertwining the kernel of `δ` yields a nonzero `G`-intertwiner
from a twist of the source by a character of `δ`. -/
theorem exists_twist_intertwiner_of_cyclicKernel (δ : G →* Multiplicative ℤ)
    (hδ : Function.Surjective δ) (d : ℕ) (hd : 0 < d) (z : G)
    (hz : δ z = Multiplicative.ofAdd (d : ℤ))
    (ρ : Representation ℂ G V) (τ : Representation ℂ G W)
    (a b : ℂˣ) (ha : ∀ x, ρ z x = (a : ℂ) • x) (hb : ∀ y, τ z y = (b : ℂ) • y)
    (j : V →ₗ[ℂ] W) (hj : j ≠ 0)
    (heq : ∀ g, δ g = 1 → ∀ x, j (ρ g x) = τ g (j x)) :
    ∃ χ : Multiplicative ℤ →* ℂˣ, ∃ T : V →ₗ[ℂ] W, T ≠ 0 ∧
      ∀ g x, T (Langlands.twist (χ.comp δ) ρ g x) = τ g (T x) := by
  classical
  let R := linHom ρ τ
  have hfix (g : G) (hg : δ g = 1) : R g j = j := by
    apply LinearMap.ext
    intro x
    change τ g (j (ρ g⁻¹ x)) = j x
    rw [← heq g hg, ρ.self_inv_apply]
  obtain ⟨t, ht⟩ := hδ (Multiplicative.ofAdd (1 : ℤ))
  have htdeg (i : ℕ) : δ (t ^ i) = Multiplicative.ofAdd (i : ℤ) := by
    rw [map_pow, ht]
    change Multiplicative.ofAdd ((i : ℤ) * 1) = _
    simp
  have htz : δ (z⁻¹ * t ^ d) = 1 := by
    rw [map_mul, map_inv, htdeg, hz, inv_mul_cancel]
  have hzact : R z j = ((b : ℂ) / (a : ℂ)) • j := by
    apply LinearMap.ext
    intro x
    change τ z (j (ρ z⁻¹ x)) = ((b : ℂ) / (a : ℂ)) • j x
    let y := ρ z⁻¹ x
    change τ z (j y) = _
    have hy : j x = (a : ℂ) • j y := by
      calc
        j x = j (ρ z y) := congrArg j (ρ.self_inv_apply z x).symm
        _ = _ := by rw [ha, map_smul]
    rw [hb, hy, smul_smul, div_mul_cancel₀ _ (Units.ne_zero a)]
  have hperiod : R (t ^ d) j = ((b : ℂ) / (a : ℂ)) • j := by
    calc
      R (t ^ d) j = R (z * (z⁻¹ * t ^ d)) j := by rw [mul_inv_cancel_left]
      _ = R z j := by rw [map_mul, Module.End.mul_apply, hfix _ htz]
      _ = _ := hzact
  let f : Fin d → (V →ₗ[ℂ] W) := fun i => R (t ^ (i : ℕ)) j
  let S := Submodule.span ℂ (Set.range f)
  have hjS : j ∈ S := by
    have h : f ⟨0, hd⟩ = j := by simp [f]
    exact h ▸ Submodule.subset_span (Set.mem_range_self _)
  have hstable : ∀ x ∈ S, R t x ∈ S := by
    change S ≤ S.comap (R t)
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    change R t (R (t ^ (i : ℕ)) j) ∈ S
    rw [← Module.End.mul_apply, ← map_mul, ← pow_succ']
    by_cases hi : (i : ℕ) + 1 < d
    · exact Submodule.subset_span (Set.mem_range_self (f := f) ⟨(i : ℕ) + 1, hi⟩)
    · have he : (i : ℕ) + 1 = d := by omega
      rw [he, hperiod]
      exact S.smul_mem _ hjS
  have hSfix : S ≤ Representation.invariants (R.comp δ.ker.subtype) := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    intro g
    let m := t ^ (i : ℕ)
    change R (g : G) (R m j) = R m j
    have hm : δ (m⁻¹ * (g : G) * m) = 1 := by
      rw [map_mul, map_mul, map_inv, MonoidHom.mem_ker.mp g.property, mul_one,
        inv_mul_cancel]
    rw [← Module.End.mul_apply, ← map_mul]
    have hgm : (g : G) * m = m * (m⁻¹ * (g : G) * m) := by group
    rw [hgm, map_mul, Module.End.mul_apply, hfix _ hm]
  let : FiniteDimensional ℂ S := FiniteDimensional.span_of_finite ℂ (Set.finite_range f)
  let : Nontrivial S := ⟨⟨⟨j, hjS⟩, 0, fun h => hj (congrArg Subtype.val h)⟩⟩
  let A : Module.End ℂ S := (R t).restrict hstable
  obtain ⟨c, hc⟩ := A.exists_eigenvalue
  obtain ⟨v, hv⟩ := hc.exists_hasEigenvector
  let T : V →ₗ[ℂ] W := v
  have hT : T ≠ 0 := fun h => hv.2 (Subtype.ext h)
  have hev : R t T = c • T := congrArg Subtype.val hv.apply_eq_smul
  have hc0 : c ≠ 0 := by
    intro h
    have hzero := congrArg (R t⁻¹) hev
    rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      h, zero_smul, map_zero] at hzero
    exact hT hzero
  let H := eigenlineStabilizer R T
  have hN : δ.ker ≤ H := fun g hg => ⟨1, by simpa using hSfix v.property ⟨g, hg⟩⟩
  have htH : t ∈ H := ⟨Units.mk0 c hc0, hev⟩
  have hgen (g : G) : g * (t ^ (δ g).toAdd)⁻¹ ∈ δ.ker := by
    change δ (g * (t ^ (δ g).toAdd)⁻¹) = 1
    rw [map_mul, map_inv, map_zpow, ht]
    have he : Multiplicative.ofAdd (1 : ℤ) ^ (δ g).toAdd = δ g := by
      change Multiplicative.ofAdd ((δ g).toAdd * 1) = _
      simp
    rw [he, mul_inv_cancel]
  have hH : H = ⊤ := eq_top_of_le_of_generator hN htH (fun g => ⟨_, hgen g⟩)
  have hline (g : G) : g ∈ eigenlineStabilizer R T := by
    change g ∈ H
    rw [hH]
    exact Subgroup.mem_top g
  let ψ := eigenlineCharacter hT hline
  have hψ (g : G) : R g T = (ψ g : ℂ) • T := eigenlineCharacter_apply_smul hT hline g
  have hψN : δ.ker ≤ ψ.ker := by
    intro g hg
    apply eigenline_scalar_unique T hT
    rw [← hψ g]
    simpa using hSfix v.property ⟨g, hg⟩
  let E := QuotientGroup.liftEquiv δ.ker hδ rfl
  let χ := (QuotientGroup.lift δ.ker ψ hψN).comp E.symm.toMonoidHom
  have hχ (g : G) : χ (δ g) = ψ g := by
    have hg : E (QuotientGroup.mk g) = δ g := rfl
    rw [← hg]
    change QuotientGroup.lift δ.ker ψ hψN (E.symm (E (QuotientGroup.mk g))) = ψ g
    rw [E.symm_apply_apply, QuotientGroup.lift_mk]
  refine ⟨χ, T, hT, fun g x => ?_⟩
  have hx := LinearMap.congr_fun (hψ g) (ρ g x)
  change τ g (T (ρ g⁻¹ (ρ g x))) = (ψ g : ℂ) • T (ρ g x) at hx
  rw [ρ.inv_self_apply] at hx
  change T ((χ (δ g) : ℂ) • ρ g x) = τ g (T x)
  rw [map_smul, hχ, hx]

section FinitePlace

open NumberField
open scoped NumberField

variable (K : Type uG) [Field K] [NumberField K] (v : IsDedekindDomain.HeightOneSpectrum (𝓞 K))

/-- The integer coordinate of the completion valuation on the unit group. -/
private def localUnitDegree : (v.adicCompletion K)ˣ →* Multiplicative ℤ :=
  WithZero.unitsWithZeroEquiv.toMonoidHom.comp
    (Units.map (Valued.v : Valuation (v.adicCompletion K) (WithZero (Multiplicative ℤ))).toMonoidHom)

private theorem coe_localUnitDegree (a : (v.adicCompletion K)ˣ) :
    ((localUnitDegree K v a : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) =
      Valued.v (a : v.adicCompletion K) :=
  WithZero.coe_unitsWithZeroEquiv_eq_units_val _

private theorem localUnitDegree_surjective : Function.Surjective (localUnitDegree K v) := by
  intro m
  obtain ⟨a, ha⟩ := v.valuedAdicCompletion_surjective K
    (m : WithZero (Multiplicative ℤ))
  have ha0 : a ≠ 0 := by
    rintro rfl
    exact WithZero.coe_ne_zero (by simpa only [map_zero] using ha.symm)
  refine ⟨Units.mk0 a ha0, WithZero.coe_injective ?_⟩
  rw [coe_localUnitDegree]
  exact ha

/-- An occurrence on the determinant-unit subgroup gives an occurrence up to an unramified
 determinant twist when scalar matrices act by scalars on the target. -/
theorem exists_unramifiedDeterminantTwist_intertwiner (n : ℕ) (hn : 0 < n)
    (ρ : Representation ℂ (GeneralLinear n (v.adicCompletion K)) V)
    (hρ : IsAdmissible ρ) (hρirr : ρ.IsIrreducible)
    (τ : Representation ℂ (GeneralLinear n (v.adicCompletion K)) W)
    (hτ : ∀ a : (v.adicCompletion K)ˣ, ∃ b : ℂˣ,
      ∀ x, τ (GeneralLinear.scalar a) x = (b : ℂ) • x)
    (j : V →ₗ[ℂ] W) (hj : j ≠ 0)
    (heq : ∀ g, Valued.v (GeneralLinear.determinant g : v.adicCompletion K) = 1 →
      ∀ x, j (ρ g x) = τ g (j x)) :
    ∃ χ : (v.adicCompletion K)ˣ →* ℂˣ,
      (∀ a : (v.adicCompletion K)ˣ, Valued.v (a : v.adicCompletion K) = 1 → χ a = 1) ∧
      ∃ T : V →ₗ[ℂ] W, T ≠ 0 ∧
        ∀ g x, T (Langlands.twist (χ.comp GeneralLinear.determinant) ρ g x) = τ g (T x) := by
  let D := localUnitDegree K v
  let δ : GeneralLinear n (v.adicCompletion K) →* Multiplicative ℤ := D.comp GeneralLinear.determinant
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  have hδ : Function.Surjective δ := (localUnitDegree_surjective K v).comp
    (Matrix.GeneralLinearGroup.det_surjective (n := Fin n))
  obtain ⟨a, ha⟩ := localUnitDegree_surjective K v (Multiplicative.ofAdd (1 : ℤ))
  let z : Subgroup.center (GeneralLinear n (v.adicCompletion K)) := GeneralLinear.scalarToCenter a
  have hz : δ (z : GeneralLinear n (v.adicCompletion K)) = Multiplicative.ofAdd (n : ℤ) := by
    change D (GeneralLinear.determinant (GeneralLinear.scalar a)) = _
    rw [Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin, map_pow]
    change (localUnitDegree K v a) ^ n = _
    rw [ha]
    change Multiplicative.ofAdd ((n : ℤ) * 1) = _
    simp
  obtain ⟨ω, hω, _⟩ := admissibleSchur_centralCharacter ρ hρ hρirr
  obtain ⟨b, hb⟩ := hτ a
  have hjδ (g : GeneralLinear n (v.adicCompletion K)) (hg : δ g = 1) :
      ∀ x, j (ρ g x) = τ g (j x) := by
    apply heq
    rw [← coe_localUnitDegree K v]
    change ((δ g : Multiplicative ℤ) : WithZero (Multiplicative ℤ)) = 1
    rw [hg]
    rfl
  obtain ⟨η, T, hT, hTeq⟩ := exists_twist_intertwiner_of_cyclicKernel δ hδ n hn z hz
    ρ τ (ω z) b (hω.2 z) hb j hj hjδ
  refine ⟨η.comp D, ?_, T, hT, hTeq⟩
  intro a' ha'
  have hDa : D a' = 1 := by
    apply WithZero.coe_injective
    exact (coe_localUnitDegree K v a').trans ha'
  change η (D a') = 1
  rw [hDa, map_one]

end FinitePlace

end Langlands.TraceFormula

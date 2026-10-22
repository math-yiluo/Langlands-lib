import Langlands.Representation.Smooth.Contragredient.CompactDualityStatement
import Langlands.Representation.Compact.Definitions

/-! # Proof of compact-open fixed-vector duality

All finite-mean helpers are kept with their consuming restriction theorem.
-/

noncomputable section

namespace Langlands

open scoped BigOperators
open Compact

universe uG uV uW

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W]

private theorem map_mean_of_constant (ρ : Representation ℂ G V) (v : V)
    [Finite (orbit ρ v)] (f : V →ₗ[ℂ] W) (w : W)
    (hf : ∀ g, f (ρ g v) = w) : f (orbitMean ρ v) = w := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  have hx (x : orbit ρ v) : f x.val = w := by
    obtain ⟨g, hg⟩ := x.property
    exact (congrArg f hg).symm.trans (hf g)
  have hc : (Fintype.card (orbit ρ v) : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  rw [orbitMean_eq_finiteMean]
  change f ((Fintype.card (orbit ρ v) : ℂ)⁻¹ • ∑ x : orbit ρ v, x.val) = w
  rw [map_smul, map_sum]
  simp only [hx, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem mean_fixed (ρ : Representation ℂ G V) (v : V)
    [Finite (orbit ρ v)] (g : G) : ρ g (orbitMean ρ v) = orbitMean ρ v := by
  classical
  let := Fintype.ofFinite (orbit ρ v)
  rw [orbitMean_eq_finiteMean]
  change ρ g ((Fintype.card (orbit ρ v) : ℂ)⁻¹ • ∑ x : orbit ρ v, x.val) = _
  rw [map_smul, map_sum]
  congr 1
  change (∑ x : orbit ρ v, (g • x).val) = ∑ x : orbit ρ v, x.val
  exact Equiv.sum_comp (MulAction.toPerm g) (fun x : orbit ρ v => x.val)

private theorem mean_action (ρ : Representation ℂ G V) (g : G) (v : V) :
    orbitMean ρ (ρ g v) = orbitMean ρ v := by
  have ho : orbit ρ (ρ g v) = orbit ρ v := by
    ext x
    constructor
    · rintro ⟨h, rfl⟩
      exact ⟨h * g, by simp⟩
    · rintro ⟨h, rfl⟩
      refine ⟨h * g⁻¹, ?_⟩
      simp [map_mul, Module.End.mul_apply]
  unfold orbitMean
  rw [ho]

variable [TopologicalSpace G] [IsTopologicalGroup G]

/-- Restriction of compact-open fixed smooth functionals is bijective. -/
theorem smoothDualFixedRestriction_bijective (ρ : Representation ℂ G V)
    (hρ : IsSmooth ρ) (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Function.Bijective (smoothDualFixedRestriction ρ K.toSubgroup) := by
  let τ := ρ.comp K.toSubgroup.subtype
  let (v : V) : Finite (orbit τ v) := finite_orbit_of_smooth ρ hρ K hK v
  let P : V →ₗ[ℂ] fixedVectors ρ K.toSubgroup :=
    (averageMap ρ hρ K hK).codRestrict (fixedVectors ρ K.toSubgroup)
      (fun v k => mean_fixed τ v k)
  have hP (v : V) : (P v).val = orbitMean τ v := rfl
  have hPid (v : fixedVectors ρ K.toSubgroup) : P v.val = v := by
    apply Subtype.ext
    exact map_mean_of_constant τ v.val (LinearMap.id : V →ₗ[ℂ] V) v.val v.property
  have hPk (k : K) (v : V) : P (ρ k.val v) = P v := by
    apply Subtype.ext
    exact mean_action τ k v
  have hfunctional (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
      (v : V) : ℓ.val.val (P v).val = ℓ.val.val v := by
    rw [hP]
    apply map_mean_of_constant
    intro k
    have hk := congrArg (fun f : SmoothDual ρ => f.val v) (ℓ.property k⁻¹)
    change ℓ.val.val (ρ ((k⁻¹ : K).val)⁻¹ v) = ℓ.val.val v at hk
    simpa only [τ, MonoidHom.comp_apply, Subgroup.subtype_apply,
      InvMemClass.coe_inv, inv_inv] using hk
  constructor
  · intro ℓ m heq
    apply Subtype.ext
    apply Subtype.ext
    apply LinearMap.ext
    intro v
    calc
      ℓ.val.val v = ℓ.val.val (P v).val := (hfunctional ℓ v).symm
      _ = m.val.val (P v).val := congrArg (fun f => f (P v)) heq
      _ = m.val.val v := hfunctional m v
  · intro φ
    let f : Module.Dual ℂ V := φ.comp P
    have hfix (k : K) : ρ.dual k.val f = f := by
      ext v
      change φ (P (ρ k.val⁻¹ v)) = φ (P v)
      exact congrArg φ (hPk k⁻¹ v)
    let ℓ : SmoothDual ρ := ⟨f, K, hfix⟩
    have hℓ (k : K) : smoothContragredient ρ k.val ℓ = ℓ :=
      Subtype.ext (hfix k)
    refine ⟨⟨ℓ, hℓ⟩, ?_⟩
    ext v
    change φ (P v.val) = φ v
    exact congrArg φ (hPid v)

theorem smoothDualCompactFixedDuality
    {G : Type uG} [Group G] [TopologicalSpace G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V] :
    SmoothDualCompactFixedDualityStatement (G := G) (V := V) := by
  intro _ ρ hρ K hK
  exact smoothDualFixedRestriction_bijective ρ hρ K hK

end Langlands

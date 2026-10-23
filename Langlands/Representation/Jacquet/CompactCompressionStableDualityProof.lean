import Langlands.Representation.Jacquet.CompactCompressionStableDualityStatement
import Langlands.Representation.Jacquet.CompressionStabilizationProof
import Langlands.Representation.Smooth.Contragredient.CompactDualityProof
import Mathlib.LinearAlgebra.Dual.Lemmas

/-!
# Evaluation duality on stable images of compact compression

Compression by the inverse element on the smooth dual is adjoint to the
original compression. The finite-dimensional Fitting decomposition makes the
restriction of the actual evaluation pairing to their stable images perfect.
-/

noncomputable section

namespace Langlands.Jacquet

universe uG uV uA uB

open scoped BigOperators

private theorem average_eval_constant
    {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    {V : Type uV} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G))
    (f : Module.Dual ℂ V) (v : V) (hf : ∀ k : K, f (ρ k.val v) = f v) :
    f (Compact.averageMap ρ hρ K hK v) = f v := by
  classical
  let τ := ρ.comp K.toSubgroup.subtype
  let := Compact.finite_orbit_of_smooth ρ hρ K hK v
  let := Fintype.ofFinite (Compact.orbit τ v)
  have hx (x : Compact.orbit τ v) : f x.val = f v := by
    obtain ⟨k, hk⟩ := x.property
    exact (congrArg f hk).symm.trans (hf k)
  have hc : (Fintype.card (Compact.orbit τ v) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  change f (Compact.orbitMean τ v) = f v
  rw [Compact.orbitMean_eq_finiteMean]
  simp only [Compact.finiteMean, map_smul, map_sum, hx, Finset.sum_const,
    Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul,
    inv_mul_cancel₀ hc, one_smul]

section Compression

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- Compression by the inverse on the smooth dual is adjoint to compression
by the original element, for the actual fixed-vector evaluation pairing. -/
theorem compressedAction_adjoint (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (ℓ : fixedVectors (smoothContragredient ρ) K.toSubgroup)
    (v : fixedVectors ρ K.toSubgroup) :
    smoothDualFixedRestriction ρ K.toSubgroup
        (compressedAction (smoothContragredient ρ)
          (isSmooth_smoothContragredient ρ) K hK g⁻¹ ℓ) v =
      smoothDualFixedRestriction ρ K.toSubgroup ℓ
        (compressedAction ρ hρ K hK g v) := by
  have hleft := average_eval_constant (smoothContragredient ρ)
    (isSmooth_smoothContragredient ρ) K hK
    ((smoothDualPairing ρ).flip v.val)
    (smoothContragredient ρ g⁻¹ ℓ.val) (fun k => by
      change (smoothContragredient ρ g⁻¹ ℓ.val).val (ρ k.val⁻¹ v.val) = _
      rw [show ρ k.val⁻¹ v.val = v.val from v.property k⁻¹]
      rfl)
  have hright := average_eval_constant ρ hρ K hK ℓ.val.val (ρ g v.val)
    (fun k => by
      have h := congrArg (fun f : SmoothDual ρ => f.val (ρ g v.val))
        (ℓ.property k⁻¹)
      change ℓ.val.val (ρ ((k⁻¹ : K).val)⁻¹ (ρ g v.val)) = _ at h
      simpa only [InvMemClass.coe_inv, inv_inv] using h)
  change smoothDualPairing ρ
      (Compact.averageMap (smoothContragredient ρ) (isSmooth_smoothContragredient ρ)
        K hK (smoothContragredient ρ g⁻¹ ℓ.val)) v.val =
    ℓ.val.val (Compact.averageMap ρ hρ K hK (ρ g v.val))
  rw [hright]
  calc
    _ = (smoothContragredient ρ g⁻¹ ℓ.val).val v.val := hleft
    _ = ℓ.val.val (ρ g v.val) := by
      change ℓ.val.val (ρ (g⁻¹)⁻¹ v.val) = _
      rw [inv_inv]

end Compression

section Algebra

variable {A : Type uA} {B : Type uB}
variable [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B]

private theorem adjoint_pow (p : A →ₗ[ℂ] Module.Dual ℂ B)
    (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b)) (n : ℕ) (a : A) (b : B) :
    p ((C ^ n) a) b = p a ((D ^ n) b) := by
  induction n generalizing a b with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', Module.End.mul_apply, h, ih, ← Module.End.mul_apply, ← pow_succ]

private theorem stable_pairing_injective
    [FiniteDimensional ℂ A] [FiniteDimensional ℂ B]
    (p : A →ₗ[ℂ] Module.Dual ℂ B) (hp : Function.Injective p)
    (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b)) :
    Function.Injective
      (p.compl₁₂ (⨅ n : ℕ, LinearMap.range (C ^ n)).subtype
        (⨅ n : ℕ, LinearMap.range (D ^ n)).subtype) := by
  rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
  intro a ha
  obtain ⟨n, hn⟩ := Filter.eventually_atTop.mp D.eventually_iInf_range_pow_eq
  have hzero : (C ^ n) a.val = 0 := by
    apply hp
    ext b
    rw [map_zero, LinearMap.zero_apply, adjoint_pow p C D h]
    have hb : (D ^ n) b ∈ ⨅ m : ℕ, LinearMap.range (D ^ m) := by
      rw [hn n le_rfl]
      exact LinearMap.mem_range_self _ b
    exact congrArg (fun f => f ⟨(D ^ n) b, hb⟩) ha
  have hker : a.val ∈ ⨆ m : ℕ, LinearMap.ker (C ^ m) :=
    Submodule.mem_iSup_of_mem n hzero
  have hz := (LinearMap.isCompl_iSup_ker_pow_iInf_range_pow C).disjoint.le_bot
    ⟨hker, a.property⟩
  exact Subtype.ext (by simpa using hz)

private theorem stable_pairing_bijective
    [FiniteDimensional ℂ B]
    (p : A →ₗ[ℂ] Module.Dual ℂ B) (hp : Function.Bijective p)
    (C : Module.End ℂ A) (D : Module.End ℂ B)
    (h : ∀ a b, p (C a) b = p a (D b)) :
    Function.Bijective
      (p.compl₁₂ (⨅ n : ℕ, LinearMap.range (C ^ n)).subtype
        (⨅ n : ℕ, LinearMap.range (D ^ n)).subtype) := by
  let : FiniteDimensional ℂ A := FiniteDimensional.of_injective p hp.1
  refine ⟨stable_pairing_injective p hp.1 C D h, ?_⟩
  apply LinearMap.flip_injective_iff₂.mp
  exact stable_pairing_injective p.flip (LinearMap.flip_injective_iff₂.mpr hp.2)
    D C (fun b a => (h a b).symm)

end Algebra

section Conclusion

variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- There is an equivalence between the stable images whose values are precisely
smooth-dual evaluation on the included vectors. -/
theorem compactCompression_stableEvaluationDuality
    (ρ : Representation ℂ G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (g : G)
    (hfin : FiniteDimensional ℂ (fixedVectors ρ K.toSubgroup)) :
    CompactCompressionStableEvaluationDuality ρ hρ K hK g := by
  let := hfin
  let p := smoothDualFixedRestriction ρ K.toSubgroup
  let q := p.compl₁₂
    (stableImage (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹).subtype
    (stableImage ρ hρ K hK g).subtype
  have hp : Function.Bijective p := smoothDualFixedRestriction_bijective ρ hρ K hK
  have hq0 := stable_pairing_bijective
      (A := fixedVectors (smoothContragredient ρ) K.toSubgroup)
      (B := fixedVectors ρ K.toSubgroup) p hp
      (compressedAction (smoothContragredient ρ) (isSmooth_smoothContragredient ρ) K hK g⁻¹)
      (compressedAction ρ hρ K hK g) (compressedAction_adjoint ρ hρ K hK g)
  have hq : Function.Bijective q := hq0
  exact ⟨LinearEquiv.ofBijective q hq, fun _ _ => rfl⟩

end Conclusion

/-- Actual evaluation duality on compact compression stable images, with all
group, representation and finite fixed-vector hypotheses quantified internally. -/
theorem compactCompression_stableDuality :
    CompactCompressionStableDualityStatement.{uG, uV} := by
  intro G _ _ _ V _ _ ρ hρ K hK g hfin
  exact compactCompression_stableEvaluationDuality ρ hρ K hK g hfin

end Langlands.Jacquet

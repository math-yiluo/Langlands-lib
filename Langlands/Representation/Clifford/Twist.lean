import Langlands.Representation.Clifford.IrreduciblePullback
import Langlands.Representation.Clifford.Coinduction
import Mathlib.LinearAlgebra.Eigenspace.Triangularizable

/-!
# Character twists across a normal subgroup with abelian quotient
-/

noncomputable section

namespace Langlands.Clifford

open Representation

universe uG uV uW

section Basic

variable {G : Type uG} [Group G]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] {W : Type uW} [AddCommGroup W] [Module ℂ W]

/-- An equivalence of representations preserves irreducibility. -/
theorem isIrreducible_of_equiv {ρ : Representation ℂ G V} {σ : Representation ℂ G W}
    (e : ρ.Equiv σ) (h : ρ.IsIrreducible) : σ.IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule] at h ⊢
  exact (LinearMap.isSimpleModule_iff_of_bijective
    (Representation.IntertwiningMap.equivLinearMapAsModule ρ σ e.toIntertwiningMap)
    e.bijective).1 h

/-- A twist by a character trivial on `N` does not change the restriction to `N`. -/
theorem twist_comp_subtype {N : Subgroup G} {χ : G →* ℂˣ} (hχ : N ≤ χ.ker)
    (τ : Representation ℂ G V) : (Langlands.twist χ τ).comp N.subtype = τ.comp N.subtype := by
  ext n v
  change (χ n : ℂ) • τ n v = τ n v
  rw [hχ n.2, Units.val_one, one_smul]

end Basic

section CommonEigenvector

variable {M : Type*} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M] [Nontrivial M]

/-- A pairwise commuting family of endomorphisms of a nonzero finite-dimensional complex
vector space has a common eigenvector. -/
theorem exists_common_eigenvector (S : Set (Module.End ℂ M))
    (hS : ∀ A ∈ S, ∀ B ∈ S, A * B = B * A) :
    ∃ v : M, v ≠ 0 ∧ ∀ A ∈ S, ∃ c : ℂ, A v = c • v := by
  classical
  let P : Submodule ℂ M → Prop := fun U => U ≠ ⊥ ∧ ∀ A ∈ S, U ≤ U.comap A
  have hex : ∃ n : ℕ, ∃ U : Submodule ℂ M, P U ∧ Module.finrank ℂ U = n :=
    ⟨_, ⊤, ⟨bot_ne_top.symm, fun A _ => fun x _ => trivial⟩, rfl⟩
  obtain ⟨U, hU, hUn⟩ := Nat.find_spec hex
  have hmin : ∀ U' : Submodule ℂ M, P U' → Module.finrank ℂ U ≤ Module.finrank ℂ U' := by
    intro U' hU'
    rw [hUn]
    exact Nat.find_min' hex ⟨U', hU', rfl⟩
  have hscalar : ∀ A ∈ S, ∃ c : ℂ, ∀ u ∈ U, A u = c • u := by
    intro A hA
    have : Nontrivial U := Submodule.nontrivial_iff_ne_bot.mpr hU.1
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (A.restrict (hU.2 A hA))
    refine ⟨c, ?_⟩
    let U' : Submodule ℂ M := U ⊓ LinearMap.ker (A - c • 1)
    have hU' : P U' := by
      refine ⟨?_, fun B hB => ?_⟩
      · obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
        intro h0
        apply hw.2
        apply Subtype.ext
        have hw1 : (w : M) ∈ U' := by
          refine ⟨w.2, ?_⟩
          have h := hw.apply_eq_smul
          change (A - c • 1) w = 0
          have h' := congrArg Subtype.val h
          change A w = c • (w : M) at h'
          simp [h']
        rw [h0] at hw1
        exact (Submodule.mem_bot ℂ).mp hw1
      · intro u hu
        refine ⟨hU.2 B hB hu.1, ?_⟩
        have hu2 : (A - c • 1) u = 0 := hu.2
        change (A - c • 1) (B u) = 0
        have hAB := hS A hA B hB
        calc (A - c • 1) (B u) = B ((A - c • 1) u) := by
              simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply,
                map_sub, map_smul]
              rw [← Module.End.mul_apply, hAB, Module.End.mul_apply]
          _ = 0 := by rw [hu2, map_zero]
    have hle : U' ≤ U := inf_le_left
    have heq : U' = U := Submodule.eq_of_le_of_finrank_le hle (hmin U' hU')
    intro u hu
    have hu' : u ∈ U' := heq ▸ hu
    have h0 : (A - c • 1) u = 0 := hu'.2
    simpa [sub_eq_zero] using h0
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU.1
  refine ⟨v, hv0, fun A hA => ?_⟩
  obtain ⟨c, hc⟩ := hscalar A hA
  exact ⟨c, hc v hv⟩

end CommonEigenvector

section TwistQuotient

variable {H : Type uG} [Group H] (N : Subgroup H) [N.Normal]
variable {W : Type uW} [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
variable {V : Type uV} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]

/-- Linear maps intertwining the restrictions to `N`, as a subrepresentation of `linHom`. -/
def restrictIntertwiners (β : Representation ℂ H W) (τ : Representation ℂ H V) :
    Subrepresentation (linHom β τ) where
  toSubmodule := Representation.invariants ((linHom β τ).comp N.subtype)
  apply_mem_toSubmodule h f hf := by
    intro n
    have hn : h⁻¹ * (n : H) * h ∈ N := Subgroup.Normal.conj_mem' ‹N.Normal› n n.2 h
    change linHom β τ (n : H) (linHom β τ h f) = linHom β τ h f
    rw [← Module.End.mul_apply, ← map_mul,
      show (n : H) * h = h * (h⁻¹ * n * h) by group, map_mul, Module.End.mul_apply]
    congr 1
    exact hf ⟨_, hn⟩

/-- If the restrictions of two finite-dimensional representations to a normal subgroup
with abelian quotient have a nonzero intertwiner, some twist by a character trivial on
the subgroup receives a nonzero intertwiner from the first one. -/
theorem exists_twist_intertwining (hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ N)
    (β : Representation ℂ H W) (τ : Representation ℂ H V)
    (P : IntertwiningMap (β.comp N.subtype) (τ.comp N.subtype)) (hP : P ≠ 0) :
    ∃ χ : H →* ℂˣ, N ≤ χ.ker ∧
      ∃ T : IntertwiningMap β (Langlands.twist χ τ), T ≠ 0 := by
  classical
  let S := restrictIntertwiners N β τ
  let R := S.toRepresentation
  have hPmem : P.toLinearMap ∈ S.toSubmodule := by
    intro n
    change τ n ∘ₗ P.toLinearMap ∘ₗ β (n⁻¹ : H) = P.toLinearMap
    apply LinearMap.ext
    intro w
    change τ n (P (β (n⁻¹ : H) w)) = P w
    have h := Representation.IntertwiningMap.isIntertwining _ _ P n (β (n⁻¹ : H) w)
    change P (β (n : H) (β (n⁻¹ : H) w)) = τ n (P (β (n⁻¹ : H) w)) at h
    rw [← h, ← Module.End.mul_apply, ← map_mul]
    simp
  have : Nontrivial S.toSubmodule :=
    ⟨⟨⟨P.toLinearMap, hPmem⟩, 0, fun h => hP (by
      apply Representation.IntertwiningMap.ext
      exact congrArg Subtype.val h)⟩⟩
  have htriv : ∀ n : N, R n = 1 := by
    intro n
    apply LinearMap.ext
    intro f
    apply Subtype.ext
    exact f.2 n
  have hcomR : ∀ x y : H, R x * R y = R y * R x := by
    intro x y
    have hn : x * y * x⁻¹ * y⁻¹ ∈ N := hcomm x y
    have h1 : x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    rw [← map_mul, ← map_mul, h1, map_mul, htriv ⟨_, hn⟩, one_mul]
  obtain ⟨f, hf0, hf⟩ := exists_common_eigenvector (Set.range R) (by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    exact hcomR x y)
  have hstab : ∀ x : H, x ∈ CyclicRestriction.eigenlineStabilizer R f := by
    intro x
    obtain ⟨c, hc⟩ := hf (R x) ⟨x, rfl⟩
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply hf0
      have h1 : R x⁻¹ (R x f) = f := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      rw [hc, zero_smul, map_zero] at h1
      exact h1.symm
    exact ⟨Units.mk0 c hc0, hc⟩
  let χ' := CyclicRestriction.eigenlineCharacter hf0 hstab
  have hχ' := CyclicRestriction.eigenlineCharacter_apply_smul hf0 hstab
  refine ⟨χ'⁻¹, ?_, ?_⟩
  · intro n hn
    have h1 := hχ' n
    rw [htriv ⟨n, hn⟩, Module.End.one_apply] at h1
    have h2 : χ' n = 1 :=
      (CyclicRestriction.eigenline_scalar_unique f hf0 (h1.symm.trans (one_smul ℂ f).symm))
    change χ'⁻¹ n = 1
    rw [MonoidHom.inv_apply, h2, inv_one]
  · let T : IntertwiningMap β (Langlands.twist χ'⁻¹ τ) :=
      { toLinearMap := (f : W →ₗ[ℂ] V)
        isIntertwining' := fun x => by
          apply LinearMap.ext
          intro w
          have h1 := congrArg (fun g : S.toSubmodule => (g : W →ₗ[ℂ] V) (β x w)) (hχ' x)
          change τ x ((f : W →ₗ[ℂ] V) (β x⁻¹ (β x w))) = (χ' x : ℂ) • (f : W →ₗ[ℂ] V) (β x w)
            at h1
          rw [← Module.End.mul_apply (β x⁻¹), ← map_mul, inv_mul_cancel, map_one,
            Module.End.one_apply] at h1
          change (f : W →ₗ[ℂ] V) (β x w) = ((χ'⁻¹ x : ℂˣ) : ℂ) • τ x ((f : W →ₗ[ℂ] V) w)
          rw [h1, MonoidHom.inv_apply, smul_smul, ← Units.val_mul, inv_mul_cancel,
            Units.val_one, one_smul] }
    refine ⟨T, fun h => hf0 ?_⟩
    apply Subtype.ext
    exact congrArg Representation.IntertwiningMap.toLinearMap h

variable {V' : Type*} [AddCommGroup V'] [Module ℂ V']

/-- If every commutator of `H` lies in `N`, two finite-dimensional representations of `H` whose
restrictions to `N` are equivalent and irreducible differ by a character trivial on `N`. -/
theorem exists_twist_equiv (hcomm : ∀ x y : H, x * y * x⁻¹ * y⁻¹ ∈ N)
    (τ : Representation ℂ H V) (τ' : Representation ℂ H V') [FiniteDimensional ℂ V']
    (hτ : Representation.IsIrreducible (τ.comp N.subtype))
    (e : Representation.Equiv (τ'.comp N.subtype) (τ.comp N.subtype)) :
    ∃ χ : H →* ℂˣ, N ≤ χ.ker ∧ Nonempty (τ'.Equiv (Langlands.twist χ τ)) := by
  have hne : e.toIntertwiningMap ≠ 0 := by
    have : Nontrivial V :=
      IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule (τ.comp N.subtype))
    intro h
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    apply hv
    have h1 := congrArg (fun T : IntertwiningMap _ _ => T (e.symm v)) h
    simpa using h1
  obtain ⟨χ, hχ, T, hT⟩ := exists_twist_intertwining N hcomm τ' τ e.toIntertwiningMap hne
  refine ⟨χ, hχ, ?_⟩
  have hτ' : τ'.IsIrreducible :=
    Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp τ' N.subtype (isIrreducible_of_equiv e.symm hτ)
  have htw : (Langlands.twist χ τ).IsIrreducible := by
    apply Langlands.FiniteRepresentation.SplitDegree.isIrreducible_of_comp _ N.subtype
    rw [twist_comp_subtype hχ]
    exact hτ
  exact Langlands.FiniteRepresentation.SplitDegree.nonempty_equiv_of_ne_zero _ _ hτ' htw T hT

omit [N.Normal] in
/-- Twists of a finite-dimensional representation that is irreducible on `N`, by characters
trivial on `N`, are equivalent only if the characters agree. -/
theorem eq_of_twist_equiv (τ : Representation ℂ H V)
    (hτ : Representation.IsIrreducible (τ.comp N.subtype))
    {χ χ' : H →* ℂˣ} (hχ : N ≤ χ.ker) (hχ' : N ≤ χ'.ker)
    (e : (Langlands.twist χ τ).Equiv (Langlands.twist χ' τ)) : χ = χ' := by
  have : Nontrivial V :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ N) (Representation.asModule (τ.comp N.subtype))
  let E : IntertwiningMap (τ.comp N.subtype) (τ.comp N.subtype) :=
    { toLinearMap := e.toLinearMap
      isIntertwining' := fun n => by
        have h := e.isIntertwining' (n : H)
        change e.toLinearMap ∘ₗ ((χ n : ℂ) • τ n) = ((χ' n : ℂ) • τ n) ∘ₗ e.toLinearMap at h
        rw [hχ n.2, hχ' n.2, Units.val_one, one_smul] at h
        exact h }
  obtain ⟨c, hc⟩ := CyclicRestriction.end_eq_smul_one _ hτ E
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hE : ∀ w, e.toLinearMap w = c • w := fun w => by
    have h2 := congrArg (fun T : Module.End ℂ V => T w) hc
    exact h2
  have hc0 : c ≠ 0 := by
    rintro rfl
    apply hv
    apply e.toLinearEquiv.injective
    have h1 := hE v
    rw [zero_smul] at h1
    rw [map_zero]
    exact h1
  ext x
  have h1 := LinearMap.congr_fun (e.isIntertwining' x) v
  change e.toLinearMap ((χ x : ℂ) • τ x v) = (χ' x : ℂ) • τ x (e.toLinearMap v) at h1
  rw [hE, hE, map_smul, smul_smul, smul_smul] at h1
  have hτx : τ x v ≠ 0 := by
    intro h0
    apply hv
    have h3 : τ x⁻¹ (τ x v) = v := by
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    rw [h0, map_zero] at h3
    exact h3.symm
  have h4 := smul_left_injective ℂ hτx h1
  rw [mul_comm (χ' x : ℂ)] at h4
  exact mul_left_cancel₀ hc0 h4

end TwistQuotient

end Langlands.Clifford

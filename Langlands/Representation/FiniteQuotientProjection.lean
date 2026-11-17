import Langlands.Representation.FiniteQuotientAveraging
import Mathlib.LinearAlgebra.Projection

/-! # Averaging equivariant retractions over a finite quotient -/

noncomputable section

universe uk uG uV uW

namespace Langlands.FiniteQuotientAveraging

open Representation

variable {k : Type uk} [CommRing k] {G : Type uG} [Group G]
  {V : Type uV} [AddCommGroup V] [Module k V]
  {W : Type uW} [AddCommGroup W] [Module k W]
  (ρ : Representation k G V) (σ : Representation k G W)
  (N : Subgroup G) [N.Normal] [Fintype (G ⧸ N)]
  [Invertible (Fintype.card (G ⧸ N) : k)]

/-- Averaging an `N`-equivariant linear map produces a `G`-equivariant map. -/
def intertwinerAverage
    (p : IntertwiningMap (ρ.comp N.subtype) (σ.comp N.subtype)) :
    IntertwiningMap ρ σ :=
  invariantsEquivIntertwiningMap ρ σ
    (normalQuotientAverage (linHom ρ σ) N
      ⟨p.toLinearMap,
        (mem_linHom_invariants_iff_isIntertwining
          (ρ := ρ.comp N.subtype) (σ := σ.comp N.subtype) p.toLinearMap).mpr
            ⟨p.isIntertwining⟩⟩)

/-- The averaged intertwiner has the usual normalized conjugation formula. -/
theorem intertwinerAverage_apply
    (p : IntertwiningMap (ρ.comp N.subtype) (σ.comp N.subtype))
    (s : G ⧸ N → G) (hs : ∀ q, (s q : G ⧸ N) = q) (v : V) :
    intertwinerAverage ρ σ N p v =
      ⅟(Fintype.card (G ⧸ N) : k) •
        ∑ q : G ⧸ N, σ (s q) (p (ρ (s q)⁻¹ v)) := by
  have h := normalQuotientAverage_apply (linHom ρ σ) N
    ⟨p.toLinearMap,
      (mem_linHom_invariants_iff_isIntertwining
        (ρ := ρ.comp N.subtype) (σ := σ.comp N.subtype) p.toLinearMap).mpr
          ⟨p.isIntertwining⟩⟩ s hs
  have hv := congrArg (fun f : V →ₗ[k] W => f v) h
  change
    ((normalQuotientAverage (linHom ρ σ) N
      ⟨p.toLinearMap,
        (mem_linHom_invariants_iff_isIntertwining
          (ρ := ρ.comp N.subtype) (σ := σ.comp N.subtype) p.toLinearMap).mpr
            ⟨p.isIntertwining⟩⟩).val v) = _
  simpa only [LinearMap.smul_apply, LinearMap.sum_apply, linHom_apply,
    LinearMap.comp_apply, IntertwiningMap.toLinearMap_apply] using hv

/-- Averaging preserves a left inverse of a `G`-equivariant linear map. -/
theorem intertwinerAverage_leftInverse
    (p : IntertwiningMap (ρ.comp N.subtype) (σ.comp N.subtype))
    (i : IntertwiningMap σ ρ) (hp : Function.LeftInverse p i) :
    Function.LeftInverse (intertwinerAverage ρ σ N p) i := by
  intro w
  rw [intertwinerAverage_apply ρ σ N p Quotient.out (fun q => Quotient.out_eq q)]
  have hterm (q : G ⧸ N) : σ q.out (p (ρ q.out⁻¹ (i w))) = w := by
    rw [← i.isIntertwining _ _ (q.out⁻¹) w, hp]
    exact Representation.self_inv_apply σ q.out w
  simp only [hterm, Finset.sum_const, Finset.card_univ]
  rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

omit σ in
/-- Averaging a projection onto a `G`-stable submodule preserves its image and its
restriction to that submodule, while making the projection `G`-equivariant. -/
theorem intertwinerAverage_isProj
    (U : Subrepresentation ρ)
    (p : IntertwiningMap (ρ.comp N.subtype) (ρ.comp N.subtype))
    (hp : LinearMap.IsProj U.toSubmodule p.toLinearMap) :
    LinearMap.IsProj U.toSubmodule
      (intertwinerAverage ρ ρ N p).toLinearMap := by
  constructor
  · intro v
    rw [IntertwiningMap.toLinearMap_apply, intertwinerAverage_apply ρ ρ N p
      Quotient.out (fun q => Quotient.out_eq q)]
    exact U.toSubmodule.smul_mem _ (U.toSubmodule.sum_mem fun q _ =>
      U.apply_mem_toSubmodule q.out (hp.1 _))
  · intro v hv
    rw [IntertwiningMap.toLinearMap_apply, intertwinerAverage_apply ρ ρ N p
      Quotient.out (fun q => Quotient.out_eq q)]
    have hterm (q : G ⧸ N) : ρ q.out (p (ρ q.out⁻¹ v)) = v := by
      change ρ q.out (p.toLinearMap (ρ q.out⁻¹ v)) = v
      rw [hp.2 _ (U.apply_mem_toSubmodule q.out⁻¹ hv)]
      exact Representation.self_inv_apply ρ q.out v
    simp only [hterm, Finset.sum_const, Finset.card_univ]
    rw [← Nat.cast_smul_eq_nsmul k, smul_smul, invOf_mul_self, one_smul]

end Langlands.FiniteQuotientAveraging

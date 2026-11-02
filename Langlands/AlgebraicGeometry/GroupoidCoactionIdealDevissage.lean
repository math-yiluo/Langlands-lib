import Langlands.AlgebraicGeometry.GroupoidCoactionInvariantIdeal
import Mathlib.RingTheory.Finiteness.Ideal

/-! # Dévissage by powers of an invariant ideal -/

universe u v

open TensorProduct

namespace Langlands.AlgebraicGeometry.GroupoidCoaction

variable {B C : Type u} [CommRing B] [CommRing C] [Algebra B C]
variable {t : B →+* C}

/-- Cocycle vanishing for all finite coactions annihilated by a fixed ideal. -/
def FiniteAnnihilatorVanishing (t : B →+* C) (I : Ideal B) : Prop :=
  ∀ (M : Type v) [AddCommGroup M] [Module B M] [Module.Finite B M]
    (θ : GroupoidCoaction t M),
    I ≤ Module.annihilator B M → θ.OneCohomologyVanishes

/-- Vanishing on modules annihilated by an invariant ideal extends to modules
annihilated by any power of that ideal. -/
theorem finiteAnnihilatorVanishing_pow [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t) (I : Ideal B)
    (hI : IsInvariantIdeal t I) (hvan : FiniteAnnihilatorVanishing.{u, v} t I)
    (n : ℕ) : FiniteAnnihilatorVanishing.{u, v} t (I ^ n) := by
  let : Module.Flat B C := RingHom.flat_algebraMap_iff.mp
    (RingHom.Etale.iff_flat_and_formallyUnramified.mp hE.etale_algebraMap).1
  induction n with
  | zero =>
    intro M _ _ _ θ hn
    have hM (m : M) : m = 0 := by
      have h1 : (1 : B) ∈ Module.annihilator B M := hn (by simp)
      simpa only [one_smul] using Module.mem_annihilator.mp h1 m
    intro x hcy
    clear hcy
    refine ⟨0, ?_⟩
    have hx : x = 0 := by
      induction x with
      | tmul c m => rw [hM m, tmul_zero]
      | add x y hx hy => rw [hx, hy, add_zero]
    simp [hx]
  | succ n ih =>
    intro M _ _ _ θ hn
    let N : Submodule B M := I • ⊤
    have hN : θ.IsStableSubmodule N := hI.isStableSubmodule_smul_top θ
    let θN := submodule θ N hE hN
    let θQ := submoduleQuotient θ N hN
    have hnN : I ^ n ≤ Module.annihilator B N := by
      intro a ha
      apply Module.mem_annihilator.mpr
      intro m
      apply Subtype.ext
      change a • (m : M) = 0
      refine Submodule.smul_induction_on m.property ?_ ?_
      · intro b hb m _
        rw [smul_smul]
        exact Module.mem_annihilator.mp
          (hn (by rw [pow_succ]; exact Ideal.mul_mem_mul ha hb)) m
      · intro x y hx hy
        simp only [smul_add, hx, hy, add_zero]
    have hIQ : I ≤ Module.annihilator B (M ⧸ N) := by
      intro a ha
      apply Module.mem_annihilator.mpr
      intro q
      obtain ⟨m, rfl⟩ := N.mkQ_surjective q
      rw [← N.mkQ.map_smul]
      apply (Submodule.Quotient.mk_eq_zero N).mpr
      exact Submodule.smul_mem_smul ha (Submodule.mem_top : m ∈ (⊤ : Submodule B M))
    exact oneCohomologyVanishes_of_shortExact N.subtype N.mkQ
      (submodule_subtype_isHom θ N hE hN)
      (submoduleQuotient_mkQ_isHom θ N hN)
      N.subtype_injective N.mkQ_surjective (by simp)
      (ih N θN hnN) (hvan (M ⧸ N) θQ hIQ)

/-- The power dévissage applies whenever the ideal lies in the radical of the
module's annihilator. -/
theorem oneCohomologyVanishes_of_le_radical_annihilator [IsNoetherianRing B]
    (hE : RingEtaleEquivalenceRelation t) (I : Ideal B)
    (hI : IsInvariantIdeal t I) (hvan : FiniteAnnihilatorVanishing.{u, v} t I)
    {M : Type v} [AddCommGroup M] [Module B M] [Module.Finite B M]
    (θ : GroupoidCoaction t M)
    (hM : I ≤ (Module.annihilator B M).radical) : θ.OneCohomologyVanishes := by
  obtain ⟨n, hn⟩ := Ideal.exists_pow_le_of_le_radical_of_fg hM I.fg_of_isNoetherianRing
  exact finiteAnnihilatorVanishing_pow hE I hI hvan n M θ hn

end Langlands.AlgebraicGeometry.GroupoidCoaction

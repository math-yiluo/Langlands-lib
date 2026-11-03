import Langlands.GroupScheme.Rational.RootReflectionAssembly
import Langlands.GroupScheme.Absolute.RegularPerturbation

/-! # Integral coroot extraction from rank-one character differences -/

noncomputable section

universe u v

namespace Langlands.GroupScheme

namespace IntegralCoroot

variable {M : Type v} [AddCommGroup M] [Module.IsTorsionFree ℤ M]
  (a : M) (ha : a ≠ 0) (w : M →ₗ[ℤ] M)
  (hdiv : ∀ x : M, ∃ m : ℤ, x - w x = m • a)

/-- The integral coefficient of the rank-one difference from the identity. -/
def differenceFunctional : Module.Dual ℤ M :=
  ((LinearEquiv.toSpanNonzeroSingleton ℤ M a ha).symm.toLinearMap).comp
    ((LinearMap.id - w).codRestrict (Submodule.span ℤ {a}) (fun x => by
      obtain ⟨m, hm⟩ := hdiv x
      exact Submodule.mem_span_singleton.mpr ⟨m, hm.symm⟩))

theorem differenceFunctional_smul (x : M) :
    differenceFunctional a ha w hdiv x • a = x - w x := by
  exact LinearEquiv.toSpanNonzeroSingleton_symm_apply_smul ℤ M a ha _

/-- Flipping the nonzero distinguished vector forces coefficient two. -/
theorem differenceFunctional_self (hflip : w a = -a) :
    differenceFunctional a ha w hdiv a = 2 := by
  apply smul_left_injective ℤ ha
  change differenceFunctional a ha w hdiv a • a = (2 : ℤ) • a
  rw [differenceFunctional_smul, hflip, sub_neg_eq_add, two_smul]

/-- The extracted functional gives the whole-lattice reflection formula. -/
theorem action_eq (x : M) :
    w x = x - differenceFunctional a ha w hdiv x • a := by
  rw [differenceFunctional_smul, sub_sub_cancel]

end IntegralCoroot

open CategoryTheory AlgebraicGeometry

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}

/-- A root-flipping endomorphism of the character lattice whose character
 differences are integral multiples of the root determines a unique actual
 integral cocharacter with the reflection formula. -/
theorem IsSplitTorus.existsUnique_coroot_of_integral_difference
    (hT : IsSplitTorus T.toGrp) (a : characterLattice T) (ha : a ≠ 0)
    (w : characterLattice T →ₗ[ℤ] characterLattice T)
    (hflip : w a = -a)
    (hdiv : ∀ χ : characterLattice T, ∃ m : ℤ, χ - w χ = m • a) :
    ∃! ν : cocharacterLattice T,
      latticePairing T a ν = 2 ∧
        ∀ χ : characterLattice T, w χ = χ - latticePairing T χ ν • a := by
  have := hT.isPerfPair_latticePairing
  have := Module.IsReflexive.of_isPerfPair (p := latticePairing T)
  let f := IntegralCoroot.differenceFunctional a ha w hdiv
  let ν := (latticePairing T).flip.toPerfPair.symm f
  have hν (χ : characterLattice T) : latticePairing T χ ν = f χ :=
    LinearMap.apply_toPerfPair_flip _ _ _
  refine ⟨ν, ⟨?_, ?_⟩, ?_⟩
  · rw [hν]
    exact IntegralCoroot.differenceFunctional_self a ha w hdiv hflip
  · intro χ
    rw [hν]
    exact IntegralCoroot.action_eq a ha w hdiv χ
  · intro μ hμ
    apply hT.isPerfPair_latticePairing.bijective_right.injective
    apply LinearMap.ext
    intro χ
    change latticePairing T χ μ = latticePairing T χ ν
    apply smul_left_injective ℤ ha
    have h := hμ.2 χ
    rw [IntegralCoroot.action_eq a ha w hdiv χ, ← hν] at h
    exact (sub_right_inj.mp h).symm

end Langlands.GroupScheme

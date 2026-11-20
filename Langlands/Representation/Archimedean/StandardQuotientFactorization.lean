import Langlands.Representation.Archimedean.ComplexReverseIntertwinerTied
import Langlands.Representation.Archimedean.ComplexTemperedStandardIrreducibleProof
import Langlands.Representation.Archimedean.RealStandardIrreducibleCriterionReduction

/-! # Realizing a standard quotient through a factored reverse intertwiner -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open scoped TensorProduct Matrix.Norms.Operator

attribute [local instance 100] LieRing.ofAssociativeRing

section LinearAlgebra

variable {K L M J : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup M] [Module ℂ M] [AddCommGroup J] [Module ℂ J]
    {κM : Representation ℂ K M} {πM : L →ₗ⁅ℂ⁆ Module.End ℂ M}

/-- A surjective map from a stable subspace that respects the restricted compact and
complexified Lie actions realizes its target as a subquotient. -/
def IsGKSubquotientMap
    (κJ : Representation ℂ K J) (πJ : L →ₗ⁅ℂ⁆ Module.End ℂ J)
    {W : Submodule ℂ M} (hW : IsGKSubmodule κM πM W) (q : W →ₗ[ℂ] J) : Prop :=
  Function.Surjective q ∧
    (∀ k (w : W), q ⟨κM k w, hW.1 k w w.2⟩ = κJ k (q w)) ∧
    ∀ X (w : W), q ⟨πM X w, hW.2 X w w.2⟩ = πJ X (q w)

end LinearAlgebra

section Factorization

variable {K L V M N J : Type*} [Group K] [LieRing L] [LieAlgebra ℂ L]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup M] [Module ℂ M]
    [AddCommGroup N] [Module ℂ N] [AddCommGroup J] [Module ℂ J]
    {κV : Representation ℂ K V} {πV : L →ₗ⁅ℂ⁆ Module.End ℂ V}
    {κM : Representation ℂ K M} {πM : L →ₗ⁅ℂ⁆ Module.End ℂ M}
    {κN : Representation ℂ K N} {πN : L →ₗ⁅ℂ⁆ Module.End ℂ N}
    {κJ : Representation ℂ K J} {πJ : L →ₗ⁅ℂ⁆ Module.End ℂ J}

private theorem exists_quotient_on_range_of_factorization
    (A : V →ₗ[ℂ] M) (B : M →ₗ[ℂ] N) (p : V →ₗ[ℂ] J)
    (hAK : ∀ k x, A (κV k x) = κM k (A x))
    (hAL : ∀ X x, A (πV X x) = πM X (A x))
    (hTK : ∀ k x, (B ∘ₗ A) (κV k x) = κN k ((B ∘ₗ A) x))
    (hTL : ∀ X x, (B ∘ₗ A) (πV X x) = πN X ((B ∘ₗ A) x))
    (hpK : ∀ k x, p (κV k x) = κJ k (p x))
    (hpL : ∀ X x, p (πV X x) = πJ X (p x))
    (hJ : IsIrreducibleGKModule κJ πJ) (hp : Function.Surjective p)
    (hT : B ∘ₗ A ≠ 0)
    (hmax : ∀ W : Submodule ℂ V, IsGKSubmodule κV πV W → W ≠ ⊤ →
      W ≤ LinearMap.ker (B ∘ₗ A)) :
    ∃ hW : IsGKSubmodule κM πM (LinearMap.range A),
      ∃ q : LinearMap.range A →ₗ[ℂ] J,
        IsGKSubquotientMap κJ πJ hW q ∧ q ∘ₗ A.rangeRestrict = p := by
  have hp₀ : p ≠ 0 := by
    have : Nontrivial J := hJ.1
    intro h
    obtain ⟨y, hy⟩ := exists_ne (0 : J)
    obtain ⟨x, hx⟩ := hp y
    rw [h, LinearMap.zero_apply] at hx
    exact hy hx.symm
  have hker : LinearMap.ker (B ∘ₗ A) = LinearMap.ker p :=
    eq_ker_of_largest_proper hpK hpL hJ hp₀
      (isGKSubmodule_ker_of_intertwine hTK hTL)
      (fun h => hT (LinearMap.ker_eq_top.mp h)) hmax
  have hAp : LinearMap.ker A ≤ LinearMap.ker p := by
    rw [← hker]
    intro x hx
    rw [LinearMap.mem_ker, LinearMap.comp_apply, LinearMap.mem_ker.mp hx, map_zero]
  have hW := isGKSubmodule_map_of_intertwine hAK hAL
    (W := ⊤) ⟨fun _ _ _ => Submodule.mem_top, fun _ _ _ => Submodule.mem_top⟩
  rw [Submodule.map_top] at hW
  let q := ((LinearMap.ker A).liftQ p hAp) ∘ₗ A.quotKerEquivRange.symm.toLinearMap
  have hq (x : V) : q (A.rangeRestrict x) = p x := by
    change (LinearMap.ker A).liftQ p hAp
      (A.quotKerEquivRange.symm ⟨A x, _⟩) = p x
    rw [LinearMap.quotKerEquivRange_symm_apply_image]
    rfl
  refine ⟨hW, q, ⟨?_, ?_, ?_⟩, LinearMap.ext hq⟩
  · intro y
    obtain ⟨x, rfl⟩ := hp y
    exact ⟨A.rangeRestrict x, hq x⟩
  · intro k w
    obtain ⟨x, rfl⟩ := A.surjective_rangeRestrict w
    have e : (⟨κM k (A x), hW.1 k _ (A.rangeRestrict x).2⟩ : LinearMap.range A) =
        A.rangeRestrict (κV k x) :=
      Subtype.ext (hAK k x).symm
    calc
      _ = q (A.rangeRestrict (κV k x)) := congrArg q e
      _ = p (κV k x) := hq _
      _ = κJ k (p x) := hpK k x
      _ = κJ k (q (A.rangeRestrict x)) := congrArg (κJ k) (hq x).symm
  · intro X w
    obtain ⟨x, rfl⟩ := A.surjective_rangeRestrict w
    have e : (⟨πM X (A x), hW.2 X _ (A.rangeRestrict x).2⟩ : LinearMap.range A) =
        A.rangeRestrict (πV X x) :=
      Subtype.ext (hAL X x).symm
    calc
      _ = q (A.rangeRestrict (πV X x)) := congrArg q e
      _ = p (πV X x) := hq _
      _ = πJ X (p x) := hpL X x
      _ = πJ X (q (A.rangeRestrict x)) := congrArg (πJ X) (hq x).symm

end Factorization

variable {J : Type*} [AddCommGroup J] [Module ℂ J] {n : ℕ}

local notation "ComplexStandard(" n ", " ds ")" =>
  kFiniteFunctions (complexStandardModule n ds) (unitaryCompact ℂ n)
local notation "RealStandard(" n ", " ds ")" =>
  kFiniteFunctions (realStandardModule n ds) (unitaryCompact ℝ n)

/-- A nonzero intertwiner to the reversed complex standard module that factors through
`es` realizes the Langlands quotient as a quotient of a stable subspace of the standard
module of `es`. The stable subspace is the range of the first intertwiner. -/
theorem complexStandardQuotient_of_reverse_factorization {ds es : List ComplexCharacterData}
    (hn : ds.length = n) (ho : IsComplexLanglandsOrdered ds)
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℂ) J}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℂ) →ₗ⁅ℂ⁆ Module.End ℂ J}
    (hJ : IsIrreducibleGKModule κ π)
    {p : ComplexStandard(n, ds) →ₗ[ℂ] J} (hp : Function.Surjective p)
    (hpGK : IsComplexStandardIntertwining n κ π ds p)
    {A : ComplexStandard(n, ds) →ₗ[ℂ] ComplexStandard(n, es)}
    {B : ComplexStandard(n, es) →ₗ[ℂ] ComplexStandard(n, ds.reverse)}
    (hA : IsComplexStandardIntertwining n (complexStandardRep n es) (complexStandardLie n es) ds A)
    (hB : IsComplexStandardIntertwining n (complexStandardRep n ds.reverse)
      (complexStandardLie n ds.reverse) es B)
    (hne : B ∘ₗ A ≠ 0) :
    ∃ hW : IsGKSubmodule (complexStandardRep n es) (complexStandardLie n es) (LinearMap.range A),
      ∃ q : LinearMap.range A →ₗ[ℂ] J,
        IsGKSubquotientMap κ π hW q ∧ q ∘ₗ A.rangeRestrict = p := by
  have hT := hA.comp B hB.map_complexStandardRep (fun X f => hB.map_complexStandardLie (1 ⊗ₜ X) f)
  exact exists_quotient_on_range_of_factorization A B p
    hA.map_complexStandardRep hA.map_complexStandardLie
    hT.map_complexStandardRep hT.map_complexStandardLie
    hpGK.map_complexStandardRep hpGK.map_complexStandardLie hJ hp hne
    (fun W hW hproper =>
      complexReverseIntertwinerKernelReduction complexTemperedStandardIrreducible
        n ds (B ∘ₗ A) W hn ho hT hW hproper)

/-- The corresponding realization for real standard modules, using the real
reverse-intertwiner kernel theorem as an explicit input. -/
theorem realStandardQuotient_of_reverse_factorization
    (hrev : RealReverseIntertwinerKernelStatement) {ds es : List RealBlock}
    (hn : realRank ds = n) (ho : IsRealLanglandsOrdered ds)
    {κ : Representation ℂ (Matrix.unitaryGroup (Fin n) ℝ) J}
    {π : (ℂ ⊗[ℝ] Matrix (Fin n) (Fin n) ℝ) →ₗ⁅ℂ⁆ Module.End ℂ J}
    (hJ : IsIrreducibleGKModule κ π)
    {p : RealStandard(n, ds) →ₗ[ℂ] J} (hp : Function.Surjective p)
    (hpGK : IsRealStandardIntertwiner n κ π ds p)
    {A : RealStandard(n, ds) →ₗ[ℂ] RealStandard(n, es)}
    {B : RealStandard(n, es) →ₗ[ℂ] RealStandard(n, ds.reverse)}
    (hA : IsRealStandardIntertwiner n (realStandardRep n es) (realStandardLie n es) ds A)
    (hB : IsRealStandardIntertwiner n (realStandardRep n ds.reverse)
      (realStandardLie n ds.reverse) es B)
    (hne : B ∘ₗ A ≠ 0) :
    ∃ hW : IsGKSubmodule (realStandardRep n es) (realStandardLie n es) (LinearMap.range A),
      ∃ q : LinearMap.range A →ₗ[ℂ] J,
        IsGKSubquotientMap κ π hW q ∧ q ∘ₗ A.rangeRestrict = p := by
  have hT := hA.comp_standard hB
  exact exists_quotient_on_range_of_factorization A B p
    hA.map_realStandardRep hA.map_realStandardLie
    hT.map_realStandardRep hT.map_realStandardLie
    hpGK.map_realStandardRep hpGK.map_realStandardLie hJ hp hne
    (fun W hW hproper => hrev n ds (B ∘ₗ A) W hn ho hT hW hproper)

end Langlands.Archimedean

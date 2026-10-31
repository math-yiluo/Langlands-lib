import Langlands.Algebra.NonUnitalModuleExactnessStatements

/-!
# Exactness through the original nonunital stable range and kernel

Categorical exactness is tested by the kernel-to-cokernel composite. The
published comparison isomorphisms reduce this to the actual subtype inclusion
and quotient projection, whose zero criterion is stable-range membership.
-/

set_option autoImplicit false

namespace Langlands.Algebra

open CategoryTheory CategoryTheory.Limits

universe uA uM

namespace NonUnitalModuleCat

variable {A : Type uA} [NonUnitalRing A]

/-- Test exactness on the existing concrete kernel and cokernel maps. -/
theorem exact_iff_concreteKernelι_comp_concreteCokernelπ_zero
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)) :
    S.Exact ↔ concreteKernelι S.g ≫ concreteCokernelπ S.f = 0 := by
  rw [S.exact_iff_kernel_ι_comp_cokernel_π_zero,
    ← cancel_epi (kernelIsoConcrete S.g).inv,
    ← cancel_mono (cokernelIsoConcrete S.f).hom]
  simp only [← Category.assoc, kernelIsoConcrete_inv_ι, comp_zero, zero_comp]
  rw [Category.assoc, π_cokernelIsoConcrete_hom]

/-- Exactness is equality of the unchanged original stable range and kernel. -/
theorem exact_iff_rangeSubmodule_eq_kernelSubmodule
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)) :
    S.Exact ↔ S.f.rangeSubmodule = S.g.kernelSubmodule := by
  rw [exact_iff_concreteKernelι_comp_concreteCokernelπ_zero]
  constructor
  · intro h
    apply SetLike.ext
    intro n
    constructor
    · rintro ⟨m, rfl⟩
      exact congrArg (fun k : S.X₁ ⟶ S.X₃ =>
        NonUnitalModuleHom.toAddMonoidHom k m) S.zero
    · intro hn
      apply (concreteCokernelπ_eq_zero_iff S.f n).1
      exact congrArg
        (fun k : concreteKernel S.g ⟶ concreteCokernel S.f =>
          NonUnitalModuleHom.toAddMonoidHom k ⟨n, hn⟩) h
  · intro h
    apply NonUnitalModuleHom.ext
    intro n
    exact (concreteCokernelπ_eq_zero_iff S.f n.val).2 (h.symm ▸ n.property)

end NonUnitalModuleCat

/-- The exact published closed proposition, with independent ring and carrier universes. -/
theorem nonUnitalModuleExactnessStatement :
    NonUnitalModuleExactnessStatement.{uA, uM} := by
  intro A _ S
  exact NonUnitalModuleCat.exact_iff_rangeSubmodule_eq_kernelSubmodule S

/-! Complete unapplied interfaces and both unequal-universe specializations. -/

example : NonUnitalModuleExactnessStatement.{uA, uM} :=
  @nonUnitalModuleExactnessStatement.{uA, uM}

example : (A : Type uA) → [NonUnitalRing A] →
    (S : ShortComplex (NonUnitalModuleCat.{uA, uM} A)) →
    (S.Exact ↔ S.f.rangeSubmodule = S.g.kernelSubmodule) :=
  @nonUnitalModuleExactnessStatement.{uA, uM}

example : NonUnitalModuleExactnessStatement.{0, 1} :=
  nonUnitalModuleExactnessStatement.{0, 1}

example : NonUnitalModuleExactnessStatement.{1, 0} :=
  nonUnitalModuleExactnessStatement.{1, 0}

end Langlands.Algebra

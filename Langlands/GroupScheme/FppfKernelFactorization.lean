import Langlands.GroupScheme.FppfQuotientComparison
import Langlands.GroupScheme.MatrixRepresentation.UnipotentQuotient
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! # Factorization through a supplied full-kernel quotient -/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option backward.defeqAttrib.useBackward true

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FppfKernelFactorization

variable {S : Scheme.{u}} {H G Q : GroupScheme S}
    (f : H ⟶ G) (q : H ⟶ Q)
    (hq : RelativeRoot.IsFppfQuotient (SubgroupFunctor.range (kernelι f)) q)

include hq

/-- A quotient by the full kernel of `f` has its whole kernel killed by `f`. -/
theorem kernel_comp_eq_zero : kernelι q ≫ f = 0 := by
  apply Grp.hom_ext
  change (kernelι q).hom.hom ≫ f.hom.hom = 1
  apply (mem_range_kernelι_iff f _).mp
  rw [← hq.2.2.2]
  exact SubgroupFunctor.mem_range.mpr ⟨𝟙 _, Category.id_comp _⟩

variable [QuasiCompact q.hom.hom.left]

/-- The canonical factor through a supplied quasi-compact fppf full-kernel quotient. -/
def factor : Q ⟶ G :=
  letI := hq.1
  letI := hq.2.1
  FpqcHomDescent.hom q f (kernel_comp_eq_zero f q hq)

@[reassoc]
theorem fac : q ≫ factor f q hq = f := by
  have := hq.1
  have := hq.2.1
  exact FpqcHomDescent.fac q f (kernel_comp_eq_zero f q hq)

/-- No further full kernel remains after dividing by the full kernel of `f`. -/
theorem mono_factor : Mono (factor f q hq).hom.hom := by
  have := hq.1
  have := hq.2.1
  apply FpqcHomDescent.mono_of_kernel_range_le q f (factor f q hq) (fac f q hq)
  exact le_of_eq hq.2.2.2.symm

/-- The factor is uniquely characterized by its composition with the quotient. -/
theorem unique (v : Q ⟶ G) (hv : q ≫ v = f) : v = factor f q hq := by
  have := hq.1
  have := hq.2.1
  exact FpqcHomDescent.unique q f (kernel_comp_eq_zero f q hq) v hv

omit [QuasiCompact q.hom.hom.left] in
/-- An affine full-kernel fppf quotient supplies the required monomorphic factor. -/
theorem exists_mono_factor [IsAffineHom q.hom.hom.left] :
    ∃ v : Q ⟶ G, Mono v.hom.hom ∧ q ≫ v = f :=
  ⟨factor f q hq, mono_factor f q hq, fac f q hq⟩

end Langlands.GroupScheme.FppfKernelFactorization

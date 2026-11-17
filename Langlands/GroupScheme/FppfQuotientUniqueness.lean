import Langlands.GroupScheme.FppfHomDescent
import Langlands.GroupScheme.FppfQuotientComparison

/-! # Uniqueness of supplied full fppf group-scheme quotients -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme.FppfQuotientComparison

variable {S : Scheme.{u}} {G Q R : GroupScheme S} {F : SubgroupFunctor G}
    {q : G ⟶ Q} {r : G ⟶ R}
    (hq : RelativeRoot.IsFppfQuotient F q) (hr : RelativeRoot.IsFppfQuotient F r)

/-- The canonical comparison for the full fppf quotient predicate. -/
def fppfHom : Q ⟶ R :=
  letI := hq.1
  letI := hq.2.1
  letI := hq.2.2.1
  FppfHomDescent.hom q r (kernel_comp hq hr)

@[reassoc]
theorem fppfHom_fac : q ≫ fppfHom hq hr = r := by
  have := hq.1
  have := hq.2.1
  have := hq.2.2.1
  exact FppfHomDescent.fac q r (kernel_comp hq hr)

/-- Two supplied full fppf quotients of the same subgroup are canonically isomorphic. -/
def fppfIso : Q ≅ R where
  hom := fppfHom hq hr
  inv := fppfHom hr hq
  hom_inv_id := by
    apply hom_ext hq
    rw [← Category.assoc, fppfHom_fac, fppfHom_fac, Category.comp_id]
  inv_hom_id := by
    apply hom_ext hr
    rw [← Category.assoc, fppfHom_fac, fppfHom_fac, Category.comp_id]

@[reassoc]
theorem fppfIso_fac : q ≫ (fppfIso hq hr).hom = r := fppfHom_fac hq hr

/-- The common-source equation uniquely determines the comparison isomorphism. -/
theorem fppfIso_unique (e : Q ≅ R) (he : q ≫ e.hom = r) : e = fppfIso hq hr := by
  apply Iso.ext
  apply hom_ext hq
  rw [he, fppfIso_fac]

end Langlands.GroupScheme.FppfQuotientComparison

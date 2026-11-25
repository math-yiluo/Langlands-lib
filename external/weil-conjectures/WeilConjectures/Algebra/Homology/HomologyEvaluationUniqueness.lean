/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomologyEvaluationDefinitions
import WeilConjectures.Algebra.Homology.HomologyEvaluationLocalCycleLift
import WeilConjectures.Algebra.Homology.HomologyEvaluationUniquenessExt

/-! # A step in the construction of homology evaluation -/

@[expose] public section
set_option autoImplicit false
universe u
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
namespace CategoryTheory

/-- Cycle evaluation determines the morphism uniquely.
Source: Stacks Project, Tag 08DH, separatedness of internal Hom.
(blueprint: new-b2-homology-evaluation-uniqueness).

Proof: Fix an open U and a Hom-cocycle phi over U. To compare the two
internal-Hom sections obtained by applying e and e' to [phi], restrict to any
open A contained in U and evaluate on an arbitrary section of H^(-n)(T) over A.
The homology class map is an epimorphism of sheaves, so that section is represented
by a cycle z after passing to a covering of A. Restrict phi to each member of
this covering. The Hom differential equation says its evaluation on z is a
J-cycle; the kernel property of the cycle inclusion supplies b with that value.
The two assumed cycle formulas identify both evaluations with [b]. Separatedness
of H^0(J) glues this equality over A. This gives equality of the internal-Hom
sections on every further open and hence equality of their natural transformations.
Finally every section of H^n(Hom(T,J)) lifts locally to a Hom-cocycle, because
its homology class map is a sheaf epimorphism. Apply the equality just proved
on those lifts and use separatedness of the internal Hom to conclude e=e'.
Empty opens and zero source or target give the same equality without requiring
any nonzero section. No local perfection or concentration hypothesis is used. -/
theorem homologyEvaluation_unique_of_cycle (X : AlgebraicGeometry.Scheme.{u})
    (T J : CochainComplex X.Modules ℤ) (n : ℤ)
    (e e' : (homComplex (R := X.sheaf) T J).homology n ⟶
      SheafOfModules.homObj (R := X.sheaf) (T.homology (-n)) (J.homology 0))
    (he : IsHomologyEvaluation X T J n e)
    (he' : IsHomologyEvaluation X T J n e') : e = e' := by
  apply homologyEvaluation_unique_of_cycle_of_local_lifts X T J n e e' he he'
  exact homologyEvaluation_local_cycle_lift X T J n

end CategoryTheory

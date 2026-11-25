/-
Copyright (c) 2026 Bin Wu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bin Wu
-/

module

public import WeilConjectures.Algebra.Homology.HomComplex
public import WeilConjectures.Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.HomotopyCategory.SingleFunctors
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationIsIso
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationComm
import WeilConjectures.Algebra.Homology.HomComplexUnitEvaluationNaturality

/-! # Hom complexes from the structure sheaf

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7.
(blueprint: lem-sc-hom-complex-unit-iso).
-/

@[expose] public section
universe u
open CategoryTheory Opposite
namespace CategoryTheory

/-- Hom from the unit concentrated in degree zero is naturally the identity on complexes.

Source: Stacks Project, sites-cohomology.tex, Sections 0A8X and 08J7.
(blueprint: lem-sc-hom-complex-unit-iso).

Proof:
1. In degree n, the product defining Hom has factors Hom(L^p, M^(p+n)). For
   L = O[0], L^p is zero when p is nonzero, so these factors are zero. The
   projection to p = 0 therefore identifies the product with Hom(O, M^n).
2. Compose this projection with SheafOfModules.homObjUnitIso, evaluation at one.
   Its inverse sends x to the family whose zero component is r -> r*x and
   whose other components are zero. The product universal property and the
   two inverse identities for evaluation prove both inverse identities.
3. The differential formula in homComplex_exists has a zero precomposition
   term because L has zero differential. Its remaining term is postcomposition
   by the differential of M, which commutes with evaluation at one. Thus the
   degreewise isomorphisms form a chain isomorphism.
4. The map formula in homComplex_exists identifies the action of a chain map
   with postcomposition in every degree. Evaluation commutes with this action,
   giving the asserted natural isomorphism. This applies in every integer
   degree, without any boundedness or injectivity hypothesis. -/
theorem homComplex_unit_iso
    {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (R : Sheaf J CommRingCat.{u}) :
    Nonempty ((homComplexFunctor (R := R)).obj
      (op ((CochainComplex.singleFunctor
        (SheafOfModules.{u} ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)) 0).obj
          (SheafOfModules.unit ((sheafCompose J (forget₂ CommRingCat RingCat)).obj R)))) ≅
        𝟭 _) := by
  classical
  let F := homComplexUnitFunctor J R
  have hIso (M) (n) := homComplex_unit_evaluation_isIso J R M n
  let e := fun M => HomologicalComplex.Hom.isoOfComponents
    (fun n => asIso (homComplexUnitEvaluation J R M n))
    (fun n m h => homComplex_unit_evaluation_comm J R M n m h)
  refine ⟨NatIso.ofComponents e ?_⟩
  intro M N f
  apply HomologicalComplex.hom_ext
  intro n
  exact homComplex_unit_evaluation_naturality J R f n

end CategoryTheory

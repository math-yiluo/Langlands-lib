/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.ProEtale.FiniteCoefficientCohomology
public import WeilConjectures.CategoryTheory.Sites.CohomologyDerivedEvaluationAll

/-!
# Pro-étale and étale cohomology with finite discrete coefficients

For a discrete abelian group `A`, the pro-étale cohomology of `continuousSheaf S A : U ↦ C(U, A)`
is the étale cohomology of the constant sheaf `A`, in every degree
(`AlgebraicGeometry.ProEtale.nonempty_addEquiv_H_continuousSheaf`): the sheaf `U ↦ C(U, A)` is the
constant pro-étale sheaf, which is `ν^*` of the constant étale sheaf, and
`RΓ(S_proét, ν^* M) ≅ RΓ(S_ét, M)`.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite

namespace AlgebraicGeometry.ProEtale

open Scheme

/-- **Pro-étale cohomology of a constant discrete sheaf is étale cohomology.** For a discrete
abelian group `A`, `Hⁿ(S_proét, C(-, A)) ≅ Hⁿ(S_ét, A)`. -/
theorem nonempty_addEquiv_H_continuousSheaf (S : Scheme.{u}) (A : Type) [TopologicalSpace A]
    [DiscreteTopology A] [AddCommGroup A] [IsTopologicalAddGroup A] (n : ℕ) :
    Nonempty (Sheaf.H (continuousSheaf S A) n ≃+
      Sheaf.H ((constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} A))) n) := by
  let M := AddCommGrpCat.of (ULift.{u + 1} A)
  let Cet := (constantSheaf S.smallEtaleTopology AddCommGrpCat.{u + 1}).obj M
  let Cproet := (constantSheaf (ProEt.topology S) AddCommGrpCat.{u + 1}).obj M
  obtain ⟨e₁⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation
    (ProEt.topology S) _ (ProEt.isTerminalMkId S) Cproet n
  obtain ⟨e₂⟩ := Sheaf.cohomology_nonempty_addEquiv_rightDerived_evaluation
    S.smallEtaleTopology _ (Etale.isTerminalMkId S) Cet n
  let e₃ : ((globalSectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived n).obj Cproet ≅
      ((Etale.sectionsFunctor AddCommGrpCat.{u + 1} S).rightDerived n).obj Cet :=
    (((globalSectionsFunctor _ S).rightDerived n).mapIso
      ((comparisonUpperStarConstantSheafIsoAddCommGrpCat S).app M)).symm ≪≫
      rightDerivedGlobalSectionsFunctorComparisonUpperStarObjIso _ S Cet n
  let e₄ := (Sheaf.functorH (ProEt.topology S) n).mapIso (constantSheafIsoContinuousSheaf S A)
  exact ⟨e₄.addCommGroupIsoToAddEquiv.symm.trans
    (e₁.trans (e₃.addCommGroupIsoToAddEquiv.trans e₂.symm))⟩

end AlgebraicGeometry.ProEtale

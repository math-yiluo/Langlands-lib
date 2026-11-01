import Langlands.Algebra.NonUnitalModuleEnoughInjectivesStatements
import Langlands.Algebra.NonUnitalModuleDualHomTransposeProof
import Langlands.Algebra.NonUnitalModuleDualRightExactnessProof
import Langlands.Algebra.NonUnitalModuleProjectivityProof
import Langlands.Algebra.NonUnitalModuleBidualInjectionProof
import Langlands.CategoryTheory.Renard.HomExactnessComparison

/-! Actual injective presentations in Renard I.5.2. -/

set_option autoImplicit false

noncomputable section

open CategoryTheory

namespace Langlands.Algebra.NonUnitalModuleInjectivityProof

open NonUnitalModuleDual NonUnitalModuleDualHomTranspose

universe uA uM

variable {A : Type uA} [NonUnitalRing A] [Module ℂ A]
  [IsScalarTower ℂ A A] [SMulCommClass ℂ A A]

/-- Extend into the actual right dual by lifting the transposed original map. -/
theorem dualObject_injective (hA : IsIdempotented A)
    (P : NondegenerateModuleCat.{uA, uM} A) [Projective P] :
    CategoryTheory.Injective (dualObject hA P) := by
  constructor
  intro X Y g f hf
  let t : P ⟶ rightDualObject hA X :=
    ObjectProperty.homMk (transpose hA X.property P.property g.hom)
  let d : rightDualObject hA Y ⟶ rightDualObject hA X :=
    (rightToLeftFunctor hA).map f.op
  let : Epi d := rightToLeft_epi_of_mono hA f hf
  let l : P ⟶ rightDualObject hA Y := Projective.factorThru t d
  refine ⟨ObjectProperty.homMk
    (NonUnitalModuleDualHomTranspose.reverse hA Y.property P.property l.hom), ?_⟩
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro x
  apply dual_ext hA P.property
  intro p
  exact congrArg
    (fun k : P ⟶ rightDualObject hA X => (k.hom.toAddMonoidHom p).val x)
    (Projective.factorThru_comp t d)

/-- The reverse orientation retains the specified transported left dual action. -/
theorem rightDualObject_injective (hA : IsIdempotented A)
    (P : RightNondegenerateModuleCat.{uA, uM} A) [Projective P] :
    CategoryTheory.Injective (rightDualObject hA P) := by
  constructor
  intro X Y g f hf
  let t : P ⟶ dualObject hA X :=
    ObjectProperty.homMk
      (NonUnitalModuleDualHomTranspose.reverse hA P.property X.property g.hom)
  let d : dualObject hA Y ⟶ dualObject hA X :=
    (leftToRightFunctor hA).map f.op
  let : Epi d := leftToRight_epi_of_mono hA f hf
  let l : P ⟶ dualObject hA Y := Projective.factorThru t d
  refine ⟨ObjectProperty.homMk (transpose hA P.property Y.property l.hom), ?_⟩
  apply ObjectProperty.hom_ext
  apply NonUnitalModuleHom.ext
  intro x
  apply dual_ext hA.op P.property
  intro p
  exact congrArg
    (fun k : P ⟶ dualObject hA X => (k.hom.toAddMonoidHom p).val x)
    (Projective.factorThru_comp t d)

/-- The exact source-Hom statement follows from the published comparison. -/
theorem dualProjectivity :
    NonUnitalModuleEnoughInjectives.DualProjectivityStatement.{uA, uM} := by
  intro A _ _ _ _ hA
  let := NondegenerateModuleCat.abelian.{uA, uM} A hA
  let := NondegenerateModuleCat.abelian.{uA, uM} Aᵐᵒᵖ hA.op
  constructor
  · intro P hP
    let : Projective P := (Langlands.Renard.homProjectiveComparison P).mp hP
    exact (Langlands.Renard.homInjectiveComparison _).mpr (dualObject_injective hA P)
  · intro P hP
    let : Projective P := (Langlands.Renard.homProjectiveComparison P).mp hP
    exact (Langlands.Renard.homInjectiveComparison _).mpr (rightDualObject_injective hA P)

/-- Dualize a projective presentation of the actual right dual and insert evaluation. -/
def leftPresentation (hA : IsIdempotented A)
    (M : NondegenerateModuleCat.{uA, max uA uM} A) : InjectivePresentation M := by
  let P := NonUnitalModuleProjectivityProof.presentation.{uA, uM} hA.op (dualObject hA M)
  refine
    { J := rightDualObject hA P.p
      injective := rightDualObject_injective hA P.p
      f := (evaluationNatTrans hA).app M ≫ (rightToLeftFunctor hA).map P.f.op
      mono := ?_ }
  exact mono_comp'
    ((NonUnitalModuleBidualInjectionProof.evaluationMonomorphisms hA).1 M)
    (rightToLeft_mono_of_epi hA P.f P.epi)

/-- The right presentation retains the actual transported left dual and right evaluation. -/
def rightPresentation (hA : IsIdempotented A)
    (M : RightNondegenerateModuleCat.{uA, max uA uM} A) : InjectivePresentation M := by
  let P := NonUnitalModuleProjectivityProof.presentation.{uA, uM} hA (rightDualObject hA M)
  refine
    { J := dualObject hA P.p
      injective := dualObject_injective hA P.p
      f := (NonUnitalModuleRightBidual.rightEvaluationNatTrans hA).app M ≫
        (leftToRightFunctor hA).map P.f.op
      mono := ?_ }
  exact mono_comp'
    ((NonUnitalModuleBidualInjectionProof.evaluationMonomorphisms hA).2 M)
    (leftToRight_mono_of_epi hA P.f P.epi)

/-- Every original module on either side has the constructed injective presentation. -/
theorem enoughInjectives :
    NonUnitalModuleEnoughInjectives.EnoughInjectivesStatement.{uA, uM} := by
  intro A _ _ _ _ hA
  exact ⟨⟨fun M => ⟨leftPresentation hA M⟩⟩,
    ⟨fun M => ⟨rightPresentation hA M⟩⟩⟩

/-- The presentations expose the original injective additive maps as well. -/
theorem injectiveEmbedding :
    NonUnitalModuleEnoughInjectives.InjectiveEmbeddingStatement.{uA, uM} := by
  intro A _ _ _ _ hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} A hA
  let := NondegenerateModuleCat.abelian.{uA, max uA uM} Aᵐᵒᵖ hA.op
  constructor
  · intro M
    let J := leftPresentation hA M
    exact ⟨J.J, J.f,
      (Langlands.Renard.homInjectiveComparison J.J).mpr J.injective,
      J.mono, (NondegenerateModuleExactnessConcrete.mono_iff hA J.f).mp J.mono⟩
  · intro M
    let J := rightPresentation hA M
    exact ⟨J.J, J.f,
      (Langlands.Renard.homInjectiveComparison J.J).mpr J.injective,
      J.mono, (NondegenerateModuleExactnessConcrete.mono_iff hA.op J.f).mp J.mono⟩

/-- The dual-projective lemma, enough injectives, and both original embeddings. -/
theorem injectivityAssertions :
    NonUnitalModuleEnoughInjectives.InjectivityAssertions.{uA, uM} :=
  ⟨dualProjectivity, enoughInjectives, injectiveEmbedding⟩

example : NonUnitalModuleEnoughInjectives.InjectivityAssertions.{uA, uM} :=
  injectivityAssertions.{uA, uM}
example : NonUnitalModuleEnoughInjectives.InjectivityAssertions.{0, 1} :=
  injectivityAssertions.{0, 1}
example : NonUnitalModuleEnoughInjectives.InjectivityAssertions.{1, 0} :=
  injectivityAssertions.{1, 0}

end Langlands.Algebra.NonUnitalModuleInjectivityProof

import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreCriterionStatement
import Mathlib.AlgebraicGeometry.Stalk

/-! # The steps of Murre's proof of the criterion for unramified functors

Statements of the three steps into which Murre's outline (Bourbaki exp. 294, Section 2)
splits the proof of `MurreCriterionStatement`: stability of the conditions under base
change, the local-to-global Proposition 2, and the local step (Steps 1, 2a, 2b of Case I)
under the induction hypothesis on the dimension. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

variable {S : Scheme.{u}}

/-- The ten conditions in the hypotheses of `MurreCriterionStatement`: `SmallValues`,
(F1a), (F1b), (F2), (F3), (F4′), strong (F5), (F6), (F7) and (F8). -/
def MurreConditions (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  SmallValues F ∧ ZariskiSheaf F ∧ FaithfullyFlatSheaf F ∧ FilteredColimits F ∧
    AdicLimits F ∧ ArtinianLifting F ∧ NilpotentInjective F ∧ ValuativeSeparation F ∧
    OneDimensionalLifting F ∧ GenericNonLifting F

/-- The conclusion of `MurreCriterionStatement`: `F` is represented by a scheme that is
separated, locally of finite type and formally unramified over `S`. -/
def UnramifiedRepresentable (F : (Over S)ᵒᵖ ⥤ Type v) : Prop :=
  ∃ (Y : Scheme.{u}) (q : Y ⟶ S),
    Nonempty (F.RepresentableBy (Over.mk q)) ∧
      IsSeparated q ∧ LocallyOfFiniteType q ∧ FormallyUnramified q

/-- The base change `F ×_S S'` of a presheaf `F` on `Over S` along `g : S' ⟶ S`: the
presheaf on `Over S'` sending `T' ⟶ S'` to `F(T' ⟶ S' ⟶ S)`. -/
def baseChange {S' : Scheme.{u}} (g : S' ⟶ S) (F : (Over S)ᵒᵖ ⥤ Type v) :
    (Over S')ᵒᵖ ⥤ Type v :=
  (Over.map g).op ⋙ F

/-- Murre, Section 2, first sentence: the conditions are stable under base change. For
every morphism of schemes `g : S' ⟶ S` and every presheaf `F` on `Over S` satisfying the
conditions, the base change `F ×_S S'` satisfies them. -/
def MurreBaseChangeStatement : Prop :=
  ∀ (S S' : Scheme.{u}) (g : S' ⟶ S) (F : (Over S)ᵒᵖ ⥤ Type v),
    MurreConditions F → MurreConditions (baseChange g F)

/-- Murre's Proposition 2: over a locally noetherian `S`, a presheaf `F` satisfying the
conditions whose base change to `Spec 𝒪_{S,s}` is representable (by a separated,
locally of finite type, formally unramified scheme) for every point `s` is itself
representable by such a scheme. -/
def MurreLocalToGlobalStatement : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ Type v),
    MurreConditions F →
      (∀ s : S, UnramifiedRepresentable (baseChange (S.fromSpecStalk s) F)) →
        UnramifiedRepresentable F

/-- The criterion over locally noetherian bases all of whose local rings have Krull
dimension `< n`. -/
def MurreDimensionBound (n : ℕ) : Prop :=
  ∀ (S : Scheme.{u}) [IsLocallyNoetherian S] (F : (Over S)ᵒᵖ ⥤ Type v),
    MurreConditions F → (∀ s : S, ringKrullDim (S.presheaf.stalk s) < n) →
      UnramifiedRepresentable F

/-- The local step of Murre's induction (Steps 1, 2a and 2b of Case I): if the criterion
holds over locally noetherian bases whose local rings have dimension `< n`, it holds over
`Spec R` for every local noetherian ring `R` of Krull dimension `n`. -/
def MurreLocalStepStatement : Prop :=
  ∀ n : ℕ, MurreDimensionBound.{u, v} n →
    ∀ (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R], ringKrullDim R = n →
      ∀ F : (Over (Spec R))ᵒᵖ ⥤ Type v, MurreConditions F → UnramifiedRepresentable F

/-- The three steps of Murre's proof together. -/
def MurreProofStepsStatement : Prop :=
  MurreBaseChangeStatement.{u, v} ∧ MurreLocalToGlobalStatement.{u, v} ∧
    MurreLocalStepStatement.{u, v}

end Langlands.AlgebraicGeometry.UnramifiedFunctor

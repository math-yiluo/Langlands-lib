import Langlands.AlgebraicGeometry.UnramifiedFunctor.MurreProofSteps
import Mathlib.RingTheory.AdicCompletion.Algebra
import Mathlib.RingTheory.QuasiFinite.Basic

/-! # The parts of the local step of Murre's induction

Statements of Murre's Lemma 1 and of Steps 1, 2a and 2b of Case I of Murre's outline
(Bourbaki exp. 294, Section 2), into which `MurreLocalStepStatement` is split. Steps 2a and 2b
take as hypotheses the representability results that the induction hypothesis supplies. -/

universe u v

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite IsLocalRing

noncomputable section

namespace Langlands.AlgebraicGeometry.UnramifiedFunctor

/-- The punctured spectrum of a local ring `R`: the open subset of `Spec R` complementary to
the closed point. -/
def puncturedSpectrum (R : CommRingCat.{u}) [IsLocalRing R] : (Spec R).Opens :=
  ⟨{closedPoint R}ᶜ, (isClosed_singleton_closedPoint R).isOpen_compl⟩

/-- The closed immersion `Spec (R/m^(k+1)) ⟶ Spec R` for a local ring `R` with maximal
ideal `m`. -/
def maximalIdealPowQuotientMap (R : CommRingCat.{u}) [IsLocalRing R] (k : ℕ) :
    Spec (CommRingCat.of (R ⧸ maximalIdeal R ^ (k + 1))) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal R ^ (k + 1))))

/-- The morphism `Spec R̂ ⟶ Spec R` from the spectrum of the completion `R̂` of a local ring
`R` with respect to its maximal ideal. -/
def completionMap (R : CommRingCat.{u}) [IsLocalRing R] :
    Spec (CommRingCat.of (AdicCompletion (maximalIdeal R) R)) ⟶ Spec R :=
  Spec.map (CommRingCat.ofHom (algebraMap R (AdicCompletion (maximalIdeal R) R)))

/-- Murre's Lemma 1, for a represented source: let `A` be a noetherian ring and let
`F : (Over (Spec A))ᵒᵖ ⥤ Type v` satisfy (F1a), (F1b), (F2) and (F3). Let `q : Y ⟶ Spec A`
be locally of finite type and `ξ ∈ F(Y)`. If `g ↦ F(g)(ξ)` is bijective on `Spec B` for every
local artinian `A`-algebra `B` whose residue field is finite over the residue field of its
image point in `Spec A` (equivalently, `B` quasi-finite over `A`), then it is bijective on
every test object `T`, that is, `ξ` exhibits `Y` as representing `F`. -/
def MurreArtinianDetectionStatement : Prop :=
  ∀ (A : CommRingCat.{u}) [IsNoetherianRing A] (F : (Over (Spec A))ᵒᵖ ⥤ Type v),
    ZariskiSheaf F → FaithfullyFlatSheaf F → FilteredColimits F → AdicLimits F →
    ∀ (Y : Scheme.{u}) (q : Y ⟶ Spec A), LocallyOfFiniteType q →
    ∀ ξ : F.obj (op (Over.mk q)),
      (∀ (B : Type u) [CommRing B] [Algebra A B] [IsLocalRing B] [IsArtinianRing B]
          [Algebra.QuasiFinite A B],
        Function.Bijective fun g : algebraOver (𝟙 (Spec A)) B ⟶ Over.mk q ↦ F.map g.op ξ) →
      ∀ T : Over (Spec A), Function.Bijective fun g : T ⟶ Over.mk q ↦ F.map g.op ξ

/-- Step 1 of Murre's Case I: over the spectrum of a local artinian ring, a presheaf
satisfying the conditions is represented by a separated, locally of finite type, formally
unramified scheme. -/
def MurreArtinianBaseStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsLocalRing R] [IsArtinianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F → UnramifiedRepresentable F

/-- Step 2a of Murre's Case I: let `R` be a complete local noetherian ring and let `F`
satisfy the conditions. If the base change of `F` to the punctured spectrum of `R` and its
base changes to `Spec (R/m^(k+1))` for all `k` are represented by separated, locally of
finite type, formally unramified schemes, then so is `F`. -/
def MurreCompleteLocalStepStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R]
    [IsAdicComplete (maximalIdeal R) R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F) →
    (∀ k : ℕ, UnramifiedRepresentable (baseChange (maximalIdealPowQuotientMap R k) F)) →
    UnramifiedRepresentable F

/-- Step 2b of Murre's Case I: let `R` be a local noetherian ring and let `F` satisfy the
conditions. If the base changes of `F` to the punctured spectrum of `R` and to the spectrum
of the completion `R̂` are represented by separated, locally of finite type, formally
unramified schemes, then so is `F`. -/
def MurreCompletionDescentStatement : Prop :=
  ∀ (R : CommRingCat.{u}) [IsLocalRing R] [IsNoetherianRing R] (F : (Over (Spec R))ᵒᵖ ⥤ Type v),
    MurreConditions F →
    UnramifiedRepresentable (baseChange (puncturedSpectrum R).ι F) →
    UnramifiedRepresentable (baseChange (completionMap R) F) →
    UnramifiedRepresentable F

/-- Steps 1, 2a and 2b of Murre's Case I together. -/
def MurreLocalStepPartsStatement : Prop :=
  MurreArtinianBaseStatement.{u, v} ∧ MurreCompleteLocalStepStatement.{u, v} ∧
    MurreCompletionDescentStatement.{u, v}

end Langlands.AlgebraicGeometry.UnramifiedFunctor

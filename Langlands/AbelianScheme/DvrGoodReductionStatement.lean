import Langlands.AbelianScheme.Tate.PrimeMonodromy
import Langlands.AlgebraicGeometry.FiniteEtale.GeometricFiberFiniteProof
import Langlands.AlgebraicGeometry.FiniteEtale.Pullback
import Mathlib.RingTheory.DiscreteValuationRing.Basic

/-! # Good reduction over a discrete valuation ring from prime Tate monodromy -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Langlands.AlgebraicGeometry.FiniteEtale

namespace Langlands.AbelianScheme

/-- In residue characteristic zero, trivial rational prime Tate monodromy on
the kernel of generic-to-total restriction implies good reduction over the
given DVR. -/
def DvrGoodReductionStatement (htor : TorsionFiniteEtaleStatement.{u}) : Prop :=
  ∀ (V K : Type u) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    [CharZero (IsLocalRing.ResidueField V)] [Field K] [Algebra V K] [IsFractionRing V K]
    (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of K)) (B : AbelianScheme (Spec (.of K)))
    (p : ℕ) [Fact p.Prime]
    (hu : ∀ n : ℕ, IsUnit ((p ^ n : ℕ) : Γ(Spec (.of K), ⊤))),
    let j := Spec.map (CommRingCat.ofHom (algebraMap V K))
    let t := s ≫ j
    let hs := geometricFiberFinite s
    let ht := geometricFiberFinite t
    (∀ g : FundamentalGroup s hs, fundamentalGroupMap j s t rfl hs ht g = 1 →
      Tate.PrimeAdic.rationalMonodromyRepresentation s hs htor B p hu g = 1) →
    ∃ B₀ : AbelianScheme (Spec (.of V)), Nonempty ((baseChange j).obj B₀ ≅ B)

end Langlands.AbelianScheme

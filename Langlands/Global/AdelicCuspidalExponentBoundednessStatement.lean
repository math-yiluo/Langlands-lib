import Langlands.Global.AdelicCuspidalExponentNonexistenceStatement

/-! # Boundedness of a form with only negative maximal cuspidal exponents
(Mœglin–Waldspurger I.4.1, as used by Bernstein–Lapid in §6.4) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The first step of the proof of the lemma of §6.4 of Bernstein–Lapid, for automorphic
functions on `U_R(𝔸) M_R(F) \ G(𝔸)`: under the hypotheses of
`CuspidalExponentNonexistenceStatement` (every cuspidal exponent `(Q, μ)` of `f` has `Q` maximal
in `R` and `⟨Re μ, β^∨⟩ < 0`), every right translate of every constant term `C_Q f`, `Q ⊆ R`, is
bounded on `M_R(𝔸)^1`. The source deduces this from the growth bound of Mœglin–Waldspurger
I.4.1. -/
def CuspidalExponentBoundednessStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (K : Subgroup (AdelicGroupPoints F G)),
    IsMaximalCompactSubgroup F G K →
    IsIwasawaCompact (fam.p ⟨∅, Set.empty_subset _⟩) K →
    (∀ J : StandardIndex F G fam.i fam.ν,
      IsMaximalCompactSubgroup F (fam.M J)
        (K.comap (AdelicGroupPoints.map F (fam.M J) G (fam.l J ≫ fam.p J)).toMonoidHom)) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      IsClosedSubgroup rho →
      let Kinf := K.comap (ofInfinite F G).toMonoidHom
      ∀ (R : StandardIndex F G fam.i fam.ν) (f : AdelicGroupPoints F G → ℂ),
        fam.IsAutomorphicOn hsmooth Kinf rho R f →
      ∀ (φc : StandardIndex F G fam.i fam.ν → AdelicGroupPoints F G → ℂ)
        (s : ∀ Q : StandardIndex F G fam.i fam.ν, Finset (ComplexCharacterParameter F (fam.P Q)))
        (c : ∀ Q : StandardIndex F G fam.i fam.ν,
          ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
        fam.IsRelativeCuspidalExponentFamily hsmooth Kinf rho R f φc s c →
        (∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R → ∀ mu ∈ s Q, c Q mu ≠ 0 →
          ∃ β : relativeRoots fam.i, β.1 ∉ Q.1 ∧ insert β.1 Q.1 = R.1 ∧
            RealTorusSpace.pair fam.T (fam.realExponent Q mu)
              ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot β) < 0) →
        ∀ Q : StandardIndex F G fam.i fam.ν, Q ≤ R → ∀ g : AdelicGroupPoints F G,
          ∃ C : ℝ, ∀ m ∈ normOneSubgroup F (fam.M R),
            ‖fam.constantTerm Q f (map F (fam.M R) G (fam.l R ≫ fam.p R) m * g)‖ ≤ C

end Langlands.Global

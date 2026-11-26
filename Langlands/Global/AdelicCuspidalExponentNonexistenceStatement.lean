import Langlands.Global.AdelicCuspidalExponentAscentStatement

/-! # Nonexistence of a nonzero form with only negative maximal cuspidal exponents
(Bernstein–Lapid, the lemma of §6.4) -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

namespace StandardParabolicFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (𝓕 : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G 𝓕.i 𝓕.ν

/-- For a function `f` on `U_R(𝔸) M_R(F) \ G(𝔸)`: along every standard parabolic `Q ⊆ R`,
`φc Q` is a cuspidal projection of the constant term `C_Q f` and `(s Q, c Q)` is an
unnormalized exponent decomposition of it. Nothing is required along `Q ⊄ R`. -/
def IsRelativeCuspidalExponentFamily {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (R : Idx) (f : AdelicGroupPoints F G → ℂ) (φc : Idx → AdelicGroupPoints F G → ℂ)
    (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ Q : Idx, Q ≤ R → 𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q f) (φc Q) ∧
    𝓕.IsExponentDecomposition hsmooth Kinf rho Q (φc Q) (s Q) (c Q)

end StandardParabolicFamily

/-- Bernstein–Lapid, the lemma of §6.4, for automorphic functions on `U_R(𝔸) M_R(F) \ G(𝔸)`.
Let `f` be such a function and fix cuspidal projections and exponent decompositions of its
constant terms along the standard parabolics `Q ⊆ R`. Assume that every cuspidal exponent
`(Q, μ)` of `f` (a nonzero component along some `Q ⊆ R`) has `Q` maximal in `R`, that is,
`Δ_0^R = Δ_0^Q ∪ {β}` for a simple root `β ∉ Δ_0^Q`, and `⟨Re μ, β^∨⟩ < 0`. Then `f = 0`.
For `R = G` this is the lemma as stated in the source; for general `R` it is the lemma for the
Levi `M_R`, applied to the restrictions `m ↦ f(m k)`. -/
def CuspidalExponentNonexistenceStatement : Prop :=
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
        f = 0

end Langlands.Global

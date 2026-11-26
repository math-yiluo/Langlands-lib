import Langlands.Global.AdelicLeadingCuspidalComponents

/-! # Ascent of a cuspidal exponent through a simple root (Bernstein–Lapid, Corollary 6.4) -/

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

/-- Along every standard parabolic `Q`, `φc Q` is a cuspidal projection of the constant
term `C_Q φ` and `(s Q, c Q)` is an unnormalized exponent decomposition of it. -/
def IsCuspidalExponentFamily {d N : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (Kinf : Subgroup (InfiniteAdelicGroupPoints F G)) (rho : MatrixRepresentation G (Fin N))
    (φ : AdelicGroupPoints F G → ℂ) (φc : Idx → AdelicGroupPoints F G → ℂ)
    (s : ∀ Q : Idx, Finset (ComplexCharacterParameter F (𝓕.P Q)))
    (c : ∀ Q : Idx, ComplexCharacterParameter F (𝓕.P Q) → AdelicGroupPoints F G → ℂ) : Prop :=
  ∀ Q : Idx, 𝓕.IsCuspidalProjection hsmooth Kinf rho Q (𝓕.constantTerm Q φ) (φc Q) ∧
    𝓕.IsExponentDecomposition hsmooth Kinf rho Q (φc Q) (s Q) (c Q)

/-- The image `Re λ ∈ 𝔞_0^*` of the real part of a parameter `λ ∈ 𝔛_Q`. -/
abbrev realExponent (Q : Idx) (lam : ComplexCharacterParameter F (𝓕.P Q)) :
    RealTorusSpace.Vstar 𝓕.T :=
  𝓕.chamberEmbedding Q (parameterRealPart F (𝓕.P Q) lam)

/-- The real span `(𝔞_0^R)^*` in `𝔞_0^*` of a set `R` of simple roots. -/
def rootSpanReal (R : Set (characterLattice 𝓕.T)) : Submodule ℝ (RealTorusSpace.Vstar 𝓕.T) :=
  Submodule.span ℝ ((fun x : characterLattice 𝓕.T => (1 : ℝ) ⊗ₜ[ℤ] x) '' R)

end StandardParabolicFamily

/-- Bernstein–Lapid, Corollary 6.4, for a chosen family of cuspidal projections and exponent
decompositions of the constant terms of an automorphic form `φ` on `G(F) \ G(𝔸)`. Let `λ` be a
cuspidal exponent of `φ` along `P` (a nonzero component of the decomposition along `P`) such
that no standard parabolic of smaller semisimple rank carries a cuspidal exponent, and let
`α` be a simple root outside `P` with `⟨Re λ, α^∨⟩ < 0`. Then some standard `Q` which is a
maximal parabolic of `P_α` (the simple roots of `Q` together with one further simple root `β`
are those of `P` together with `α`) carries a cuspidal exponent `μ` with
`⟨Re μ, β^∨⟩ ≥ 0` and `(Re μ)_{P_α} = (Re λ)_{P_α}`, that is, `Re λ - Re μ` lies in the real
span of the simple roots of `P_α`. -/
def CuspidalExponentAscentStatement : Prop :=
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
      ∀ φ : AdelicGroupPoints F G → ℂ,
        IsAutomorphicFunctionOn F G hsmooth (adelicDifferentialCommutator_of_smooth F G hsmooth)
          (rationalSubgroup F G) Kinf rho φ →
      ∀ (φc : StandardIndex F G fam.i fam.ν → AdelicGroupPoints F G → ℂ)
        (s : ∀ Q : StandardIndex F G fam.i fam.ν, Finset (ComplexCharacterParameter F (fam.P Q)))
        (c : ∀ Q : StandardIndex F G fam.i fam.ν,
          ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
        fam.IsCuspidalExponentFamily hsmooth Kinf rho φ φc s c →
      ∀ (P : StandardIndex F G fam.i fam.ν) (lam : ComplexCharacterParameter F (fam.P P)),
        lam ∈ s P → c P lam ≠ 0 →
        (∀ Q : StandardIndex F G fam.i fam.ν, Q.1.ncard < P.1.ncard → ∀ mu ∈ s Q, c Q mu = 0) →
      ∀ α : relativeRoots fam.i, α.1 ∈ simpleRelativeRoots fam.i fam.ν → α.1 ∉ P.1 →
        RealTorusSpace.pair fam.T (fam.realExponent P lam)
          ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot α) < 0 →
      ∃ (Q : StandardIndex F G fam.i fam.ν) (β : relativeRoots fam.i),
        β.1 ∉ Q.1 ∧ insert β.1 Q.1 = insert α.1 P.1 ∧
        ∃ mu ∈ s Q, c Q mu ≠ 0 ∧
          0 ≤ RealTorusSpace.pair fam.T (fam.realExponent Q mu)
            ((1 : ℝ) ⊗ₜ[ℤ] fam.coroots.coroot β) ∧
          fam.realExponent P lam - fam.realExponent Q mu ∈ fam.rootSpanReal (insert α.1 P.1)

end Langlands.Global

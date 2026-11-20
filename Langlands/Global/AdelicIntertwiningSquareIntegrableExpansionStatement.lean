import Langlands.Global.AdelicIntertwiningContinuationStatement
import Langlands.Global.AdelicSquareIntegrableInducedForms

/-! # Intertwining operators on `A^2_P` have finite expansions in `A^2_Q`

Lapid 2011, §2, p.312 (Working hypothesis, a consequence of Langlands' theory): for
`φ ∈ A^2_P` and `w ∈ Ω(P, Q)`, `λ ↦ M(w, λ)φ` is meromorphic with values in a finite-dimensional
subspace of `A^2_Q` determined by the `K`- and `𝔷`-types of `φ`. In a spanning family `ψ i` of
that subspace, `M(w, λ)φ = ∑ i, coeff i λ • ψ i` with scalar coefficients meromorphic in linear
coordinates. Since `M(w, λ)` is unitary, hence holomorphic, for `λ ∈ i𝔞_P^*` (Lapid, loc. cit.;
Mœglin–Waldspurger IV.3.12), the coefficients may be chosen holomorphic near `i𝔞_P^*`.

Lapid states the hypothesis for standard parabolics and one maximal compact `K` in good position
with respect to a minimal Levi. The proposition below assumes it for all presented parabolics and
every maximal compact `K` with the Iwasawa decompositions; this extension is an assumption of the
premise, not a result of the source (see the paired Markdown). -/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- Finite expansions of `M(w, λ)φ` in `A^2_Q` (Lapid 2011, §2, p.312, Working hypothesis).
Let `P = MU` and `Q = M'V` be parabolics of a connected reductive `G` over a number field, with
presentations `r`, `r'`, a Levi projection `π'` of `Q`, a Weyl conjugation `(w, c)` from `P` to
`Q`, and `K` maximal compact with `P(𝔸)K = Q(𝔸)K = G(𝔸)`. For every `φ ∈ A^2_P` there are
finitely many `ψ i ∈ A^2_Q` and scalar functions `coeff i` on `X^*(P) ⊗ ℂ`, meromorphic in linear
coordinates with one domain of holomorphy `D` containing `i(X^*(P) ⊗ ℝ)`, such that
`M(w, λ)φ = ∑ i, coeff i λ • ψ i` for `Re λ` sufficiently regular. -/
def IntertwiningSquareIntegrableExpansionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F)))
    (A A' : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
    [IsAffine Q.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
    [IsAffine V.X.left]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    [IsClosedImmersion (iU ≫ p).hom.hom.left]
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (q : Q ⟶ G) [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
    [IsClosedImmersion (iV ≫ q).hom.hom.left]
    (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation q l' a') (π' : Q ⟶ M')
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    haveI : LocallyOfFiniteType Q.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := q) ‹IsClosedImmersion q.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    LeviSubgroup.IsGeometricUnipotentRadical iV → IsIso (subgroupMultiplication l' iV) →
    l' ≫ π' = 𝟙 M' → IsWeylConjugation p l q l' w c →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K)
      (hK' : IsIwasawaCompact q K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ →
      ∃ (k : ℕ) (ψ : Fin k → AdelicGroupPoints F G → ℂ)
        (coeff : Fin k → ComplexCharacterParameter F P → ℂ)
        (D : Set (ComplexCharacterParameter F P)),
        (∀ i, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc q iV l' (ψ i)) ∧
        Set.range (imaginaryParameter F P) ⊆ D ∧
        (∀ i, IsMeromorphicInCoordinatesOn (coeff i) D) ∧
        ∃ R₀ : ℝ, ∀ lam : ComplexCharacterParameter F P, r.IsRegularParameter hA hT R₀ lam →
          ∀ g : AdelicGroupPoints F G,
            hK.intertwiningOperator hK' iU l iV c π' w φ lam g = ∑ i, coeff i lam * ψ i g

end Langlands.Global

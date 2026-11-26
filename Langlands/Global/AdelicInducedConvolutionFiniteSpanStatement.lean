import Langlands.Global.AdelicEisensteinConvolutionIdentity
import Langlands.Global.AdelicWavePacketTranslationReduction

/-! # Finite span of the integrated induced action on `A^2_P`

`InducedConvolutionFiniteSpanStatement`: for `v ∈ A^2_P` and a test function `φ` of
`IsLeftFiniteTestFunction`, the functions `I(λ, φ) v`, `λ ∈ X^*(P) ⊗ ℂ`, lie in the span of
finitely many elements of `A^2_P`, with coefficients entire in `λ` (Mœglin–Waldspurger I.2.17,
the finiteness theorem, and IV.1.7 (*); Arthur 2005, §7, pp.33–34). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-- **Finite span of the integrated induced action** (Mœglin–Waldspurger I.2.17 and IV.1.7 (*);
Arthur 2005, §7, pp.33–34). Let `P = M U` be a parabolic of a connected reductive `G` over a
number field, with geometric unipotent radical `iU`, rational Levi `l` and a presentation `r` of
its split component, let `K` be a maximal compact subgroup with `P(𝔸) K = G(𝔸)` which is in Iwasawa
position for some minimal parabolic, and let `rho` be a closed matrix embedding. For every
`v ∈ A^2_P` and every continuous, compactly supported, left `K_∞`-finite and left
`G(𝔸_f)`-smooth `φ`, there are finitely many `w i ∈ A^2_P` and functions `b i` on `X^*(P) ⊗ ℂ`,
holomorphic in linear coordinates on the whole space, such that
`I(λ, φ) v = ∑ i, b i λ • w i` for every `λ`, where
`I(λ, φ) v (x) = ∫ φ(h) e^{-⟨λ, H_P(x)⟩} v(x h) e^{⟨λ, H_P(x h)⟩} dh`. -/
def InducedConvolutionFiniteSpanStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F]
    (G P M U : GroupScheme (Spec (CommRingCat.of F)))
    (A : CommGroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
    (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
    (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (_hA : IsSplitTorus A.toGrp) (_hT : IsSplitTorus r.data.T.toGrp),
    haveI : LocallyOfFiniteType P.X.hom :=
      IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
    IsConnectedReductive G → LeviSubgroup.IsGeometricUnipotentRadical iU →
    ∀ (K : Subgroup (AdelicGroupPoints F G)) (hK : IsIwasawaCompact p K) {N d : ℕ}
      (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth),
      IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
      (∃ (P₀ : GroupScheme (Spec (CommRingCat.of F))) (_ : IsAffine P₀.X.left) (p₀ : P₀ ⟶ G)
        (_ : IsClosedImmersion p₀.hom.hom.left),
        IsMinimalParabolicSubgroup p₀ ∧ IsIwasawaCompact p₀ K) →
    ∀ v : AdelicGroupPoints F G → ℂ,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v →
    ∀ φ : AdelicGroupPoints F G → ℂ,
      IsLeftFiniteTestFunction F G (K.comap (ofInfinite F G).toMonoidHom) φ →
      ∃ (m : ℕ) (w : Fin m → AdelicGroupPoints F G → ℂ)
        (b : Fin m → ComplexCharacterParameter F P → ℂ),
        (∀ i, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (w i)) ∧
        (∀ i, IsHolomorphicInCoordinatesOn (b i) Set.univ) ∧
        ∀ lam : ComplexCharacterParameter F P,
          hK.inducedConvolution lam φ v = fun x => ∑ i, b i lam * w i x

end Langlands.Global

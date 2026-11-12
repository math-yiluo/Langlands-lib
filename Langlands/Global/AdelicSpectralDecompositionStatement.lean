import Langlands.Global.AdelicParabolicSpectrum
import Langlands.Global.AdelicIntertwiningOperator
import Langlands.GroupScheme.Dynamic.RepresentedStructure

/-! # Langlands' spectral decomposition of `L²([G])`

Getz–Hahn Theorem 10.5.1 (Arthur 2005, Theorem 7.2(b) and (7.5)): `L²([G])`,
`[G] = A_G G(F) \ G(𝔸)`, is the orthogonal direct sum, over the finitely many association
classes `𝒫` of parabolic subgroups, of the closed subspaces `L²_𝒫([G])` spanned by wave packets
of Eisenstein series; the class of `G` itself contributes `L²_disc([G])`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- Langlands' spectral decomposition (Getz–Hahn Theorem 10.5.1). Let `G` be connected reductive
over a number field, `K` a maximal compact subgroup of `G(𝔸)` and `P₀` a minimal parabolic with
`P₀(𝔸)K = G(𝔸)`. For a standard parabolic `P = MU ⊇ P₀` with presentation `r` and unipotent
radical `U`, let `L²_P([G])` be `parabolicSpectrum`, the closed span of the wave packets of `P`
over `i(𝔞_M^G)^*`. Then:
* only finitely many subspaces `L²_P([G])` occur, and together they span a dense subspace of
  `L²([G])`;
* `L²_P([G]) = L²_{P'}([G])` when the Levi components `M` and `M'` are conjugate by a rational
  point `w` of `G`, that is, when `P` and `P'` are associate;
* `L²_P([G])` and `L²_{P'}([G])` are orthogonal when `P` and `P'` are not associate;
* `L²_G([G])` is the discrete spectrum `L²_disc([G])`. -/
def SpectralDecompositionStatement : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (hG : IsConnectedReductive G)
    (K : Subgroup (AdelicGroupPoints F G)) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth),
    IsMaximalCompactSubgroup F G K → IsClosedSubgroup rho →
    ∀ (P₀ : GroupScheme (Spec (CommRingCat.of F))) [IsAffine P₀.X.left] (p₀ : P₀ ⟶ G)
      [IsClosedImmersion p₀.hom.hom.left],
      IsMinimalParabolicSubgroup p₀ → IsIwasawaCompact p₀ K →
    let S : Set (Submodule ℂ (Lp ℂ 2 (RestrictionSplitCentre.canonicalMeasure F G))) :=
      {V | ∃ (P M U : GroupScheme (Spec (CommRingCat.of F)))
        (A : CommGroupScheme (Spec (CommRingCat.of F)))
        (_ : IsAffine P.X.left) (_ : IsAffine M.X.left) (_ : LocallyOfFiniteType M.X.hom)
        (_ : IsAffine U.X.left)
        (p : P ⟶ G) (_ : IsClosedImmersion p.hom.hom.left) (iU : U ⟶ P) (l : M ⟶ P)
        (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
        (_ : Mono r.data.i.hom.hom.left) (_ : Fintype (relativeWeylGroup r.data.i))
        (_ : Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left)
        (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
        haveI : LocallyOfFiniteType P.X.hom :=
          IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
        SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p ∧
        LeviSubgroup.IsGeometricUnipotentRadical iU ∧ ∃ hK : IsIwasawaCompact p K,
          V = parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT}
    (S.Finite ∧ (sSup S).topologicalClosure = ⊤) ∧
    ∀ (P M U : GroupScheme (Spec (CommRingCat.of F)))
      (A : CommGroupScheme (Spec (CommRingCat.of F)))
      [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
      (p : P ⟶ G) [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
      (a : A.toGrp ⟶ M) (r : ParabolicRootPresentation p l a)
      [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
      [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
      (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp),
      haveI : LocallyOfFiniteType P.X.hom :=
        IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
      SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p →
      LeviSubgroup.IsGeometricUnipotentRadical iU →
      ∀ hK : IsIwasawaCompact p K,
        (IsIso p → parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT =
          discreteSpectrum F G hG) ∧
        ∀ (P' M' U' : GroupScheme (Spec (CommRingCat.of F)))
          (A' : CommGroupScheme (Spec (CommRingCat.of F)))
          [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
          [IsAffine U'.X.left]
          (p' : P' ⟶ G) [IsClosedImmersion p'.hom.hom.left] (iU' : U' ⟶ P') (l' : M' ⟶ P')
          (a' : A'.toGrp ⟶ M') (r' : ParabolicRootPresentation p' l' a')
          [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
          [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
          (hA' : IsSplitTorus A'.toGrp) (hT' : IsSplitTorus r'.data.T.toGrp),
          haveI : LocallyOfFiniteType P'.X.hom :=
            IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
          SubgroupFunctor.range p₀ ≤ SubgroupFunctor.range p' →
          LeviSubgroup.IsGeometricUnipotentRadical iU' →
          ∀ hK' : IsIwasawaCompact p' K,
            ((∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
                IsWeylConjugation p l p' l' w c) →
              parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT =
                parabolicSpectrum hK' rho hsmooth hcalc iU' l' r' hA' hT') ∧
            ((¬ ∃ (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (c : M' ⟶ M),
                IsWeylConjugation p l p' l' w c) →
              parabolicSpectrum hK rho hsmooth hcalc iU l r hA hT ⟂
                parabolicSpectrum hK' rho hsmooth hcalc iU' l' r' hA' hT')

end Langlands.Global

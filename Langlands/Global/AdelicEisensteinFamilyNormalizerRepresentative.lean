import Langlands.Global.AdelicEisensteinFamilyWeylRepresentative
import Langlands.Global.AdelicEisensteinFamilyStandardSource
import Langlands.Global.AdelicWeylTorusAlignment
import Langlands.Global.AdelicStandardWeylRepresentative
import Langlands.Global.AdelicIntertwiningRightLeviRepresentative
import Langlands.Global.AdelicStandardWeylSteps
import Langlands.GroupScheme.Torus.SplitLatticeBaseChange

/-! # A normalizer representative matching the simple roots -/

noncomputable section

universe u v w

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic Langlands.Aubert.General.RationalPointFamily

variable {F : Type u} [Field F] [NumberField F]
  {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

variable {Q M' V : GroupScheme (Spec (CommRingCat.of F))}

/-- **A normalizer representative matching the simple roots.** For a Weyl conjugation `(w, c)`
between standard parabolics `P_I` and `P_J` of one family, there are a rational point `n` of
the normalizer of the maximal split torus and a Levi conjugation `c'` such that `(n, c')`
presents the same element of `W(P_I, P_J)`, its Weyl class maps the simple roots in `I` into
`J` and its inverse those in `J` into `I`, and the family comparison for `(n, c')` implies the
family comparison for `(w, c)`. -/
theorem FamilyRegularComparison.exists_normalizerRepresentative
    (fam : StandardParabolicFamily F G) (I J : StandardIndex F G fam.i fam.ν)
    [Fintype (relativeWeylGroup fam.i)] [IsClosedImmersion (fam.p I).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f I)).hom.hom.left]
    [IsClosedImmersion (fam.p J).hom.hom.left]
    [Mono (CommGroupScheme.groupHom (fam.f J)).hom.hom.left]
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : fam.M J ⟶ fam.M I}
    (hw : IsWeylConjugation (fam.p I) (fam.l I) (fam.p J) (fam.l J) w c)
    {proj : fam.P J ⟶ fam.M J} (hproj : fam.l J ≫ proj = 𝟙 (fam.M J))
    {K : Subgroup (AdelicGroupPoints F G)} (hKI : IsIwasawaCompact (fam.p I) K)
    (hKJ : IsIwasawaCompact (fam.p J) K) {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
    (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) :
    ∃ (n : normalizerPoints fam.i) (c' : fam.M J ⟶ fam.M I),
      IsWeylConjugation (fam.p I) (fam.l I) (fam.p J) (fam.l J) n.val c' ∧
      (∀ α ∈ I.val, schemeWeylCharacterAction fam.i
        (QuotientGroup.mk n : relativeWeylGroup fam.i) α ∈ J.val) ∧
      (∀ α ∈ J.val, schemeWeylCharacterAction fam.i
        ((QuotientGroup.mk n : relativeWeylGroup fam.i)⁻¹) α ∈ I.val) ∧
      (FamilyRegularComparison.{u, v, w} (fam.iU I) (fam.l I)
          (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩ :
            ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 (fam.iU J) (fam.l J)
          (⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
            ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
          (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 proj n.val c' hKI hKJ rho hsmooth hcalc →
        FamilyRegularComparison.{u, v, w} (fam.iU I) (fam.l I)
          (⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩ :
            ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I))
          (fam.isCompatible I).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 (fam.iU J) (fam.l J)
          (⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩ :
            ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
          (fam.isCompatible J).splitComponent.isCentralSplitTorus.1.1
          fam.maximalSplit.isSplitSubtorus.1 proj w c hKI hKJ rho hsmooth hcalc) := by
  classical
  have hG := fam.connectedReductive
  let stdI : ParabolicRootPresentation (fam.p I) (fam.l I) (fam.a I) :=
    ⟨⟨fam.T, fam.i, fam.ν, I.val, fam.f I⟩, fam.isCompatible I⟩
  let stdJ : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J) :=
    ⟨⟨fam.T, fam.i, fam.ν, J.val, fam.f J⟩, fam.isCompatible J⟩
  obtain ⟨z, e, he⟩ := weylTorusAlignment F G (fam.P I) (fam.M I) (fam.P J) (fam.M J) (fam.A I)
    (fam.A J) (fam.p I) (fam.l I) (fam.a I) stdI (fam.p J) (fam.l J) (fam.a J) stdJ w c hw
  let n₀ : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X := w * (z ≫ (fam.l I ≫ fam.p I).hom.hom)
  have hn₀inv : n₀⁻¹ ∈ normalizerPoints fam.i :=
    ⟨CommGroupScheme.isoOfGroupIso e, by
      change fam.i ≫ (G.innerIso n₀⁻¹).hom = e.hom ≫ fam.i
      rw [innerIso_inv_hom]
      exact he⟩
  have hn₀ : n₀ ∈ normalizerPoints fam.i := (normalizerPoints fam.i).inv_mem_iff.mp hn₀inv
  have hw₀ := hw.mul_right_levi z
  have : Finite (SimpleRoot fam.i fam.ν) :=
    (fam.maximalSplit.isSplitSubtorus.1.finite_simpleRelativeRoots fam.i fam.ν).to_subtype
  obtain ⟨LI, hLI⟩ := fam.exists_rootSet_eq I
  obtain ⟨LJ, hLJ⟩ := fam.exists_rootSet_eq J
  have hIr : SubgroupFunctor.range (fam.l I ≫ fam.p I) = standardLevi fam.i fam.ν (rootSet fam.i fam.ν LI) := by
    rw [hLI]
    exact (fam.isCompatible I).levi_eq
  have hJr : SubgroupFunctor.range (fam.l J ≫ fam.p J) = standardLevi fam.i fam.ν (rootSet fam.i fam.ν LJ) := by
    rw [hLJ]
    exact (fam.isCompatible J).levi_eq
  obtain ⟨z', n', hn', hIJ, hJI⟩ := standardWeylRepresentative F G (fam.P I) (fam.M I) (fam.P J)
    (fam.M J) fam.T fam.i fam.ν LI LJ (fam.p I) (fam.l I) (fam.p J) (fam.l J) hG fam.maximalSplit
    fam.generic hIr hJr ⟨n₀, hn₀⟩ _ hw₀
  have hw₁ := hw₀.mul_right_levi z'
  rw [← hn'] at hw₁
  let c' : fam.M J ⟶ fam.M I := (c ≫ ((fam.M I).innerIso z).inv) ≫ ((fam.M I).innerIso z').inv
  have hpar : weylParameter (F := F) (fam.l I) c proj = weylParameter (fam.l I) c' proj := by
    change _ = weylParameter (fam.l I) ((c ≫ ((fam.M I).innerIso z).inv) ≫ ((fam.M I).innerIso z').inv) proj
    rw [weylParameter_comp_innerIso_inv, weylParameter_comp_innerIso_inv]
  refine ⟨n', c', hw₁, ?_, ?_, fun h => ?_⟩
  · intro α hα
    rw [← hLJ]
    exact hIJ α (hLI ▸ hα)
  · intro α hα
    rw [← hLI]
    exact hJI α (hLJ ▸ hα)
  · exact FamilyRegularComparison.of_weylRepresentative hG (fam.isUnipotentRadical I) hproj hw hw₁
      hpar h

end Langlands.Global

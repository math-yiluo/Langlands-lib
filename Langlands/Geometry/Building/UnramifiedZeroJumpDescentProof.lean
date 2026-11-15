import Langlands.Geometry.Building.UnramifiedZeroJumpDescentAssembly
import Langlands.Geometry.Building.RootGroupLinearizationProof
import Langlands.Geometry.Building.UnramifiedZeroJumpGaloisDescent

/-! # Zero-value root jumps descend over the maximal unramified extension

This module proves `Langlands.Geometry.Building.UnramifiedZeroJumpDescentStatement`.

* `unramifiedZeroJumpGaloisDescent` is the descent principle for zero-value jumps that the
  reduction `unramifiedZeroJumpDescent_of_galoisDescent` (module
  `UnramifiedZeroJumpDescentAssembly`) takes as its hypothesis `hdesc`. Its type is that
  hypothesis, copied verbatim. It is proved by
  `MaximalUnramified.isRootFiltrationJump_fieldRestrict_of_linearization` (module
  `UnramifiedZeroJumpGaloisDescent`) at `r = 0`, whose linearization hypothesis is
  `rootGroupLinearization` (module `RootGroupLinearizationProof`).
* `unramifiedZeroJumpDescent` is the target: the reduction applied to the descent principle.
-/

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj Pointwise
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace
open Langlands.GroupScheme.GaloisPointComparison
open Langlands.LocalGalois.Separable

namespace Langlands.Geometry.Building

/-- **Descent of zero-value root jumps from `F^ur` to `F`.** Let `F` be a non-archimedean local
field, `K = F^ur`, `G` a connected reductive `F`-group with a maximal split torus `S`, and `α` a
root of `(G, S)`. Let `ψ` be a family of root functions of `(G_K, S_K)` such that, on the root
group `U_{α_K}(K)`, `ψ_{α_K}` is ultrametric (H1), invariant under `Aut(K/F)` (H2), and
invariant under conjugation by the points of `S_K` at which every rational character has
valuation one (H3). Then a jump of `α_K` at `0` for `ψ` gives a jump of `α` at `0` for
`fieldRestrict ψ`. The type is the hypothesis `hdesc` of
`unramifiedZeroJumpDescent_of_galoisDescent`, copied verbatim. -/
theorem unramifiedZeroJumpGaloisDescent :
    ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
      [IsNonarchimedeanLocalField F]
      (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G)
      (S : CommGroupScheme (Spec (CommRingCat.of F))) (iS : S.toGrp ⟶ G)
      (hiS : IsMaximalSplitTorus iS),
      letI : IsAffineHom G.X.hom := hG.isAffineHom
      letI : Smooth G.X.hom := hG.smooth
      haveI := mono_of_isMaximalSplitTorus hiS
      ∀ α ∈ relativeRoots iS,
      ∀ ψ : RootFunctionFamily
          ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S)
          ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj G),
        (∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ∀ h ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          min (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g)
              (ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) h) ≤
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (g * h⁻¹)) →
        (∀ σ : inertiaFixedField F ≃ₐ[F] inertiaFixedField F,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalConjugate F (inertiaFixedField F) G σ g) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        (∀ t ∈ characterValuationKernel (MaximalUnramified.valuation F)
            ((CommGroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).obj S).toGrp,
          ∀ g ∈ rootGroupPoints
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α),
          ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α)
              (rationalPoints.map
                ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) t *
                g * (rationalPoints.map
                  ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS)
                    t)⁻¹) =
            ψ (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) g) →
        IsRootFiltrationJump
            ((GroupScheme.baseChange (algebraBaseMap F (inertiaFixedField F))).map iS) ψ
            (characterLattice.baseChange (algebraBaseMap F (inertiaFixedField F)) S α) 0 →
          IsRootFiltrationJump iS
            (RootFunctionFamily.fieldRestrict (k := F) (K := inertiaFixedField F) ψ) α 0 :=
  fun F _ _ _ _ G hG S iS hiS => by
    have : IsAffineHom G.X.hom := hG.isAffineHom
    have : Smooth G.X.hom := hG.smooth
    have := mono_of_isMaximalSplitTorus hiS
    intro α hα ψ hmin hgal htor hjump
    have hEbase : RelativeRoot.HasOppositeFactorPairs iS := fun a ha g hg _ =>
      RelativeRoot.exists_oppositeFactorPair_of_componentReductivity
        RelativeRoot.kernelCentralizerComponentReductive F G hG S iS hiS a ha.1 g hg
    exact MaximalUnramified.isRootFiltrationJump_fieldRestrict_of_linearization F iS
      hiS.isSplitSubtorus.1 hα
      (rootGroupLinearization iS hiS.isSplitSubtorus.1 hEbase hα (MaximalUnramified.valuation F))
      ψ hmin hgal htor 0 hjump

/-- **Zero-value root jumps descend over `F^ur`** (an internal pointwise form of the converse
part of KP Proposition 9.4.28, at a point where the affine root vanishes). -/
theorem unramifiedZeroJumpDescent : UnramifiedZeroJumpDescentStatement.{u} :=
  unramifiedZeroJumpDescent_of_galoisDescent unramifiedZeroJumpGaloisDescent

end Langlands.Geometry.Building

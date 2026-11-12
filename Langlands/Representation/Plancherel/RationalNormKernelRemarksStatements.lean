import Langlands.Representation.Plancherel.RationalNormKernelTopology
import Mathlib.MeasureTheory.Group.ModularCharacter

/-! # Remaining assertions of Renard V.2.3, V.2.5 and V.2.6 on the norm kernel `⁰G`

(V.2.3, Proposition) `⁰G` is unimodular. (V.2.5) For split tori `A₁ ⊆ A₂`,
`⁰A₁ = A₁ ∩ ⁰A₂`. (V.2.6, Proposition) If the centre of `G` is compact, then `⁰G = G`.
The V.2.6 Lemma `⁰A_G = ⁰G ∩ A_G` is the published
`RenardCartan.SplitComponentKernelStatement`.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj

namespace Langlands.Plancherel

/-- Renard V.2.3, Proposition, the unimodularity clause: for a connected reductive `G` over
a nonarchimedean local field, the open subgroup `⁰G = rationalCommonNormKernel G` of `G(F)`
is unimodular: its modular character is identically one. The topology on `G(F)` is the
canonical `rationalPointTopology`; local compactness, the nonarchimedean group structure and
Hausdorffness of `G(F)` are displayed as instance binders, and `⁰G` carries the subspace
topology, locally compact because `⁰G` is open (`isOpen_rationalCommonNormKernel`). -/
def RationalNormKernelUnimodularStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    haveI := hG.smooth
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    ∀ [LocallyCompactSpace (GroupScheme.rationalPoints G)]
      [NonarchimedeanGroup (GroupScheme.rationalPoints G)]
      [T2Space (GroupScheme.rationalPoints G)],
      haveI : LocallyCompactSpace (rationalCommonNormKernel G) :=
        (isOpen_rationalCommonNormKernel G).locallyCompactSpace
      ∀ h : rationalCommonNormKernel G, MeasureTheory.Measure.modularCharacter h = 1

/-- Renard V.2.5, last paragraph: for split tori `A₁ ⊆ A₂` over a nonarchimedean local
field, that is a split subtorus `f : A₁ ⟶ A₂` of the split torus `A₂`, a point of `A₁(F)` lies
in `⁰A₁` exactly when its image lies in `⁰A₂`: `⁰A₁ = A₁ ∩ ⁰A₂`. -/
def RationalNormKernelRestrictionStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (A₁ A₂ : CommGroupScheme (Spec (CommRingCat.of F))) (f : A₁.toGrp ⟶ A₂.toGrp),
    IsSplitTorus A₂.toGrp → IsSplitSubtorus f →
      (rationalCommonNormKernel A₂.toGrp).comap (GroupScheme.rationalPoints.map f) =
        rationalCommonNormKernel A₁.toGrp

/-- Renard V.2.6, Proposition, last assertion: for a connected reductive `G` over a
nonarchimedean local field, if the centre of `G(F)` is compact for the canonical
`rationalPointTopology`, then `⁰G = G(F)`. -/
def RationalNormKernelCompactCenterStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) (hG : IsConnectedReductive G),
    haveI := hG.isAffineHom
    haveI : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom
    letI : TopologicalSpace (GroupScheme.rationalPoints G) := rationalPointTopology F G.X
    IsCompact (Subgroup.center (GroupScheme.rationalPoints G) :
        Set (GroupScheme.rationalPoints G)) →
      rationalCommonNormKernel G = ⊤

end Langlands.Plancherel

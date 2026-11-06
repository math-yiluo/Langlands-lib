import Langlands.GroupScheme.SimplyConnected.Basic
import Langlands.GroupScheme.Rational.RelativeRoots
import Langlands.GroupScheme.Rational.RootSubgroup
import Langlands.Representation.Plancherel.RationalCharacterValuation

/-!
# Rank-one generation of split-torus centralizers in simply connected groups

A Kneser–Tits type generation statement over nonarchimedean local fields.
This module states a proposition and supplies no proof of it.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

/-- For a simply connected group `G` over a nonarchimedean local field with maximal split
torus `S` and represented centralizer `Z = Z_G(S)`, every rational point of `Z` is a product
of centralizing elements of the rank-one groups `⟨U_a(F), U_{-a}(F)⟩` and an element of
the norm-one subgroup `Z(F)^1`. -/
def SimplyConnectedRankOneCentralizerGenerationStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom], IsSimplyConnected G →
    ∀ (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G),
      IsMaximalSplitTorus i →
    ∀ (Z : GroupScheme (Spec (CommRingCat.of F))) (j : Z ⟶ G),
      (torusCentralizer i).IsRepresentedBy j →
      (rationalPoints.map j).range ≤
        Subgroup.closure (⋃ a ∈ relativeRoots i,
            ((centralizerPoints i ⊓ Subgroup.closure
              (((RelativeRoot.subgroup i a).carrier (Over.mk (𝟙 _)) :
                  Set (rationalPoints G)) ∪
                (RelativeRoot.subgroup i (-a)).carrier (Over.mk (𝟙 _))) :
              Subgroup (rationalPoints G)) : Set (rationalPoints G))) ⊔
          (Plancherel.rationalCommonNormKernel Z).map (rationalPoints.map j)

end Langlands.GroupScheme

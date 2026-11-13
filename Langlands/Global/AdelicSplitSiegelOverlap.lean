import Langlands.Global.AdelicSplitFundamentalSet

/-! # Springer's Siegel-set overlap estimate for split groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal Pointwise

namespace Langlands.Global.AdelicSiegelFactors

open Langlands.GroupScheme AdelicGroupPoints

/-- Springer's Proposition 2.6 for a split connected reductive group, in the right-action
form produced by `HasRightAdelicFundamentalSet`. Fix a compact set `C` of adelic points and
an upper bound `c` for the simple-root norms. For each simple root `α` there is a threshold
`d` such that whenever one adelic point has two factorizations
`x i(s) p q = x' i(s') p' q'`, with `x, x' ∈ C`, norm-one torus factors whose simple-root
norms are at most `c`, norm-one minimal-parabolic factors and rational right factors, and
moreover `|α(s)| ≤ d`, the rational quotient `q' q⁻¹` lies in the standard maximal
parabolic `P_(Δ \ {α})` over the ground field. -/
def SplitSiegelOverlapStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom],
    IsConnectedReductive G →
      ∀ (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
        (ν : cocharacterLattice T),
        IsMaximalSplitTorus i → IsMaximalTorus i → IsGenericCocharacter i ν →
          ∀ C : Set (AdelicGroupPoints F G), IsCompact C →
            ∀ c : ℝ≥0ˣ, ∀ α ∈ simpleRelativeRoots i ν, ∃ d : ℝ≥0ˣ,
              ∀ x ∈ C, ∀ x' ∈ C,
                ∀ (s s' : AdelicGroupPoints F T.toGrp)
                  (p p' : normOneSubgroup F (Standard.parabolicScheme i ν ∅))
                  (q q' : RationalGroupPoints F G),
                  map F T.toGrp G i s ∈ normOneSubgroup F G →
                  map F T.toGrp G i s' ∈ normOneSubgroup F G →
                  (∀ β ∈ simpleRelativeRoots i ν,
                    PositiveRealTorus.normCharacter F T β s ≤ c) →
                  (∀ β ∈ simpleRelativeRoots i ν,
                    PositiveRealTorus.normCharacter F T β s' ≤ c) →
                  PositiveRealTorus.normCharacter F T α s ≤ d →
                  x * map F T.toGrp G i s *
                      map F _ G (Standard.parabolicHom i ν ∅) p * rational F G q =
                    x' * map F T.toGrp G i s' *
                      map F _ G (Standard.parabolicHom i ν ∅) p' * rational F G q' →
                  ∃ r : RationalGroupPoints F
                      (Standard.parabolicScheme i ν (simpleRelativeRoots i ν \ {α})),
                    (Standard.parabolicScheme i ν (simpleRelativeRoots i ν \ {α})).affinePointsTarget
                        (Standard.parabolicHom i ν (simpleRelativeRoots i ν \ {α}))
                        (CommAlgCat.of F F) r = q' * q⁻¹

end Langlands.Global.AdelicSiegelFactors

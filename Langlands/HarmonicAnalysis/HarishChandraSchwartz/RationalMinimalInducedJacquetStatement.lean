import Langlands.HarmonicAnalysis.HarishChandraSchwartz.RationalXiCoefficient
import Langlands.Representation.Jacquet.StandardFixedVectorGeneration
import Langlands.Representation.Jacquet.StandardCasselmanPairing

/-! # The center of `M_J` acts unipotently on the Jacquet modules of `I_{P₀}^G 1` (statement)

`RationalMinimalInducedJacquetUnipotentStatement`: for a connected reductive group `G` over a
nonarchimedean local field, a maximal split torus, a generic cocharacter and an actual standard
parabolic `P_J = M_J U_J`, there is `d` such that `(π_P(z) - 1)^d = 0` on the normalized Jacquet
module `V_P` of `(π, V) = I_{P₀}^G 1` for every `z` in the center of `M_J(F)`. In particular
(`RationalMinimalInducedJacquetUnipotentStatement.splitComponent`) this holds for every point `a`
of a compatible split component `A_{M_J}`, which is the fact used by Waldspurger in the proof of
Lemma II.1.1 ("On voit qu'il existe un entier `d` tel que pour tout `a ∈ A_M`, `(π_P(a) - 1)^d`
annule `V_P`"). The Jacquet module is normalized by `δ_{U_J}`, the Haar modulus of conjugation on
`U_J(F)`.
-/
noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj NNReal
open Langlands.GroupScheme Langlands.AlgebraicGeometry.PointTopology
open Langlands.BruhatTits.SpecialCompact

namespace Langlands.HarishChandraSchwartz

attribute [local instance] rationalWeightsIsAffine rationalWeightsTopology
  rationalWeightsTopologicalGroup rationalWeightsT2Field rationalWeightsLocallyCompact
  rationalWeightsMeasurableSpace rationalWeightsBorelSpace

/-- **The normalized Jacquet module of `I_{P₀}^G 1` along `P_J`**: the coinvariants of
`rationalMinimalInduced` under the actual standard radical `U_J(F)`, with the action of the
standard Levi `M_J(F)` normalized by the inverse square root of `δ_{U_J}`, the Haar modulus of
conjugation on the closed subgroup `U_J(F)` (Waldspurger's `(π_P, V_P)` of I.3 for
`π = I_{P₀}^G 1`, with `δ_{U_J}` in place of `δ_P`). -/
def rationalMinimalInducedJacquet {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F] {S : CommGroupScheme (Spec (CommRingCat.of F))}
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (i : S.toGrp ⟶ G) (ν : cocharacterLattice S)
    (h : Aubert.General.IsSemidirectDecomposition (standardParabolicPoints i ν ∅)
      (standardLeviPoints i ν ∅) (standardUnipotentPoints i ν ∅))
    (J : Set (characterLattice S)) :
    Representation ℂ (standardLeviPoints i ν J)
      (Jacquet.Coinvariants (rationalMinimalInduced i ν h).representation
        (standardUnipotentPoints i ν J)) :=
  Jacquet.normalizedActionOfModulus (rationalMinimalInduced i ν h).representation
    (standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
    (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J)
    (HaarModulus.closedRestrictCharacter (standardUnipotentPoints i ν J)
      (isClosed_standardUnipotentPoints i ν J) (standardLeviPoints i ν J)
      (standardLeviPoints_le_normalizer_standardUnipotentPoints i ν J))

/-- **Unipotence of the center of `M_J` on the Jacquet modules of `I_{P₀}^G 1`** (a
strengthening of the fact stated in Waldspurger's proof of Lemme II.1.1, printed p. 251, derived
there from the computation of `π_P` in I.3). Let `F` be a nonarchimedean local field, `G` a
connected reductive group over `F` with a maximal split torus `i : S → G` and a generic
cocharacter `ν`, and `(π, V)` the actual normalized induction `I_{P₀}^G 1` of the trivial character
of `M₀(F)` (`rationalMinimalInduced`, for the decomposition
`isSemidirectDecomposition_minimalStandard`). For every set `J` of simple relative roots there is
`d ∈ ℕ` such that `(π_P(z) - 1)^d = 0` on the normalized Jacquet module
`V_P = rationalMinimalInducedJacquet` for every `z ∈ M_J(F)` commuting with every element of
`M_J(F)`. -/
def RationalMinimalInducedJacquetUnipotentStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    (S : CommGroupScheme (Spec (CommRingCat.of F))) (i : S.toGrp ⟶ G)
    (hi : IsMaximalSplitTorus i) (ν : cocharacterLattice S) (hν : IsGenericCocharacter i ν)
    (J : Set (characterLattice S)), J ⊆ simpleRelativeRoots i ν →
    ∃ d : ℕ, ∀ z : standardLeviPoints i ν J, (∀ m : standardLeviPoints i ν J, z * m = m * z) →
      (rationalMinimalInducedJacquet i ν (isSemidirectDecomposition_minimalStandard hG hi hν) J z
          - 1) ^ d = 0

/-- **The split-component form** used in Waldspurger's proof of Lemme II.1.1: under
`RationalMinimalInducedJacquetUnipotentStatement`, for every compatible split component
`q : A → S` of `M_J` there is `d` with `(π_P(a) - 1)^d = 0` for every point `a` in the image of
`A(F)`, which is central in `M_J(F)` (`IsCompatibleStandardSplitComponent.map_commute`). -/
theorem RationalMinimalInducedJacquetUnipotentStatement.splitComponent
    (h : RationalMinimalInducedJacquetUnipotentStatement.{u})
    {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom] (hG : IsConnectedReductive G)
    {S : CommGroupScheme (Spec (CommRingCat.of F))} {i : S.toGrp ⟶ G}
    (hi : IsMaximalSplitTorus i) {ν : cocharacterLattice S} (hν : IsGenericCocharacter i ν)
    {J : Set (characterLattice S)} (hJ : J ⊆ simpleRelativeRoots i ν)
    {A : CommGroupScheme (Spec (CommRingCat.of F))} {q : A.toGrp ⟶ S.toGrp}
    (hA : IsCompatibleStandardSplitComponent i ν J A q) :
    ∃ d : ℕ, ∀ x : rationalPoints A.toGrp,
      (rationalMinimalInducedJacquet i ν (isSemidirectDecomposition_minimalStandard hG hi hν) J
          ⟨rationalPoints.map (q ≫ i) x, hA.map_mem_standardLeviPoints i ν x⟩ - 1) ^ d = 0 := by
  obtain ⟨d, hd⟩ := h F G hG S i hi ν hν J hJ
  exact ⟨d, fun x => hd _ fun m => Subtype.ext (hA.map_commute x m.2).symm⟩

end Langlands.HarishChandraSchwartz

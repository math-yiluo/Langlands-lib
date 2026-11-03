import Langlands.GroupScheme.Rational.DominantChamberMove
import Langlands.GroupScheme.Rational.ParabolicCocharacterConjugacy
import Langlands.GroupScheme.Rational.CocharacterStandardFace
import Langlands.GroupScheme.Rational.StandardParabolicClassificationReduction
import Langlands.GroupScheme.Rational.ParabolicConjugacyRigidity
import Langlands.GroupScheme.Rational.ReflectionNegation
import Langlands.GroupScheme.Rational.StandardParabolicClassificationStatement
import Langlands.GroupScheme.Dynamic.SmoothProof

/-! # The rational classification of standard parabolics from its structural inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {k : Type u} [Field k]
  {T : CommGroupScheme (Spec (CommRingCat.of k))}
  {G : GroupScheme (Spec (CommRingCat.of k))}

/-- Every cocharacter of a connected reductive group is conjugated by a rational point to
one whose dynamic parabolic contains the generic parabolic `P(ν)`, on every test scheme.
The route is maximal split torus conjugacy followed by a normalizer move into the closed
dominant chamber; minimal-parabolic conjugacy is not used. -/
theorem exists_conjugate_parabolic_containing_generic_of_chamber
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hroot : RelativeRootSystemStatement.{u})
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        ∃ g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X,
          Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
            Dynamic.parabolic (zeta ≫ (G.innerIso g).hom) := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  intro hν zeta
  obtain ⟨g, ξ, hg⟩ := exists_innerIso_comp_eq_cocharacter hconj hi zeta
  obtain ⟨n, hn⟩ := exists_normalizerPoint_parabolic_le_of_statements hroot hsigns hG hi hν ξ
  refine ⟨(n : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X) * g, ?_⟩
  rw [innerIso_mul_hom, ← Category.assoc, hg]
  exact hn

/-- A rational point conjugating a cocharacter to one whose dynamic parabolic contains
`P(ν)`, chosen under the hypotheses of
`exists_conjugate_parabolic_containing_generic_of_chamber`, with its containment. -/
def conjugatingPointToGenericOvergroup
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hroot : RelativeRootSystemStatement.{u})
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} (hν : letI := hG.isAffineHom; IsGenericCocharacter i ν)
    (zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G) :
    {g : Over.mk (𝟙 (Spec (CommRingCat.of k))) ⟶ G.X //
      Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤
        Dynamic.parabolic (zeta ≫ (G.innerIso g).hom)} :=
  Classical.indefiniteDescription _
    (exists_conjugate_parabolic_containing_generic_of_chamber hconj hroot hsigns hG hi hν zeta)

/-- Standardness by containment: a dynamic parabolic of a connected reductive group
containing the generic parabolic `P(ν)` is a standard parabolic `P_J`, `J ⊆ Δ`. -/
theorem exists_standardParabolic_eq_of_parabolic_le_of_structural_statements
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hnegation : RelativeRootNegationStatement.{u})
    (hG : IsConnectedReductive G) {i : T.toGrp ⟶ G} (hi : IsMaximalSplitTorus i)
    {ν : cocharacterLattice T} :
    letI := hG.isAffineHom
    IsGenericCocharacter i ν →
      ∀ zeta : (Gm (Spec (CommRingCat.of k))).toGrp ⟶ G,
        Dynamic.parabolic (CommGroupScheme.groupHom ν ≫ i) ≤ Dynamic.parabolic zeta →
          ∃ J : Set (characterLattice T), J ⊆ simpleRelativeRoots i ν ∧
            Dynamic.parabolic zeta = standardParabolic i ν J := by
  have := hG.isAffineHom
  have := hG.smooth
  have := hG.connectedSpace
  intro hν zeta hle
  obtain ⟨ξ, hξ⟩ :=
    exists_parabolic_eq_cocharacter_of_parabolic_le hconj dynamicSmooth hconn hi ν zeta hle
  rw [hξ] at hle ⊢
  exact exists_standardParabolic_eq_of_parabolic_le_of_statements hsigns hnegation hG T i hi ν
    hν ξ hle

/-- **The rational classification of standard parabolics**, conditional on its
structural inputs: conjugacy of maximal split tori in smooth connected affine groups,
connectedness of dynamic subgroups, the relative root system, the root-sign criterion,
the relative Tits system and the order of standard parabolics. Smoothness of dynamic
subgroups is the published `dynamicSmooth`. -/
theorem standardParabolicClassificationStatement_of_structural_statements
    (hconj : SmoothMaximalSplitTorusConjugacyStatement.{u})
    (hconn : DynamicConnectedStatement.{u})
    (hroot : RelativeRootSystemStatement.{u})
    (hsigns : RelativeRootSignInclusionsStatement.{u})
    (hTS : RelativeTitsSystemStatement.{u})
    (horder : StandardParabolicOrderStatement.{u}) :
    StandardParabolicClassificationStatement.{u} := by
  intro k _ G hG T i hi ν
  have := hG.isAffineHom
  have := hi.isSplitSubtorus.mono
  intro hν
  exact standardParabolicClassification_of_local_inputs i ν
    (exists_standardParabolic_eq_of_parabolic_le_of_structural_statements hconj hconn hsigns
      (relativeRootNegationStatement_of_relativeRootSystemStatement hroot) hG hi hν)
    (exists_conjugate_parabolic_containing_generic_of_chamber hconj hroot hsigns hG hi hν)
    (horder k G hG T i hi ν hν).2
    (fun J K h => standardParabolic_eq_of_isRationallyConjugate_of_statements hTS horder hG T i
      hi ν hν J.1 K.1 J.2 K.2 h)

end Langlands.GroupScheme

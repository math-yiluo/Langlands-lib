import Langlands.GroupScheme.Quaternionic.MaximalSplitTorusWeightsStatement
import Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankStatement
import Langlands.GroupScheme.Quaternionic.ConnectedIsometrySplitRankProof
import Langlands.GroupScheme.Quaternionic.IsometryTorusWeightAssembly
import Langlands.GroupScheme.Rational.SmoothMaximalSplitTorusConjugacyProof
import Langlands.GroupScheme.Rational.MaximalSplitTorusExtension
import Langlands.GroupScheme.Rational.SplitRankReduction

/-! # Maximal split torus weights from the connected rank equality -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme.Quaternionic

/-- The connected rank equality implies the maximal split torus weight formula. -/
theorem isometryMaximalSplitTorusWeights_of_connectedIsometrySplitRank
    (hRank : ConnectedIsometrySplitRankStatement.{u}) :
    IsometryMaximalSplitTorusWeightsStatement.{u} := by
  classical
  intro K D _ _ _ _ _ degree hdeg σ hσ n _ _ q _ hq S i hi
  obtain ⟨I, hI, ⟨e⟩⟩ := hi.1.1
  let : Finite I := hI
  let : Fintype I := Fintype.ofFinite I
  have hcard := hi.card_eq_splitRank_of_extension_conjugacy
    (fun J _ j hj =>
      exists_maximalSplitTorus_extension (σ.connectedIsometryGroup q) j
        (T := splitTorus.commGroupScheme (Spec (CommRingCat.of K)) J)
        ⟨isSplitTorus_splitTorus J, hj⟩)
    (fun T' i' hi' =>
      smoothMaximalSplitTorusConjugacy K (σ.connectedIsometryGroup q)
        T' S i' i hi' hi) I e
  have hrank : Fintype.card I = σ.quadraticWittIndex q := by
    have h := hcard.trans (hRank K D degree hdeg σ hσ n q hq)
    rw [Nat.card_eq_fintype_card] at h
    exact_mod_cast h
  have hclosed : IsClosedSubgroup
      (i ≫ identityComponentι (σ.isometryGroup q)) :=
    hi.1.2.comp (IdentityComponent.isClosedSubgroup_identityComponentι _)
  simpa only [Category.assoc] using
    σ.exists_characters_of_isometryTorus_rank_eq q hq
      (i ≫ identityComponentι (σ.isometryGroup q)) hclosed e hrank

/-- Weights of a maximal split torus of the connected quadratic isometry group. -/
theorem isometryMaximalSplitTorusWeights :
    IsometryMaximalSplitTorusWeightsStatement.{u} :=
  isometryMaximalSplitTorusWeights_of_connectedIsometrySplitRank
    connectedIsometrySplitRank

end Langlands.GroupScheme.Quaternionic

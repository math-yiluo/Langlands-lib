import Langlands.Correspondence.SupercuspidalFactorCompatibility

/-!
# The irreducible-Weil/supercuspidal local Langlands correspondence

The correspondence predicate on a supercuspidal map conjoins rankwise bijectivity,
dual compatibility and, for one geometrically normalized reciprocity candidate,
rank one, determinant, twist and pair-factor compatibility. Existence and
uniqueness, per field and over all p-adic fields, are propositions only.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `c` is an irreducible-Weil/supercuspidal local Langlands correspondence for
`GL_n(F)`, all `n ≥ 1`: it is bijective in every rank and compatible with
contragredients, and some reciprocity candidate with the geometric normalization
makes it compatible with rank one, determinants, all quasi-character twists and
all pair L- and epsilon-factors for every nontrivial additive character. -/
def IsSupercuspidalCorrespondence (c : SupercuspidalMap.{uF, uP, uA} F) : Prop :=
  SupercuspidalRankwiseBijective F c ∧ SupercuspidalDualCompatibility F c ∧
    ∃ e : ReciprocityCandidate F, IsGeometricReciprocity F e ∧
      SupercuspidalRankOneCompatibility F e c ∧
      SupercuspidalDeterminantCompatibility F e c ∧
      SupercuspidalTwistCompatibility F e c ∧
      SupercuspidalFactorCompatibility F e c

/-- Existence of a supercuspidal correspondence over `F` (statement only). -/
def SupercuspidalCorrespondenceExistence : Prop :=
  ∃ c : SupercuspidalMap.{uF, uP, uA} F, IsSupercuspidalCorrespondence F c

/-- Uniqueness of a supercuspidal correspondence over `F`, as equality of maps on
isomorphism classes in every rank (statement only). -/
def SupercuspidalCorrespondenceUniqueness : Prop :=
  ∀ c c' : SupercuspidalMap.{uF, uP, uA} F,
    IsSupercuspidalCorrespondence F c → IsSupercuspidalCorrespondence F c' → c = c'

/-- Existence and uniqueness of a supercuspidal correspondence over `F`
(statement only). -/
def SupercuspidalCorrespondenceExistsUnique : Prop :=
  ∃! c : SupercuspidalMap.{uF, uP, uA} F, IsSupercuspidalCorrespondence F c

/-- For every prime `p` and every p-adic field `F`, there is exactly one
supercuspidal correspondence (statement only; no correspondence is an input). -/
def SupercuspidalCorrespondenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    SupercuspidalCorrespondenceExistsUnique.{uF, uP, uA} F

end Langlands.Correspondence

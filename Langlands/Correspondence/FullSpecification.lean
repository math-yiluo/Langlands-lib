import Langlands.Correspondence.FullFactorCompatibility
import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.Correspondence.UnramifiedNormalization

/-!
# The full local Langlands correspondence for GL_n

The correspondence predicate on a full map, from Frobenius-semisimple Weil–Deligne
classes with arbitrary monodromy to all irreducible admissible classes, conjoins
rankwise bijectivity, dual compatibility and, for one geometrically normalized
reciprocity candidate, rank one, determinant, twist and full pair-factor
compatibility. Existence and uniqueness, per field and over all p-adic fields, the
restriction to the supercuspidal correspondence and the unramified normalization
are propositions only.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- `c` is a local Langlands correspondence for `GL_n(F)`, all `n ≥ 1`: it is
bijective in every rank and compatible with contragredients, and some reciprocity
candidate with the geometric normalization makes it compatible with rank one,
determinants, all quasi-character twists and all pair L- and epsilon-factors for
every nontrivial additive character. -/
def IsFullCorrespondence (c : FullMap.{uF, uP, uA} F) : Prop :=
  RankwiseBijective F c ∧ DualCompatibility F c ∧
    ∃ e : ReciprocityCandidate F, IsGeometricReciprocity F e ∧
      RankOneCompatibility F e c ∧
      DeterminantCompatibility F e c ∧
      TwistCompatibility F e c ∧
      FullFactorCompatibility F e c

/-- Existence of a full correspondence over `F` (statement only). -/
def FullCorrespondenceExistence : Prop :=
  ∃ c : FullMap.{uF, uP, uA} F, IsFullCorrespondence F c

/-- Uniqueness of a full correspondence over `F`, as equality of maps on
isomorphism classes in every rank (statement only). -/
def FullCorrespondenceUniqueness : Prop :=
  ∀ c c' : FullMap.{uF, uP, uA} F,
    IsFullCorrespondence F c → IsFullCorrespondence F c' → c = c'

/-- Existence and uniqueness of a full correspondence over `F` (statement only). -/
def FullCorrespondenceExistsUnique : Prop :=
  ∃! c : FullMap.{uF, uP, uA} F, IsFullCorrespondence F c

/-- For every prime `p` and every p-adic field `F`, there is exactly one full
correspondence (statement only; no correspondence is an input). -/
def FullCorrespondenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    FullCorrespondenceExistsUnique.{uF, uP, uA} F

/-- Restriction (statement only): every full correspondence extends some
supercuspidal correspondence, through the zero-monodromy and supercuspidal
inclusions. -/
def FullCorrespondenceRestrictionStatement : Prop :=
  ∀ c : FullMap.{uF, uP, uA} F, IsFullCorrespondence F c →
    ∃ c0 : SupercuspidalMap.{uF, uP, uA} F,
      IsSupercuspidalCorrespondence F c0 ∧ ExtendsSupercuspidal F c0 c

/-- Unramified normalization (statement only): every full correspondence satisfies
the spherical and principal-series conditions for the geometrically normalized
reciprocity candidate. -/
def FullCorrespondenceUnramifiedStatement : Prop :=
  ∀ (c : FullMap.{uF, uP, uA} F) (e : ReciprocityCandidate F),
    IsFullCorrespondence F c → IsGeometricReciprocity F e → UnramifiedCompatibility F e c

end Langlands.Correspondence

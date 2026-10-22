import Langlands.Correspondence.FullSpecification
import Langlands.Correspondence.AssemblyRelation

/-!
# The assembled correspondence

Two statements about the assembly of a supercuspidal correspondence, after
Henniart 2002: the assembly inherits pair epsilon-factor compatibility
(Theorem 1.5(iii), epsilon part), and, conditionally on a supercuspidal
correspondence, the assembly exists and is a full correspondence. The
unconditional statement is `FullCorrespondenceStatement`; the prerequisite is
`SupercuspidalCorrespondenceStatement`. These are statements, not proofs.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Inherited pair epsilon-factor compatibility (statement only): the assembly of a
supercuspidal correspondence is compatible with all pair epsilon-factors, for every
nontrivial additive character, for some system whose base component is the
geometrically normalized reciprocity candidate. -/
def AssemblyEpsilonInheritanceStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F),
    IsSupercuspidalCorrespondence F c0 → IsAssemblyOf F c0 c → IsGeometricReciprocity F e →
      FullEpsilonCompatibility F e c

/-- Conditional assembly (statement only): if `c0` is a supercuspidal
correspondence, then `c0` has an assembly, and every assembly of `c0` is a full
correspondence. -/
def ConditionalAssemblyStatement : Prop :=
  ∀ c0 : SupercuspidalMap.{uF, uP, uA} F, IsSupercuspidalCorrespondence F c0 →
    (∃ c : FullMap.{uF, uP, uA} F, IsAssemblyOf F c0 c) ∧
      ∀ c : FullMap.{uF, uP, uA} F, IsAssemblyOf F c0 c → IsFullCorrespondence F c

end Langlands.Correspondence

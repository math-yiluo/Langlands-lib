import Langlands.Correspondence.AssemblyRankOne
import Langlands.Correspondence.AssemblyDeterminant
import Langlands.Correspondence.AssemblyTwist
import Langlands.Correspondence.AssemblyDual
import Langlands.Correspondence.AssemblyUniqueness
import Langlands.Representation.Classification.MultisegmentConstituentCentralCharacterProof
import Langlands.Representation.Classification.MultisegmentConstituentCharacterTwistCompatibilityProof
import Langlands.Representation.Classification.MultisegmentConstituentContragredientProof

/-!
# Rank-one, determinant, twist and dual compatibility of the assembly

Proof of `AssemblyOperationStatement`. Rank one and the determinant come from
`rankOneCompatibility_of_assembly` and
`AssemblyDeterminant.determinantCompatibility_of_assembly`, the latter with the published
central-character compatibility of multisegment heads. For twists and duals, the
reductions in `AssemblyTwist` and `AssemblyDual` produce a twisted or dual parameter
class `E` and an automorphic class assembled from `E` with the required relation to the
assembled class of `D`. The unconditional uniqueness `isAssembledFrom_unique` identifies it
with the assembled class of `E`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The assembly of a supercuspidal map compatible with twists is compatible with
twists. -/
theorem twistCompatibility_of_isAssemblyOf {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c : FullMap.{uF, uP, uA} F} {e : ReciprocityCandidate F} (hc : IsAssemblyOf F c0 c)
    (htwist : SupercuspidalTwistCompatibility F e c0) : TwistCompatibility F e c := by
  intro n D χ
  obtain ⟨E, hE⟩ := AssemblyTwist.exists_isTwistOf F (LocalFactor.RankOne.weilCharacter F e χ)
    (AssemblyTwist.isOpen_ker_weilCharacter_inertia F e χ) D
  refine ⟨E, hE, ?_⟩
  obtain ⟨r, d, m, σ, hB, hH⟩ := hc n D
  obtain ⟨π', hπ', hH'⟩ := AssemblyTwist.isMultisegmentHeadClass_twist F
    (Classification.multisegmentConstituentCharacterTwistCompatibility F
      F.canonicalTopologicalData) c0 e htwist χ σ m hH
  have hE' : IsAssembledFrom F c0 E π' :=
    ⟨r, d, m, _, AssemblyTwist.isBlockSum_twist F e χ σ m hB hE, hH'⟩
  rwa [isAssembledFrom_unique F c0 (hc n E) hE']

/-- The assembly of a supercuspidal map compatible with twists and duals is compatible
with duals, for a geometrically normalized reciprocity candidate. -/
theorem dualCompatibility_of_isAssemblyOf {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c : FullMap.{uF, uP, uA} F} {e : ReciprocityCandidate F} (hc : IsAssemblyOf F c0 c)
    (he : IsGeometricReciprocity F e) (htwist : SupercuspidalTwistCompatibility F e c0)
    (hdual : SupercuspidalDualCompatibility F c0) : DualCompatibility F c := by
  intro n D
  obtain ⟨E, hE⟩ := AssemblyDual.exists_isDualOf F D
  refine ⟨E, hE, ?_⟩
  obtain ⟨r, d, m, σ, hB, hH⟩ := hc n D
  obtain ⟨π', hπ', hH'⟩ :=
    AssemblyDual.isMultisegmentHeadClass_dual F
      (Classification.multisegmentConstituentContragredientCompatibility F
        F.canonicalTopologicalData) c0 he htwist hdual σ m hH
  have hE' : IsAssembledFrom F c0 E π' :=
    ⟨r, d, m, _, AssemblyDual.isBlockSum_dual F e σ m hB hE, hH'⟩
  rwa [isAssembledFrom_unique F c0 (hc n E) hE']

/-- **Operation compatibility of the assembly.** -/
theorem assemblyOperation : AssemblyOperationStatement.{uF, uP, uA} F := by
  intro c0 c e hc he hrank hdet htwist hdual
  exact ⟨rankOneCompatibility_of_assembly F hc hrank,
    AssemblyDeterminant.determinantCompatibility_of_assembly F
      (Classification.multisegmentConstituentCentralCharacter F F.canonicalTopologicalData)
      c0 c e hc he hdet,
    twistCompatibility_of_isAssemblyOf F hc htwist,
    dualCompatibility_of_isAssemblyOf F hc he htwist hdual⟩

end Langlands.Correspondence

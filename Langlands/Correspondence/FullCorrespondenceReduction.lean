import Langlands.Correspondence.AssemblyConstruction
import Langlands.Correspondence.AssemblyWellDefinedProof
import Langlands.Correspondence.AssemblyBijectiveProof
import Langlands.Correspondence.AssemblyOperationProof
import Langlands.Correspondence.AssemblyLInheritanceProof
import Langlands.Correspondence.AssemblyEpsilonInheritanceProof
import Langlands.Correspondence.AssemblyLCharacterizationReduction
import Langlands.Correspondence.AssemblySquareIntegrablePreimageReduction
import Langlands.Correspondence.FullCharacterizationExtendsReduction
import Langlands.Correspondence.FullCharacterizationStatement
import Langlands.Correspondence.FullSpecification
import Langlands.Correspondence.SupercuspidalSpecification
import Langlands.Representation.Classification.MultisegmentHeadClassificationProof
import Langlands.Representation.RankinSelberg.SquareIntegrablePoleOrderCharacterizationProof
import Langlands.Representation.RankinSelberg.SupercuspidalLFactorCharacterizationProof
import Langlands.Representation.RankinSelberg.SupercuspidalLocalConverseProof
import Langlands.LocalFactor.NonabelianUniquenessProof
import Langlands.HarmonicAnalysis.PadicUnitaryAdditiveCharacterExistsProof

/-!
# The full correspondence from a supercuspidal correspondence

Over every p-adic field, a supercuspidal correspondence yields exactly one full
correspondence (after Henniart 2002, Theorem 1.5 and Corollary 1.8). Every
ingredient is a published Library proof. The supercuspidal correspondence itself
remains a hypothesis here.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

/-- Over every p-adic field `F`, if a supercuspidal correspondence exists, then
there is exactly one full correspondence (statement only). -/
def FullCorrespondenceFromSupercuspidalExistenceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{uF} p),
    SupercuspidalCorrespondenceExistence.{uF, uP, uA} F →
      FullCorrespondenceExistsUnique.{uF, uP, uA} F

section PerField

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Specialize both pair-factor conditions to one nontrivial additive character,
retaining the same local-constant system and its base reciprocity witness. -/
theorem fullFactorCompatibilityAt_of_fullFactorCompatibility
    (e : ReciprocityCandidate F) (ψ : NontrivialAdditiveCharacter F)
    (c : FullMap.{uF, uP, uA} F) (h : FullFactorCompatibility F e c) :
    FullFactorCompatibilityAt F e ψ c := by
  rcases h.2 with ⟨eC, ε, hε, heC, hpair⟩
  exact ⟨h.1 ψ, eC, ε, hε, heC, hpair ψ⟩

/-- The full characterization over one field from supercuspidal extension and
the L-factor characterization of assembly. -/
theorem fullCharacterization_of_extends_of_lCharacterization
    (hext : FullCharacterizationExtendsStatement.{uF, uP, uA} F)
    (hLc : AssemblyLCharacterizationStatement.{uF, uP, uA} F) :
    FullCharacterizationStatement.{uF, uP, uA} F := by
  intro c0 τ ψ e hc0 he h1 hfac
  exact hLc c0 τ ψ hc0 (hext c0 τ ψ e hc0 he h1 hfac)
    (fun k j _ D D' _ _ => hfac.1 k j D D')

/-- Conditional per-field synthesis. Character existence is proved in the
imported harmonic-analysis module; it is not an additional hypothesis. -/
theorem fullCorrespondenceExistsUnique_of_henniartPrerequisites
    (hSupercuspidal : SupercuspidalCorrespondenceExistence.{uF, uP, uA} F)
    (hAssembly : ConditionalAssemblyStatement.{uF, uP, uA} F)
    (hCharacterization : FullCharacterizationStatement.{uF, uP, uA} F) :
    FullCorrespondenceExistsUnique.{uF, uP, uA} F := by
  obtain ⟨c0, hc0⟩ := hSupercuspidal
  obtain ⟨⟨c, hc⟩, hfull⟩ := hAssembly c0 hc0
  refine ⟨c, hfull c hc, ?_⟩
  intro τ hτ
  obtain ⟨e, he, hRankOne, _, _, hFactors⟩ := hτ.2.2
  obtain ⟨ψ⟩ :=
    HarmonicAnalysis.padicUnitaryAdditiveCharacterExists F F.canonicalTopologicalData
  have hAt : FullFactorCompatibilityAt F e ψ τ :=
    fullFactorCompatibilityAt_of_fullFactorCompatibility F e ψ τ hFactors
  exact ((hCharacterization c0 τ ψ e hc0 he hRankOne hAt).2 c hc).symm

/-- The full correspondence over one field from a supercuspidal correspondence
over that field. Assembly (Henniart 2002, Theorem 1.5), its L-factor
characterization (Theorem 1.8) and supercuspidal extension (Corollary 1.6) are
assembled here from their published ingredient proofs. -/
theorem fullCorrespondenceExistsUnique_of_supercuspidalExistence
    (hSupercuspidal : SupercuspidalCorrespondenceExistence.{uF, uP, uA} F) :
    FullCorrespondenceExistsUnique.{uF, uP, uA} F := by
  have hAssembly : ConditionalAssemblyStatement.{uF, uP, uA} F :=
    conditionalAssembly_of_fivePrerequisites F (assemblyWellDefined F)
      (assemblyBijective F) (assemblyOperation F) (assemblyLInheritance F)
      (assemblyEpsilonInheritance F)
  have hLc : AssemblyLCharacterizationStatement.{uF, uP, uA} F :=
    assemblyLCharacterization_of_ingredients (F := F)
      ⟨assemblyWellDefined F, assemblyBijective F, assemblyLInheritance F,
        RankinSelberg.squareIntegrablePoleOrderCharacterization,
        assemblySquareIntegrablePreimage_of_headClassification F
          (Classification.multisegmentHeadClassification F F.canonicalTopologicalData)⟩
  have hext : FullCharacterizationExtendsStatement.{uF, uP, uA} F :=
    fullCharacterizationExtends_of_inputs (F := F) RankinSelberg.supercuspidalLocalConverse
      RankinSelberg.supercuspidalLFactorCharacterization
      (fun eC => LocalFactor.NonabelianSystem.unique F eC)
  exact fullCorrespondenceExistsUnique_of_henniartPrerequisites F hSupercuspidal hAssembly
    (fullCharacterization_of_extends_of_lCharacterization F hext hLc)

end PerField

/-- Over every p-adic field, supercuspidal existence gives exactly one full
correspondence. -/
theorem fullCorrespondenceFromSupercuspidalExistence :
    FullCorrespondenceFromSupercuspidalExistenceStatement.{uF, uP, uA} :=
  fun _ _ F => fullCorrespondenceExistsUnique_of_supercuspidalExistence F

/-- The full correspondence from the supercuspidal correspondence, with
independent field, parameter-carrier and representation-carrier universes. Only
the existence part of the hypothesis is used. -/
theorem fullCorrespondenceStatement_of_supercuspidalCorrespondence
    (hsc : SupercuspidalCorrespondenceStatement.{uF, uP, uA}) :
    FullCorrespondenceStatement.{uF, uP, uA} :=
  fun p _ F => fullCorrespondenceFromSupercuspidalExistence p F (hsc p F).exists

end Langlands.Correspondence

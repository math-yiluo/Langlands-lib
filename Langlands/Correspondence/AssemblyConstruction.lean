import Langlands.Correspondence.AssemblyTheorems
import Langlands.Correspondence.AssemblyLFactorStatement

/-!
# Assembly construction from the published prerequisite propositions

Pointwise choice constructs the unique assembly from well-definedness.
The four inheritance propositions then supply the full correspondence
predicate. All five mathematical prerequisites remain explicit inputs.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- Choose the unique assembled class at every positive rank and parameter. -/
def assemblyOfWellDefined
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) : FullMap.{uF, uP, uA} F :=
  fun n D => Classical.choose (hwell c0 n D)

/-- The chosen family satisfies the original assembly relation. -/
theorem assemblyOfWellDefined_isAssemblyOf
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) :
    IsAssemblyOf F c0 (assemblyOfWellDefined F hwell c0) := by
  intro n D
  exact (Classical.choose_spec (hwell c0 n D)).1

/-- Pointwise uniqueness of assembled classes makes any two assemblies equal. -/
theorem IsAssemblyOf.eq_of_wellDefined
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    {c0 : SupercuspidalMap.{uF, uP, uA} F}
    {c c' : FullMap.{uF, uP, uA} F}
    (hc : IsAssemblyOf F c0 c) (hc' : IsAssemblyOf F c0 c') : c = c' := by
  apply fullMap_ext F
  intro n D
  obtain ⟨π, _, hπ⟩ := hwell c0 n D
  exact (hπ (c n D) (hc n D)).trans (hπ (c' n D) (hc' n D)).symm

/-- Well-definedness gives a unique full family satisfying the assembly relation. -/
theorem existsUnique_assembly_of_wellDefined
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) :
    ∃! c : FullMap.{uF, uP, uA} F, IsAssemblyOf F c0 c := by
  refine ⟨assemblyOfWellDefined F hwell c0,
    assemblyOfWellDefined_isAssemblyOf F hwell c0, ?_⟩
  intro c hc
  exact IsAssemblyOf.eq_of_wellDefined F hwell hc
    (assemblyOfWellDefined_isAssemblyOf F hwell c0)

/-- Every assembly is a full correspondence once the four inheritance
propositions are supplied. The reciprocity candidate is taken from `c0`. -/
theorem isFullCorrespondence_of_assembly_inheritance
    (hbij : AssemblyBijectiveStatement.{uF, uP, uA} F)
    (hops : AssemblyOperationStatement.{uF, uP, uA} F)
    (hL : AssemblyLInheritanceStatement.{uF, uP, uA} F)
    (hε : AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F)
    (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (hc0 : IsSupercuspidalCorrespondence F c0) (hc : IsAssemblyOf F c0 c) :
    IsFullCorrespondence F c := by
  obtain ⟨e, he, h1, hdet, htwist, _⟩ := hc0.2.2
  obtain ⟨h1c, hdetc, htwistc, hdualc⟩ :=
    hops c0 c e hc he h1 hdet htwist hc0.2.1
  exact ⟨hbij c0 c hc0.1 hc, hdualc, e, he, h1c, hdetc, htwistc,
    hL c0 c hc0 hc, hε c0 c e hc0 hc he⟩

/-- The five published prerequisite propositions imply the unchanged conditional
assembly target. This implication does not discharge those prerequisites. -/
theorem conditionalAssembly_of_fivePrerequisites
    (hwell : AssemblyWellDefinedStatement.{uF, uP, uA} F)
    (hbij : AssemblyBijectiveStatement.{uF, uP, uA} F)
    (hops : AssemblyOperationStatement.{uF, uP, uA} F)
    (hL : AssemblyLInheritanceStatement.{uF, uP, uA} F)
    (hε : AssemblyEpsilonInheritanceStatement.{uF, uP, uA} F) :
    ConditionalAssemblyStatement.{uF, uP, uA} F := by
  intro c0 hc0
  refine ⟨⟨assemblyOfWellDefined F hwell c0,
    assemblyOfWellDefined_isAssemblyOf F hwell c0⟩, ?_⟩
  intro c hc
  exact isFullCorrespondence_of_assembly_inheritance F hbij hops hL hε c0 c hc0 hc

end Langlands.Correspondence

import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Smooth.SmallRealizationProof
import Langlands.Representation.Induction.BlockEquivalence
import Langlands.Representation.Category.UniverseLiftPadic

/-!
# Changing the carriers of Langlands blocks

Pointwise actual representation equivalences transport tempered and essentially
square-integrable Langlands data without changing their ranks or exponents.
The resulting standard modules are equivalent, including across universes.
-/

noncomputable section

namespace Langlands.PadicField.TopologicalData

universe uF uV uW uX

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData} {n : ℕ}

namespace TemperedLanglandsDatum

variable (d : TemperedLanglandsDatum.{uV, uF} T n)
  (b : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (d.shape.size i) F.Carrier))
  (E : letI := T.topology
    ∀ i, (d.blocks i).representation.Equiv (b i).representation)

/-- Replace the blocks by equivalent actions, preserving shape and exponents. -/
def withBlocks : TemperedLanglandsDatum.{uW, uF} T n where
  shape := d.shape
  blocks := b
  irreducible i := (isIrreducible_iff_of_equiv (E i)).mp (d.irreducible i)
  tempered i := (T.isTempered_iff_of_equiv (E i)).mp (d.tempered i)
  exponent := d.exponent
  strictAnti := d.strictAnti

/-- The standard module transports the pointwise equivalences of twisted blocks. -/
def withBlocksStandardModuleEquiv :
    letI := T.topology
    d.standardModule.representation.Equiv (d.withBlocks b E).standardModule.representation := by
  letI := T.topology
  exact T.normalizedProductInducedEquiv d.shape
    (σ := fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).representation)
    (τ := fun i => (T.twistedBlocks d.shape b d.exponent i).representation)
    (fun i => twistEquiv _ (E i))

/-- Lift every block carrier, retaining the original ranks and real exponents. -/
def universeLift : TemperedLanglandsDatum.{max uX uV, uF} T n :=
  letI := T.topology
  d.withBlocks (fun i => SmoothRep.universeLift.{uX} (d.blocks i))
    (fun i => SmoothRep.universeLiftEquiv (d.blocks i))

/-- The lifted datum has the same actual standard module up to equivalence. -/
def universeLiftStandardModuleEquiv :
    letI := T.topology
    d.standardModule.representation.Equiv
      (d.universeLift.{uF, uV, uX}).standardModule.representation :=
  d.withBlocksStandardModuleEquiv _ _

/-- Every tempered datum admits equivalent blocks in any prescribed universe.
Only the individual irreducible blocks are realized on small carriers. -/
theorem exists_realization :
    letI := T.topology
    ∃ e : TemperedLanglandsDatum.{uW, uF} T n,
      e.shape = d.shape ∧ HEq e.exponent d.exponent ∧
        Nonempty (d.standardModule.representation.Equiv e.standardModule.representation) := by
  let := T.topology
  choose b _ E using fun i => padicIrreducibleSmoothSmallRealization.{uF, uV, uW}
    p F T (d.shape.size i) (d.blocks i) (d.irreducible i)
  exact ⟨d.withBlocks b (fun i => (E i).some), rfl, HEq.rfl,
    ⟨d.withBlocksStandardModuleEquiv b (fun i => (E i).some)⟩⟩

end TemperedLanglandsDatum

namespace SquareIntegrableLanglandsDatum

variable (d : SquareIntegrableLanglandsDatum.{uV, uF} T n)
  (b : letI := T.topology
    ∀ i, SmoothRep.{0, uF, uW} ℂ (GeneralLinear (d.shape.size i) F.Carrier))
  (E : letI := T.topology
    ∀ i, (d.blocks i).representation.Equiv (b i).representation)

/-- Replace the blocks and transport their actual invariant positive forms. -/
def withBlocks : SquareIntegrableLanglandsDatum.{uW, uF} T n where
  shape := d.shape
  blocks := b
  irreducible i := (isIrreducible_iff_of_equiv (E i)).mp (d.irreducible i)
  essentiallySquareIntegrable i :=
    (T.isEssentiallySquareIntegrable_iff_of_equiv (E i)).mp (d.essentiallySquareIntegrable i)
  unitaryExponent i := (d.unitaryExponent i).ofEquiv (E i)
  antitone := d.antitone

/-- Equivalent block actions give equivalent actual normalized inductions. -/
def withBlocksInducedEquiv :
    letI := T.topology
    d.induced.representation.Equiv (d.withBlocks b E).induced.representation := by
  letI := T.topology
  exact T.normalizedProductInducedEquiv d.shape E

/-- Lift every essentially square-integrable block and its unitary exponent data. -/
def universeLift : SquareIntegrableLanglandsDatum.{max uX uV, uF} T n :=
  letI := T.topology
  d.withBlocks (fun i => SmoothRep.universeLift.{uX} (d.blocks i))
    (fun i => SmoothRep.universeLiftEquiv (d.blocks i))

/-- The lifted square-integrable datum induces an equivalent representation. -/
def universeLiftInducedEquiv :
    letI := T.topology
    d.induced.representation.Equiv
      (d.universeLift.{uF, uV, uX}).induced.representation :=
  d.withBlocksInducedEquiv _ _

end SquareIntegrableLanglandsDatum

end Langlands.PadicField.TopologicalData

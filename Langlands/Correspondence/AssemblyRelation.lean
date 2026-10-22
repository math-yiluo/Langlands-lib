import Langlands.Correspondence.OperationCompatibility
import Langlands.Representation.Classification.LanglandsData
import Langlands.WeilDeligne.SpecialBlocks
import Langlands.WeilDeligne.DirectSum

/-!
# Assembly of a full correspondence from a supercuspidal one

A parameter `⊕_i σ_i ⊗ Sp(m_i)` is sent to the Langlands head of the multisegment
of segments `[c0 σ_i, ν^(m_i - 1) c0 σ_i]`. The assembly is a relation between
parameter classes and representation classes, defined from the published block,
segment and Langlands-head relations. Its well-definedness, bijectivity, extension
and inherited compatibilities are propositions only.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

/-- The cuspidal datum of the supercuspidal class `c0 σ` of rank `d + 1`. -/
def cuspidalDatumOf (c0 : SupercuspidalMap.{uF, uP, uA} F) {d : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) :
    CuspidalDatum.{uA, uF} F.canonicalTopologicalData where
  rank := d + 1
  rank_pos := Nat.succ_pos d
  cls := c0 d.succPNat σ

/-- The segment `[c0 σ, ν c0 σ, …, ν^m c0 σ]` of length `m + 1`. -/
def segmentOf (c0 : SupercuspidalMap.{uF, uP, uA} F) {d : ℕ}
    (σ : IrreducibleWeilClass.{uF, uP} F d.succPNat) (m : ℕ) :
    Segment.{uA, uF} F.canonicalTopologicalData where
  base := cuspidalDatumOf F c0 σ
  length := m + 1
  length_pos := Nat.succ_pos m

/-- The multisegment of the segments `[c0 σ_i, ν^(m_i) c0 σ_i]`. -/
def multisegmentOf (c0 : SupercuspidalMap.{uF, uP, uA} F) {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ) :
    Multisegment.{uA, uF} F.canonicalTopologicalData :=
  (List.ofFn fun i => segmentOf F c0 (σ i) (m i) : Multiset _)

/-- `D` is the class of the block sum `⊕_i σ_i ⊗ Sp(m_i + 1)`: the published
uncentered special blocks on representatives of the irreducible Weil classes `σ_i`. -/
def IsBlockSum {r : ℕ} {d : Fin r → ℕ}
    (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat) (m : Fin r → ℕ)
    {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) : Prop :=
  ∃ (B : Fin r → Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (A : Weil.Local.LocalWeilDeligneRepresentation.{uF, uP} F),
    (∀ i, FiniteRepresentation.classOf (B i) = weilClassForget F (σ i)) ∧
    WeilDeligneRepresentation.classOf A = parameterForget F D ∧
    Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.directSum fun i =>
        WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
          (B i) (m i + 1)) A)

/-- `π` is the class of the Langlands head of `multisegmentOf F c0 σ m`: some
representative of `π` is equivalent to a representation that is the published
`Multisegment.IsLanglandsHead` of that multisegment. -/
def IsMultisegmentHeadClass (c0 : SupercuspidalMap.{uF, uP, uA} F) {r : ℕ}
    {d : Fin r → ℕ} (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat)
    (m : Fin r → ℕ) {n : ℕ+} (π : AutomorphicClass.{uF, uA} F n) : Prop :=
  ∃ (A : AutomorphicObject.{uF, uA} F n)
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (n : ℕ) F.Carrier)),
    automorphicClassOf F A = π ∧
      (multisegmentOf F c0 σ m).IsLanglandsHead J ∧
      Nonempty (J.representation.Equiv A.obj.representation)

/-- The assembly relation: for some block decomposition `D = ⊕_i σ_i ⊗ Sp(m_i + 1)`,
`π` is the Langlands head of the multisegment of the segments of length `m_i + 1`
beginning at `c0 σ_i`. All decomposition data are existential. -/
def IsAssembledFrom (c0 : SupercuspidalMap.{uF, uP, uA} F) {n : ℕ+}
    (D : WeilDeligneClass.{uF, uP} F n) (π : AutomorphicClass.{uF, uA} F n) : Prop :=
  ∃ (r : ℕ) (d m : Fin r → ℕ) (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat),
    IsBlockSum F σ m D ∧ IsMultisegmentHeadClass F c0 σ m π

/-- The full map `c` is the assembly of `c0`. -/
def IsAssemblyOf (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F) :
    Prop :=
  ∀ (n : ℕ+) (D : WeilDeligneClass.{uF, uP} F n), IsAssembledFrom F c0 D (c n D)

/-- Well-definedness (statement only): for every supercuspidal map, every parameter
class is assembled to exactly one class. This contains the independence of the
block decomposition, of the order of the blocks and of the Langlands ordering. -/
def AssemblyWellDefinedStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (n : ℕ+) (D : WeilDeligneClass.{uF, uP} F n),
    ∃! π : AutomorphicClass.{uF, uA} F n, IsAssembledFrom F c0 D π

/-- Exhaustion and injectivity (statement only): the assembly of a rankwise bijective
supercuspidal map is rankwise bijective. -/
def AssemblyBijectiveStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F),
    SupercuspidalRankwiseBijective F c0 → IsAssemblyOf F c0 c → RankwiseBijective F c

/-- Extension (statement only): the assembly agrees with `c0` on irreducible Weil
classes, through the zero-monodromy and supercuspidal inclusions. -/
def AssemblyExtendsStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F),
    IsAssemblyOf F c0 c → ExtendsSupercuspidal F c0 c

/-- Inherited operation compatibilities (statement only): if `c0` is compatible with
rank one, determinants, twists and duals for a geometrically normalized `e`, so is
its assembly. -/
def AssemblyOperationStatement : Prop :=
  ∀ (c0 : SupercuspidalMap.{uF, uP, uA} F) (c : FullMap.{uF, uP, uA} F)
    (e : ReciprocityCandidate F),
    IsAssemblyOf F c0 c → IsGeometricReciprocity F e →
      SupercuspidalRankOneCompatibility F e c0 →
      SupercuspidalDeterminantCompatibility F e c0 →
      SupercuspidalTwistCompatibility F e c0 →
      SupercuspidalDualCompatibility F c0 →
        RankOneCompatibility F e c ∧ DeterminantCompatibility F e c ∧
          TwistCompatibility F e c ∧ DualCompatibility F c

end Langlands.Correspondence

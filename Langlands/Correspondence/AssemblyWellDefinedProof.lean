import Langlands.Correspondence.AssemblyUniqueness
import Langlands.WeilDeligne.ParameterNormalFormProof
import Langlands.Weil.Local.ContinuityProof
import Langlands.Representation.Classification.MultisegmentConstituentDataExistenceProof
import Langlands.Representation.Classification.OrderedMultisegmentHeadExistenceProof
import Langlands.Representation.Smooth.Admissibility.FiniteLengthProof
import Langlands.Representation.Smooth.IrreducibleRealization

/-!
# Well-definedness of the assembly

Every parameter class is assembled from a supercuspidal map to exactly one
automorphic class. Existence: a representative of the parameter class is a sum of
special blocks on irreducible Weil representations (published block normal form);
the multisegment of the blocks has a Langlands head (published ordered head
existence); the head has an irreducible admissible realization with carriers in
`uA` (published small realization and finite-length admissibility). Uniqueness is
the published `isAssembledFrom_unique`.
-/

noncomputable section

namespace Langlands.Correspondence

universe uF uP uA

open PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

local instance assemblyWellDefinedFieldTopology : TopologicalSpace F.Carrier :=
  F.canonicalTopologicalData.topology

local instance assemblyWellDefinedGeneralLinearTopology (n : ℕ) :
    TopologicalSpace (GeneralLinear n F.Carrier) :=
  F.canonicalGeneralLinearTopology n

namespace AssemblyWellDefined

/-- An irreducible local Weil representation has positive rank. -/
theorem rank_pos_of_isIrreducible {B : Weil.Local.LocalWeilRepresentation.{uF, uP} F}
    (hB : B.IsIrreducible) : 0 < B.rank := by
  have : IsSimpleModule (MonoidAlgebra ℂ (Weil.Local.localWeilGroup F))
      B.representation.asModule :=
    (Representation.irreducible_iff_isSimpleModule_asModule _).mp hB
  have : Nontrivial B :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (Weil.Local.localWeilGroup F))
      B.representation.asModule
  exact Module.finrank_pos

/-- The irreducible Weil class of a continuous irreducible representation `B`, in
rank `(B.rank - 1) + 1 = B.rank`. -/
def irreducibleClassOf (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hB : B.IsContinuous ∧ B.IsIrreducible) :
    IrreducibleWeilClass.{uF, uP} F (B.rank - 1).succPNat :=
  ⟨Quotient.mk _ ⟨B, hB⟩, by
    change B.rank = B.rank - 1 + 1
    have := rank_pos_of_isIrreducible F hB.2
    omega⟩

/-- `B` represents its irreducible Weil class. -/
theorem weilClassForget_irreducibleClassOf (B : Weil.Local.LocalWeilRepresentation.{uF, uP} F)
    (hB : B.IsContinuous ∧ B.IsIrreducible) :
    FiniteRepresentation.classOf B = weilClassForget F (irreducibleClassOf F B hB) :=
  rfl

/-- Every parameter class is a block sum `⊕_i σ_i ⊗ Sp(m_i + 1)` of uncentered special
blocks on irreducible Weil classes. -/
theorem exists_isBlockSum {n : ℕ+} (D : WeilDeligneClass.{uF, uP} F n) :
    ∃ (r : ℕ) (d m : Fin r → ℕ) (σ : ∀ i, IrreducibleWeilClass.{uF, uP} F (d i).succPNat),
      IsBlockSum F σ m D := by
  obtain ⟨⟨A, hA⟩, hAD⟩ := Quotient.exists_rep D.val
  have : CompactSpace (Weil.Local.localDegree F).toMonoidHom.ker :=
    isCompact_iff_compactSpace.mp (Weil.Local.localInertia_isCompact F)
  obtain ⟨k, b, hb, ⟨e⟩⟩ := WeilDeligneRepresentation.ParameterNormalForm.exists_blocks
    (Weil.Local.localNormCharacter F).toMonoidHom (Weil.Local.localDegree F).toMonoidHom
    WeilDeligneRepresentation.Blocks.decompositionExistence.{uF, uP}
    (Weil.Local.localDegree_surjective F) A hA
  have hc : ∀ i, (b i).representation.IsContinuous ∧ (b i).representation.IsIrreducible :=
    fun i => ⟨((Weil.Local.localWeilContinuity F (b i).representation).2.2.1).mpr (hb i).2,
      (hb i).1⟩
  have hblock : ∀ i, Nonempty (WeilDeligneRepresentation.Equiv
      (WeilDeligneRepresentation.block (Weil.Local.localNormCharacter F).toMonoidHom
        (b i).representation ((b i).length - 1 + 1))
      ((b i).pair (Weil.Local.localNormCharacter F).toMonoidHom)) := by
    intro i
    rw [Nat.sub_add_cancel (b i).length_pos]
    exact ⟨WeilDeligneRepresentation.Equiv.refl _⟩
  refine ⟨k, fun i => (b i).representation.rank - 1, fun i => (b i).length - 1,
    fun i => irreducibleClassOf F (b i).representation (hc i), fun i => (b i).representation,
    A, fun i => weilClassForget_irreducibleClassOf F _ (hc i), ?_,
    ⟨(WeilDeligneRepresentation.directSumEquiv fun i => (hblock i).some).trans e.symm⟩⟩
  change _ = WeilDeligneRepresentation.frobeniusSemisimpleClassForget _ _ D.val
  rw [← hAD]
  rfl

/-- A multisegment with carriers in `uV` and degree `n` has a Langlands head on
`GL_n(F)` with carriers in `max uF uV`. -/
theorem exists_isLanglandsHead (a : Multisegment.{uA, uF} F.canonicalTopologicalData) {n : ℕ}
    (hn : a.degree = n) :
    ∃ J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier), a.IsLanglandsHead J := by
  have key : ∀ (b : Multisegment.{max uF uA, uF} F.canonicalTopologicalData) {n : ℕ},
      b.degree = n →
        ∃ J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear n F.Carrier), b.IsLanglandsHead J := by
    intro b n hb
    subst hb
    obtain ⟨-, d, hd, hord, hheads⟩ :=
      Classification.multisegmentConstituentDataExistence.{uF, uA} F F.canonicalTopologicalData b
    obtain ⟨J, hJ⟩ := Classification.orderedMultisegmentHeadExistence.{uF, uA} F
      F.canonicalTopologicalData b.degree d hord hheads
    exact ⟨J, d, hd, hJ⟩
  obtain ⟨J, hJ⟩ := key a.universeLift ((Multisegment.universeLift_degree a).trans hn)
  exact ⟨J, (Multisegment.isLanglandsHead_universeLift_iff a J).mp hJ⟩

/-- An irreducible smooth representation of `GL_n(F)` with carriers in `max uF uA` is
equivalent to the representation of an automorphic object with carriers in `uA`. -/
theorem exists_automorphicObject {n : ℕ+}
    (J : SmoothRep.{0, uF, max uF uA} ℂ (GeneralLinear (n : ℕ) F.Carrier))
    (hJ : J.IsIrreducible) :
    ∃ A : AutomorphicObject.{uF, uA} F n, Nonempty (J.representation.Equiv A.obj.representation) := by
  obtain ⟨τ, hτ, ⟨e⟩⟩ := padicIrreducibleSmoothSmallRealization.{uF, max uF uA, uA} p F
    F.canonicalTopologicalData n J hJ
  have hadm : τ.IsAdmissible := glFiniteLengthAdmissibility.{uF, uA} F F.canonicalTopologicalData
    n τ (SmoothRep.hasFiniteLength_of_isIrreducible hτ)
  exact ⟨⟨τ, hτ, hadm⟩, ⟨e⟩⟩

/-- Existence of the assembly: every parameter class is assembled from `c0` to some
automorphic class. -/
theorem exists_isAssembledFrom (c0 : SupercuspidalMap.{uF, uP, uA} F) {n : ℕ+}
    (D : WeilDeligneClass.{uF, uP} F n) : ∃ π, IsAssembledFrom F c0 D π := by
  obtain ⟨r, d, m, σ, hB⟩ := exists_isBlockSum F D
  have hdeg : (multisegmentOf F c0 σ m).degree = (n : ℕ) := by
    rw [degree_multisegmentOf, ← hB.rank_eq]
  obtain ⟨J, hJ⟩ := exists_isLanglandsHead F (multisegmentOf F c0 σ m) hdeg
  have hirr : J.IsIrreducible := by
    obtain ⟨-, -, -, -, hirr, -⟩ := hJ
    exact hirr
  obtain ⟨A, hA⟩ := exists_automorphicObject F J hirr
  exact ⟨automorphicClassOf F A, r, d, m, σ, hB, A, J, rfl, hJ, hA⟩

end AssemblyWellDefined

/-- Well-definedness of the assembly: for every supercuspidal map, every parameter class
is assembled to exactly one automorphic class. -/
theorem assemblyWellDefined : AssemblyWellDefinedStatement.{uF, uP, uA} F := by
  intro c0 n D
  obtain ⟨π, hπ⟩ := AssemblyWellDefined.exists_isAssembledFrom F c0 D
  exact ⟨π, hπ, fun π' hπ' => isAssembledFrom_unique F c0 hπ' hπ⟩

end Langlands.Correspondence

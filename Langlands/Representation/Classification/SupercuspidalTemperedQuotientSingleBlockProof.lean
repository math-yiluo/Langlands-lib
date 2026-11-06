import Langlands.Representation.Classification.SupercuspidalTemperedQuotientSingleBlockStatement
import Langlands.Representation.Classification.RegularLanglandsHeadReduction
import Langlands.Representation.Parabolic.SecondAdjointnessProof
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.CuspidalSupport.JacquetVanishingSubgroups
import Langlands.Representation.CuspidalSupport.AssociationReduction
import Langlands.Representation.Filtration.LengthTwoMatching
import Langlands.Group.GL.ReverseBlocks
import Langlands.Representation.Tensor.FiniteProperties

/-!
# Supercuspidal Langlands quotients come from one-block data

A supercuspidal representation has zero opposite Jacquet module for every
proper block shape. By second adjointness it receives no nonzero intertwiner
from a properly induced admissible representation. Hence a supercuspidal
Langlands quotient of a tempered standard module has a one-block datum, and the
standard module is then equivalent to it.
-/

noncomputable section

namespace Langlands

universe uF uV uW

open GeneralLinear

namespace GeneralLinear

variable {F : Type uF} [Field F] [TopologicalSpace F] {n : ℕ}
  {V : Type uV} [AddCommGroup V] [Module ℂ V]

/-- A supercuspidal representation has zero coinvariants for the opposite
radical of every proper standard block parabolic: that radical is a conjugate
of the upper radical of the reversed shape. -/
theorem IsSupercuspidal.subsingleton_oppositeCoinvariants
    {ρ : Representation ℂ (GeneralLinear n F) V} (hρ : IsSupercuspidal ρ)
    (B : BlockShape n) (hB : B.parabolic F ≠ ⊤) :
    Subsingleton (Jacquet.Coinvariants ρ (B.oppositeUnipotentSubgroup F)) := by
  have hrev : B.reverse.parabolic F ≠ ⊤ := (B.reverse_parabolic_ne_top_iff F).mpr hB
  have hvan := hρ.2 B.reverse hrev (B.reverseMatrix F)
  change Subsingleton (Jacquet.Coinvariants ρ
    ((B.reverse.unipotentSubgroup F).map
      (MulAut.conj (B.reverseMatrix F)).toMonoidHom)) at hvan
  rwa [B.reverse_unipotentSubgroup_map_conj F] at hvan

end GeneralLinear

namespace PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Second adjointness: every intertwiner from a properly induced admissible
representation to a supercuspidal representation is zero. -/
theorem normalizedParabolicInduced_intertwiningMap_eq_zero_of_isSupercuspidal
    {n : ℕ} (hn : 0 < n) (B : BlockShape n) (hB : B.parabolic F.Carrier ≠ ⊤)
    (σ : Rep.{uV} ℂ (B.Levi F.Carrier))
    (hσ : letI := T.topology; IsAdmissible σ.ρ)
    (π : Rep.{uW} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; IsSupercuspidal π.ρ)
    (f : letI := T.topology
      (T.normalizedParabolicInduced B σ.ρ).IntertwiningMap π.ρ) :
    f = 0 := by
  let := T.topology
  obtain ⟨E, -, -⟩ := Parabolic.normalizedSecondAdjointness.{uF, uV, uW}.1 p F T n hn B
  have hsub : Subsingleton (CuspidalJacquetMultiplicity.oppositeJacquet T B π) :=
    hπ.subsingleton_oppositeCoinvariants B hB
  have hE : E σ π hσ hπ.1 f = 0 := by
    ext v
    exact Subsingleton.elim _ _
  exact (LinearEquiv.map_eq_zero_iff _).mp hE

namespace TemperedLanglandsDatum

variable {T} {n : ℕ} (d : T.TemperedLanglandsDatum.{uV, uF} n)

/-- A supercuspidal Langlands quotient of a tempered standard module of
positive rank forces the datum to have exactly one block. -/
theorem shape_length_eq_one_of_isSupercuspidal (hn : 0 < n)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; IsSupercuspidal π.representation)
    (hq : d.IsLanglandsQuotient π) : d.shape.length = 1 := by
  let := T.topology
  obtain ⟨hirr, q, hqs⟩ := hq
  have htop : d.shape.parabolic F.Carrier = ⊤ := by
    by_contra hB
    have hσ : IsAdmissible (d.shape.blockTensor
        (fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).representation)) :=
      FiniteTensor.isAdmissible_external _ (fun i =>
        (RegularHeadExistence.twistedBlock_admissible_finiteLength T d i).1)
    have h0 : q = 0 :=
      T.normalizedParabolicInduced_intertwiningMap_eq_zero_of_isSupercuspidal hn d.shape hB
        (Rep.of (d.shape.blockTensor
          (fun i => (T.twistedBlocks d.shape d.blocks d.exponent i).representation)))
        hσ (Rep.of π.representation) hπ q
    have hnt : Nontrivial π := by
      have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
          π.representation.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
      have : Nontrivial π.representation.asModule :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
          π.representation.asModule
      exact π.representation.asModuleEquiv.toEquiv.symm.nontrivial
    obtain ⟨w, hw⟩ := exists_ne (0 : π)
    obtain ⟨v, rfl⟩ := hqs w
    apply hw
    rw [h0]
    rfl
  have hsub := CuspidalSupport.block_indices_subsingleton_of_parabolic_eq_top d.shape htop
  have hpos : 0 < d.shape.length := by
    by_contra h0
    have hl : d.shape.length = 0 := by omega
    have hsum := d.shape.sum_eq
    have : (∑ i : Fin d.shape.length, d.shape.size i) = 0 := by
      rw [Finset.sum_eq_zero]
      intro i _
      exact absurd i.isLt (by omega)
    omega
  by_contra hne
  have h01 : (⟨0, hpos⟩ : Fin d.shape.length) = ⟨1, by omega⟩ := Subsingleton.elim _ _
  simp at h01

/-- A supercuspidal Langlands quotient of a tempered standard module of
positive rank is equivalent to the standard module itself. -/
theorem nonempty_standardModule_equiv_of_isSupercuspidal (hn : 0 < n)
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (hπ : letI := T.topology; IsSupercuspidal π.representation)
    (hq : d.IsLanglandsQuotient π) :
    letI := T.topology
    Nonempty (d.standardModule.representation.Equiv π.representation) := by
  let := T.topology
  have hB : d.shape.length = 1 := d.shape_length_eq_one_of_isSupercuspidal hn hπ hq
  obtain ⟨hirr, q, hqs⟩ := hq
  let i : Fin d.shape.length := d.shape.singleBlockIndex hB
  let τ := fun j => (T.twistedBlocks d.shape d.blocks d.exponent j).representation
  have hτ : ∀ j, IsSmooth (τ j) := fun j =>
    (T.twistedBlocks d.shape d.blocks d.exponent j).isSmooth
  let e := T.singleBlockNormalizedProductEquiv d.shape hB τ hτ i
  have hτi : Representation.IsIrreducible ((τ i).comp
      (GeneralLinear.reindex (R := F.Carrier)
        (finCongr (d.shape.singleBlock_size hB i))).symm.toMonoidHom) :=
    (CuspidalSupport.isIrreducible_comp_mulEquiv_iff (τ i) _).mpr
      (RegularHeadExistence.twistedBlock_irreducible T d i)
  have hstd : Representation.IsIrreducible d.standardModule.representation :=
    LengthTwo.isIrreducible_of_equiv e.symm hτi
  have hq0 : q ≠ 0 := by
    intro h0
    have hnt : Nontrivial π := by
      have : IsSimpleModule (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
          π.representation.asModule :=
        (Representation.irreducible_iff_isSimpleModule_asModule _).mp hirr
      have : Nontrivial π.representation.asModule :=
        IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
          π.representation.asModule
      exact π.representation.asModuleEquiv.toEquiv.symm.nontrivial
    obtain ⟨w, hw⟩ := exists_ne (0 : π)
    obtain ⟨v, rfl⟩ := hqs w
    apply hw
    rw [h0]
    rfl
  have hbij := (Representation.IsIrreducible.bijective_or_eq_zero q).resolve_right hq0
  exact ⟨Representation.IntertwiningMap.ofBijective q hbij⟩

end TemperedLanglandsDatum

end PadicField.TopologicalData

namespace Classification

/-- A supercuspidal Langlands quotient of a tempered standard module of
`GL_(n+1)(F)` has a one-block datum. -/
theorem supercuspidalTemperedQuotientSingleBlock :
    SupercuspidalTemperedQuotientSingleBlockStatement.{uF, uV} :=
  fun _ _ _ _ n d _ hq hπ =>
    d.shape_length_eq_one_of_isSupercuspidal (Nat.succ_pos n) hπ hq

end Classification

end Langlands

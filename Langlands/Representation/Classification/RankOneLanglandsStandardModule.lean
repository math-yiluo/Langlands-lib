import Langlands.Representation.Classification.LanglandsData
import Langlands.Representation.Induction.SingleBlock
import Langlands.Representation.CuspidalSupport.AssociationReduction

/-! # Single-block and rank-one tempered standard modules -/

noncomputable section

namespace Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

universe uF uV

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p}
  {T : F.TopologicalData}

/-- A tempered standard module with exactly one block is irreducible. -/
theorem standardModule_irreducible_of_length_eq_one {n : ℕ}
    (d : TemperedLanglandsDatum.{uV, uF} T n) (h : d.shape.length = 1) :
    letI := T.topology
    Representation.IsIrreducible d.standardModule.representation := by
  let := T.topology
  let i := d.shape.singleBlockIndex h
  let e := T.singleBlockNormalizedProductEquiv d.shape h
    (fun j => (T.twistedBlocks d.shape d.blocks d.exponent j).representation)
    (fun j => (T.twistedBlocks d.shape d.blocks d.exponent j).isSmooth) i
  apply (Langlands.isIrreducible_iff_of_equiv e).mpr
  apply (CuspidalSupport.isIrreducible_comp_mulEquiv_iff _ _).mpr
  exact (Langlands.isIrreducible_twist_iff _ _).mpr (d.irreducible i)

/-- Every irreducible quotient of a one-block tempered standard module is
actually equivalent to the standard module. -/
theorem nonempty_standardModule_equiv_of_length_eq_one {n : ℕ}
    (d : TemperedLanglandsDatum.{uV, uF} T n) (h : d.shape.length = 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : d.IsLanglandsQuotient π) :
    letI := T.topology
    Nonempty (d.standardModule.representation.Equiv π.representation) := by
  let := T.topology
  obtain ⟨hπirr, q, hq⟩ := hπ
  let := d.standardModule_irreducible_of_length_eq_one h
  let : Representation.IsIrreducible π.representation := hπirr
  let : Nontrivial π :=
    IsSimpleModule.nontrivial (MonoidAlgebra ℂ (GeneralLinear n F.Carrier))
      π.representation.asModule
  have hqne : q ≠ 0 := by
    intro hzero
    obtain ⟨w, hw⟩ := exists_ne (0 : π)
    obtain ⟨v, hv⟩ := hq w
    exact hw (hv.symm.trans (by rw [hzero]; rfl))
  have hinj := (Representation.IsIrreducible.injective_or_eq_zero q).resolve_right hqne
  exact ⟨q.ofBijective ⟨hinj, hq⟩⟩

/-- A block shape of total rank one necessarily has one block. -/
theorem shape_length_eq_one (d : TemperedLanglandsDatum.{uV, uF} T 1) :
    d.shape.length = 1 := by
  have hle := d.shape.length_le
  have hpos := (d.shape.coordinateBlock (0 : Fin 1)).isLt
  omega

/-- Every tempered standard module of rank one is irreducible. -/
theorem standardModule_irreducible_rankOne
    (d : TemperedLanglandsDatum.{uV, uF} T 1) :
    letI := T.topology
    Representation.IsIrreducible d.standardModule.representation :=
  d.standardModule_irreducible_of_length_eq_one d.shape_length_eq_one

/-- A rank-one Langlands quotient is equivalent to its presenting tempered
standard module, without an additional classification hypothesis. -/
theorem nonempty_standardModule_equiv_rankOne
    (d : TemperedLanglandsDatum.{uV, uF} T 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 1 F.Carrier))
    (hπ : d.IsLanglandsQuotient π) :
    letI := T.topology
    Nonempty (d.standardModule.representation.Equiv π.representation) :=
  d.nonempty_standardModule_equiv_of_length_eq_one d.shape_length_eq_one π hπ

/-- Choose an actual equivariant linear equivalence from a one-block tempered
standard module to a supplied irreducible quotient. -/
def standardModuleEquivOfLengthEqOne {n : ℕ}
    (d : TemperedLanglandsDatum.{uV, uF} T n) (h : d.shape.length = 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : d.IsLanglandsQuotient π) :
    letI := T.topology
    d.standardModule.representation.Equiv π.representation :=
  Classical.choice (d.nonempty_standardModule_equiv_of_length_eq_one h π hπ)

/-- The actual equivalence between a rank-one tempered standard module and a
supplied Langlands quotient. -/
def standardModuleEquivRankOne
    (d : TemperedLanglandsDatum.{uV, uF} T 1)
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear 1 F.Carrier))
    (hπ : d.IsLanglandsQuotient π) :
    letI := T.topology
    d.standardModule.representation.Equiv π.representation :=
  d.standardModuleEquivOfLengthEqOne d.shape_length_eq_one π hπ

end Langlands.PadicField.TopologicalData.TemperedLanglandsDatum

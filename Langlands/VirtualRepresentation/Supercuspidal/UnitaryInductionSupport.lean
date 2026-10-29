import Langlands.VirtualRepresentation.Supercuspidal.UnitarySupport

/-!
# Unitary lattice support from actual normalized induction factors

A supplied family of actual unitary supercuspidal factors determines an
effective integral support. An irreducible representation equivalent to their
normalized product has precisely this witnessed lattice support.
-/

noncomputable section

universe uF uV

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped Classical

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)
  {n : ℕ} (B : GeneralLinear.BlockShape n)

/-- The genuine positive-rank class of one supplied block factor. -/
def blockCuspidalDatum
    (σ : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (i : Fin B.length) : CuspidalDatum.{uV, uF} T where
  rank := B.size i
  rank_pos := B.positive i
  cls := letI := T.topology; (σ i).isoClass

@[simp]
theorem blockCuspidalDatum_rank
    (σ : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (i : Fin B.length) : (T.blockCuspidalDatum B σ i).rank = B.size i := rfl

/-- Package the supplied invariant-positive-form witness for each actual factor. -/
def blockUnitaryCuspidalDatum
    (σ : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (hσ : letI := T.topology
      ∀ i, IsUnitarizable (σ i).obj.representation)
    (i : Fin B.length) : UnitaryCuspidalDatum.{uF, uV} T :=
  ⟨T.blockCuspidalDatum B σ i, hσ i⟩

@[simp]
theorem blockUnitaryCuspidalDatum_val
    (σ : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (hσ : letI := T.topology
      ∀ i, IsUnitarizable (σ i).obj.representation)
    (i : Fin B.length) :
    (T.blockUnitaryCuspidalDatum B σ hσ i).val = T.blockCuspidalDatum B σ i := rfl

/-- The full integral sum of the supplied unitary supercuspidal block classes. -/
def unitaryInductionSupport
    (σ : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (hσ : letI := T.topology
      ∀ i, IsUnitarizable (σ i).obj.representation) :
    letI := T.topology
    Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier :=
  T.unitarySupportLattice
    (List.ofFn (T.blockUnitaryCuspidalDatum B σ hσ) : Multiset _)

variable
  (σ : letI := T.topology
    ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
      (F := F.Carrier) (n := B.size i))
  (hσ : letI := T.topology
    ∀ i, IsUnitarizable (σ i).obj.representation)

/-- Every coefficient is the exact multiplicity among all the supplied factors. -/
theorem unitaryInductionSupport_apply (d : UnitaryCuspidalDatum.{uF, uV} T) :
    T.unitaryInductionSupport B σ hσ (T.unitaryCuspidalDatumBasisEquiv d) =
      ((List.ofFn (T.blockUnitaryCuspidalDatum B σ hσ) : Multiset _).count d : ℤ) :=
  T.unitarySupportLattice_apply _ d

/-- Forgetting the unitary witnesses retains the complete actual class multiset. -/
theorem includeUnitary_unitaryInductionSupport :
    letI := T.topology
    Supercuspidal.includeUnitary F.Carrier (T.unitaryInductionSupport B σ hσ) =
      T.supportLattice (List.ofFn (T.blockCuspidalDatum B σ) : Multiset _) := by
  let := T.topology
  rw [unitaryInductionSupport, T.includeUnitary_unitarySupportLattice]
  simp only [Multiset.map_coe, List.map_ofFn]
  rfl

theorem unitaryInductionSupport_effective :
    T.unitaryInductionSupport B σ hσ ∈ effective :=
  T.unitarySupportLattice_effective _

/-- Degree is the ambient general linear group rank, with all multiplicities. -/
theorem unitaryInductionSupport_degree :
    letI := T.topology
    Supercuspidal.unitaryDegree F.Carrier (T.unitaryInductionSupport B σ hσ) =
      (n : ℤ) := by
  let := T.topology
  rw [unitaryInductionSupport, T.unitarySupportLattice_degree,
    Multiset.map_coe, Multiset.sum_coe, List.map_ofFn, List.sum_ofFn]
  simpa [Function.comp_def, blockUnitaryCuspidalDatum, blockCuspidalDatum] using
    congrArg (fun k : ℕ => (k : ℤ)) B.sum_eq

/-- Replacing block factors by actually isomorphic objects preserves the sum. -/
theorem unitaryInductionSupport_eq_of_iso
    (σ' : letI := T.topology
      ∀ i, GeneralLinear.SupercuspidalRep.{uF, uV}
        (F := F.Carrier) (n := B.size i))
    (hσ' : letI := T.topology
      ∀ i, IsUnitarizable (σ' i).obj.representation)
    (e : letI := T.topology
      ∀ i, σ i ≅ σ' i) :
    T.unitaryInductionSupport B σ hσ = T.unitaryInductionSupport B σ' hσ' := by
  let := T.topology
  have hd : T.blockUnitaryCuspidalDatum B σ hσ =
      T.blockUnitaryCuspidalDatum B σ' hσ' := by
    funext i
    apply Subtype.ext
    exact congrArg (CuspidalDatum.mk (B.size i) (B.positive i))
      ((GeneralLinear.SupercuspidalRep.isoClass_eq_iff (σ i) (σ' i)).mpr ⟨e i⟩)
  unfold unitaryInductionSupport
  rw [hd]

/-- An actual irreducible normalized product has the full supplied unitary support. -/
theorem isUnitaryLatticeSupport_of_normalizedProductEquiv
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (hπ : letI := T.topology; π.IsIrreducible)
    (e : letI := T.topology
      π.representation.Equiv
        (T.normalizedProductInduced B (fun i => (σ i).obj.representation))) :
    T.IsUnitaryLatticeSupport π (T.unitaryInductionSupport B σ hσ) := by
  let := T.topology
  apply IsSupercuspidalSupport.isUnitaryLatticeSupport
  refine ⟨B.length, T.blockCuspidalDatum B σ, ?_, ?_⟩
  · simp only [Multiset.map_coe, List.map_ofFn]
    rfl
  · refine ⟨B.sum_eq, σ, fun _ => rfl, hπ, ?_⟩
    exact SmoothRep.IsSubrepresentation.isSubquotient
      ⟨SmoothRep.ofHom e.toIntertwiningMap, e.injective⟩

end Langlands.PadicField.TopologicalData

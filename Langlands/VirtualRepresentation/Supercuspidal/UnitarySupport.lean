import Langlands.VirtualRepresentation.Supercuspidal.Support

/-!
# Actual unitary supercuspidal support in the integral lattice

Multisets of genuine supercuspidal classes with explicit unitarizability
witnesses are encoded in the existing unitary lattice. The support relation
retains an actual normalized-induction support witness.
-/

noncomputable section

universe uF uV

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped Classical

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- Unitarity of the actual supercuspidal class in a cuspidal datum. -/
def CuspidalDatum.IsUnitary (d : CuspidalDatum.{uV, uF} T) : Prop :=
  letI := T.topology
  GeneralLinear.SupercuspidalClass.IsUnitarizable d.cls

/-- Actual positive-rank cuspidal data with invariant positive-form witnesses. -/
abbrev UnitaryCuspidalDatum :=
  {d : CuspidalDatum.{uV, uF} T // d.IsUnitary}

/-- Restrict the actual datum/basis equivalence to the genuine unitary subset. -/
def unitaryCuspidalDatumBasisEquiv :
    letI := T.topology
    UnitaryCuspidalDatum.{uF, uV} T ≃ Supercuspidal.UnitaryBasis.{uF, uV} F.Carrier :=
  letI := T.topology
  { toFun := fun d => ⟨T.cuspidalDatumBasisEquiv d.val, d.property⟩
    invFun := fun b => ⟨T.cuspidalDatumBasisEquiv.symm b.val, b.property⟩
    left_inv := fun d => Subtype.ext (T.cuspidalDatumBasisEquiv.symm_apply_apply d.val)
    right_inv := fun b => Subtype.ext (T.cuspidalDatumBasisEquiv.apply_symm_apply b.val) }

@[simp]
theorem unitaryCuspidalDatumBasisEquiv_val (d : UnitaryCuspidalDatum.{uF, uV} T) :
    (T.unitaryCuspidalDatumBasisEquiv d).val = T.cuspidalDatumBasisEquiv d.val := rfl

@[simp]
theorem unitaryCuspidalDatumBasisEquiv_rank (d : UnitaryCuspidalDatum.{uF, uV} T) :
    ((T.unitaryCuspidalDatumBasisEquiv d).val.1 : ℕ) = d.val.rank := rfl

/-- Encode a witnessed unitary multiset directly in the actual unitary lattice. -/
def unitarySupportLattice :
    letI := T.topology
    Multiset (UnitaryCuspidalDatum.{uF, uV} T) →+
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier :=
  letI := T.topology
  Multiset.sumAddMonoidHom.comp
    (Multiset.mapAddMonoidHom fun d => generator (T.unitaryCuspidalDatumBasisEquiv d))

@[simp]
theorem unitarySupportLattice_zero :
    T.unitarySupportLattice (0 : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) = 0 :=
  map_zero _

@[simp]
theorem unitarySupportLattice_add (s t : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    T.unitarySupportLattice (s + t) =
      T.unitarySupportLattice s + T.unitarySupportLattice t :=
  map_add _ _ _

@[simp]
theorem unitarySupportLattice_singleton (d : UnitaryCuspidalDatum.{uF, uV} T) :
    T.unitarySupportLattice {d} = generator (T.unitaryCuspidalDatumBasisEquiv d) := by
  simp [unitarySupportLattice]

@[simp]
theorem unitarySupportLattice_cons (d : UnitaryCuspidalDatum.{uF, uV} T)
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    T.unitarySupportLattice (d ::ₘ s) =
      generator (T.unitaryCuspidalDatumBasisEquiv d) + T.unitarySupportLattice s := by
  simp [unitarySupportLattice]

/-- The coefficient at each actual unitary class is its exact multiset count. -/
theorem unitarySupportLattice_apply (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T))
    (d : UnitaryCuspidalDatum.{uF, uV} T) :
    T.unitarySupportLattice s (T.unitaryCuspidalDatumBasisEquiv d) =
      (s.count d : ℤ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases h : a = d
    · subst a
      simp [unitarySupportLattice_cons, generator, ih, add_comm]
    · simp [unitarySupportLattice_cons, Finsupp.add_apply, generator, Ne.symm h, ih]

/-- The integral encoding retains every unitary datum and multiplicity. -/
theorem unitarySupportLattice_injective : Function.Injective T.unitarySupportLattice := by
  classical
  intro s t h
  apply Multiset.ext.mpr
  intro d
  have hc := congrArg (fun x => x (T.unitaryCuspidalDatumBasisEquiv d)) h
  rw [T.unitarySupportLattice_apply, T.unitarySupportLattice_apply] at hc
  exact Nat.cast_inj.mp hc

@[simp]
theorem unitarySupportLattice_eq_iff (s t : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    T.unitarySupportLattice s = T.unitarySupportLattice t ↔ s = t :=
  T.unitarySupportLattice_injective.eq_iff

/-- Forgetting unitarity gives exactly the already constructed ambient support. -/
theorem includeUnitary_unitarySupportLattice
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    letI := T.topology
    Supercuspidal.includeUnitary F.Carrier (T.unitarySupportLattice s) =
      T.supportLattice (s.map Subtype.val) := by
  let := T.topology
  induction s using Multiset.induction_on with
  | empty => simp
  | cons d s ih =>
    rw [T.unitarySupportLattice_cons, map_add, ih, Multiset.map_cons, T.supportLattice_cons]
    simp [Supercuspidal.includeUnitary,
      includeSubset, VirtualRepresentation.map, generator]

/-- Unitary multiset supports have nonnegative integral coefficients. -/
theorem unitarySupportLattice_effective
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    T.unitarySupportLattice s ∈ effective := by
  intro b
  obtain ⟨d, rfl⟩ := T.unitaryCuspidalDatumBasisEquiv.surjective b
  rw [T.unitarySupportLattice_apply]
  exact Nat.cast_nonneg (α := ℤ) _

/-- Degree counts the general linear group ranks of all unitary terms. -/
theorem unitarySupportLattice_degree
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    letI := T.topology
    Supercuspidal.unitaryDegree F.Carrier (T.unitarySupportLattice s) =
      ((s.map fun d => d.val.rank).sum : ℤ) := by
  let := T.topology
  change Supercuspidal.degree F.Carrier
    (Supercuspidal.includeUnitary F.Carrier (T.unitarySupportLattice s)) = _
  rw [T.includeUnitary_unitarySupportLattice, T.supportLattice_degree]
  simp [Multiset.map_map]

/-- A unitary lattice support retains an actual supercuspidal-support witness. -/
def IsUnitaryLatticeSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier) : Prop :=
  ∃ s : Multiset (UnitaryCuspidalDatum.{uF, uV} T),
    T.IsSupercuspidalSupport π (s.map Subtype.val) ∧ T.unitarySupportLattice s = x

variable {T}

/-- A witnessed support consisting of unitary data gives its unitary encoding. -/
theorem IsSupercuspidalSupport.isUnitaryLatticeSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)}
    (hs : T.IsSupercuspidalSupport π (s.map Subtype.val)) :
    T.IsUnitaryLatticeSupport π (T.unitarySupportLattice s) :=
  ⟨s, hs, rfl⟩

/-- Recover the original actual support relation from an encoded unitary multiset. -/
theorem isUnitaryLatticeSupport_unitarySupportLattice_iff {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (UnitaryCuspidalDatum.{uF, uV} T)) :
    T.IsUnitaryLatticeSupport π (T.unitarySupportLattice s) ↔
      T.IsSupercuspidalSupport π (s.map Subtype.val) := by
  constructor
  · rintro ⟨s', hs', he⟩
    exact (T.unitarySupportLattice_injective he) ▸ hs'
  · exact IsSupercuspidalSupport.isUnitaryLatticeSupport

/-- A unitary support is the same actual support after ambient inclusion. -/
theorem IsUnitaryLatticeSupport.isLatticeSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier}
    (hx : T.IsUnitaryLatticeSupport π x) :
    letI := T.topology
    T.IsLatticeSupport π (Supercuspidal.includeUnitary F.Carrier x) := by
  obtain ⟨s, hs, rfl⟩ := hx
  exact ⟨s.map Subtype.val, hs, (T.includeUnitary_unitarySupportLattice s).symm⟩

/-- Actual representation isomorphisms preserve witnessed unitary lattice support. -/
theorem IsUnitaryLatticeSupport.of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier}
    (hx : T.IsUnitaryLatticeSupport π x) (e : π ≅ π') :
    T.IsUnitaryLatticeSupport π' x := by
  obtain ⟨s, hs, he⟩ := hx
  exact ⟨s, hs.of_iso e, he⟩

theorem isUnitaryLatticeSupport_iff_of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : π ≅ π')
    (x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier) :
    T.IsUnitaryLatticeSupport π x ↔ T.IsUnitaryLatticeSupport π' x :=
  ⟨fun hx => hx.of_iso e, fun hx => hx.of_iso e.symm⟩

theorem IsUnitaryLatticeSupport.effective {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier}
    (hx : T.IsUnitaryLatticeSupport π x) : x ∈ effective := by
  obtain ⟨s, _, rfl⟩ := hx
  exact T.unitarySupportLattice_effective s

theorem IsUnitaryLatticeSupport.degree {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier}
    (hx : T.IsUnitaryLatticeSupport π x) :
    letI := T.topology
    Supercuspidal.unitaryDegree F.Carrier x = (n : ℤ) := by
  let := T.topology
  exact hx.isLatticeSupport.degree

/-- Pointwise unitary class witnesses suffice to lift an actual multiset support. -/
theorem IsSupercuspidalSupport.exists_unitaryLatticeSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) (hu : ∀ d ∈ s, d.IsUnitary) :
    letI := T.topology
    ∃ x : Supercuspidal.UnitaryLattice.{uF, uV} F.Carrier,
      T.IsUnitaryLatticeSupport π x ∧
        Supercuspidal.includeUnitary F.Carrier x = T.supportLattice s := by
  let := T.topology
  let t : Multiset (UnitaryCuspidalDatum.{uF, uV} T) :=
    s.pmap (fun d hd => ⟨d, hd⟩) hu
  have ht : t.map Subtype.val = s := by
    simp [t, Multiset.map_pmap, Multiset.pmap_eq_map]
  refine ⟨T.unitarySupportLattice t, ⟨t, ?_, rfl⟩, ?_⟩
  · rwa [ht]
  · rw [T.includeUnitary_unitarySupportLattice, ht]

end Langlands.PadicField.TopologicalData

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual unitary datum/basis equivalence for canonical p-adic topology. -/
abbrev unitaryCuspidalDatumBasisEquiv :
    PadicField.TopologicalData.UnitaryCuspidalDatum.{uF, uV} F.canonicalTopologicalData ≃
      UnitaryBasis.{uF, uV} F :=
  F.canonicalTopologicalData.unitaryCuspidalDatumBasisEquiv

/-- The multiset-support encoding into the canonical actual unitary lattice. -/
abbrev unitarySupportLattice :
    Multiset (PadicField.TopologicalData.UnitaryCuspidalDatum.{uF, uV}
      F.canonicalTopologicalData) →+ UnitaryLattice.{uF, uV} F :=
  F.canonicalTopologicalData.unitarySupportLattice

/-- Actual support with witnessed unitary terms, in canonical p-adic topology. -/
abbrev IsUnitaryLatticeSupport {n : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (x : UnitaryLattice.{uF, uV} F) : Prop :=
  F.canonicalTopologicalData.IsUnitaryLatticeSupport π x

end Langlands.VirtualRepresentation.PadicSupercuspidal

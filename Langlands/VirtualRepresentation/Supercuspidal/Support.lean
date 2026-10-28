import Langlands.VirtualRepresentation.Supercuspidal.Basic
import Langlands.Representation.Classification.SupercuspidalSupport
import Mathlib.Algebra.BigOperators.Group.Multiset.Basic
import Mathlib.Data.Multiset.Count

/-!
# Actual supercuspidal support in the integral lattice

The multiset support relation is transported to the free integral module on the
same actual supercuspidal classes. Existence and uniqueness of support remain
separate theorem obligations.
-/

noncomputable section

universe uF uV

open CategoryTheory
open Langlands.VirtualRepresentation
open scoped Classical

namespace Langlands.PadicField.TopologicalData

variable {p : ℕ} [Fact p.Prime] {F : PadicField.{uF} p} (T : F.TopologicalData)

/-- The two actual models of a positive-rank supercuspidal class agree. -/
def cuspidalDatumBasisEquiv :
    letI := T.topology
    CuspidalDatum.{uV, uF} T ≃ Supercuspidal.Basis.{uF, uV} F.Carrier :=
  letI := T.topology
  { toFun := fun d => ⟨⟨d.rank, d.rank_pos⟩, d.cls⟩
    invFun := fun b => ⟨b.1, b.1.pos, b.2⟩
    left_inv := fun d => by cases d; rfl
    right_inv := fun b => by rcases b with ⟨⟨n, hn⟩, c⟩; rfl }

@[simp]
theorem cuspidalDatumBasisEquiv_rank (d : CuspidalDatum.{uV, uF} T) :
    ((T.cuspidalDatumBasisEquiv d).1 : ℕ) = d.rank := rfl

/-- A multiset of actual cuspidal data as an integral sum of its basis classes. -/
def supportLattice :
    letI := T.topology
    Multiset (CuspidalDatum.{uV, uF} T) →+ Supercuspidal.Lattice.{uF, uV} F.Carrier :=
  letI := T.topology
  Multiset.sumAddMonoidHom.comp
    (Multiset.mapAddMonoidHom fun d => generator (T.cuspidalDatumBasisEquiv d))

@[simp]
theorem supportLattice_zero : T.supportLattice (0 : Multiset (CuspidalDatum.{uV, uF} T)) = 0 :=
  map_zero _

@[simp]
theorem supportLattice_add (s t : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.supportLattice (s + t) = T.supportLattice s + T.supportLattice t :=
  map_add _ _ _

@[simp]
theorem supportLattice_singleton (d : CuspidalDatum.{uV, uF} T) :
    T.supportLattice {d} = generator (T.cuspidalDatumBasisEquiv d) := by
  simp [supportLattice]

@[simp]
theorem supportLattice_cons (d : CuspidalDatum.{uV, uF} T)
    (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.supportLattice (d ::ₘ s) =
      generator (T.cuspidalDatumBasisEquiv d) + T.supportLattice s := by
  simp [supportLattice]

/-- Each coefficient is exactly the multiplicity in the multiset. -/
theorem supportLattice_apply (s : Multiset (CuspidalDatum.{uV, uF} T))
    (d : CuspidalDatum.{uV, uF} T) :
    T.supportLattice s (T.cuspidalDatumBasisEquiv d) = (s.count d : ℤ) := by
  classical
  induction s using Multiset.induction_on with
  | empty => simp
  | cons a s ih =>
    by_cases h : a = d
    · subst a
      simp [supportLattice_cons, generator, ih, add_comm]
    · simp [supportLattice_cons, Finsupp.add_apply, generator, Ne.symm h, ih]

/-- Passing to integer coefficients loses no multiset information. -/
theorem supportLattice_injective : Function.Injective T.supportLattice := by
  classical
  intro s t h
  apply Multiset.ext.mpr
  intro d
  have hc := congrArg (fun x => x (T.cuspidalDatumBasisEquiv d)) h
  rw [T.supportLattice_apply, T.supportLattice_apply] at hc
  exact Nat.cast_inj.mp hc

@[simp]
theorem supportLattice_eq_iff (s t : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.supportLattice s = T.supportLattice t ↔ s = t :=
  T.supportLattice_injective.eq_iff

/-- Multiset supports have nonnegative coefficients. -/
theorem supportLattice_effective (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    letI := T.topology
    T.supportLattice s ∈ Supercuspidal.effective F.Carrier := by
  let := T.topology
  intro b
  obtain ⟨d, rfl⟩ := T.cuspidalDatumBasisEquiv.surjective b
  rw [T.supportLattice_apply]
  exact Nat.cast_nonneg (α := ℤ) _

/-- The lattice degree is the sum of group ranks, with all multiplicities. -/
theorem supportLattice_degree (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    letI := T.topology
    Supercuspidal.degree F.Carrier (T.supportLattice s) =
      ((s.map CuspidalDatum.rank).sum : ℤ) := by
  let := T.topology
  induction s using Multiset.induction_on with
  | empty => simp
  | cons d s ih =>
    rw [T.supportLattice_cons, map_add, ih]
    have hd : Supercuspidal.degree F.Carrier
        (generator (T.cuspidalDatumBasisEquiv d)) = (d.rank : ℤ) := by
      simp [Supercuspidal.degree, rankedDegree, VirtualRepresentation.degree, extend,
        generator, cuspidalDatumBasisEquiv]
    simp [hd]

/-- An actual support of `π`, represented in the genuine integral lattice. -/
def IsLatticeSupport {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (x : letI := T.topology
      Supercuspidal.Lattice.{uF, uV} F.Carrier) : Prop :=
  ∃ s, T.IsSupercuspidalSupport π s ∧ T.supportLattice s = x

variable {T}

/-- Every witnessed multiset support gives its lattice support. -/
theorem IsSupercuspidalSupport.isLatticeSupport {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {s : Multiset (CuspidalDatum.{uV, uF} T)}
    (hs : T.IsSupercuspidalSupport π s) :
    T.IsLatticeSupport π (T.supportLattice s) :=
  ⟨s, hs, rfl⟩

/-- The lattice relation at an encoded multiset is precisely the original one. -/
theorem isLatticeSupport_supportLattice_iff {n : ℕ}
    (π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (s : Multiset (CuspidalDatum.{uV, uF} T)) :
    T.IsLatticeSupport π (T.supportLattice s) ↔ T.IsSupercuspidalSupport π s := by
  constructor
  · rintro ⟨s', hs', he⟩
    exact (T.supportLattice_injective he) ▸ hs'
  · exact IsSupercuspidalSupport.isLatticeSupport

/-- Isomorphisms of actual smooth representations preserve lattice support. -/
theorem IsLatticeSupport.of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.Lattice.{uF, uV} F.Carrier}
    (hx : T.IsLatticeSupport π x) (e : π ≅ π') : T.IsLatticeSupport π' x := by
  obtain ⟨s, hs, he⟩ := hx
  exact ⟨s, hs.of_iso e, he⟩

theorem isLatticeSupport_iff_of_iso {n : ℕ}
    {π π' : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    (e : π ≅ π')
    (x : letI := T.topology
      Supercuspidal.Lattice.{uF, uV} F.Carrier) :
    T.IsLatticeSupport π x ↔ T.IsLatticeSupport π' x :=
  ⟨fun hx => hx.of_iso e, fun hx => hx.of_iso e.symm⟩

theorem IsLatticeSupport.effective {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.Lattice.{uF, uV} F.Carrier}
    (hx : T.IsLatticeSupport π x) :
    letI := T.topology
    x ∈ Supercuspidal.effective F.Carrier := by
  obtain ⟨s, _, rfl⟩ := hx
  exact T.supportLattice_effective s

theorem IsLatticeSupport.degree {n : ℕ}
    {π : letI := T.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier)}
    {x : letI := T.topology
      Supercuspidal.Lattice.{uF, uV} F.Carrier}
    (hx : T.IsLatticeSupport π x) :
    letI := T.topology
    Supercuspidal.degree F.Carrier x = (n : ℤ) := by
  obtain ⟨s, hs, rfl⟩ := hx
  rw [T.supportLattice_degree, hs.sum_rank]

end Langlands.PadicField.TopologicalData

namespace Langlands.VirtualRepresentation.PadicSupercuspidal

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{uF} p)

/-- The actual class equivalence for the canonical p-adic topology. -/
abbrev cuspidalDatumBasisEquiv :
    PadicField.TopologicalData.CuspidalDatum.{uV, uF} F.canonicalTopologicalData ≃
      Basis.{uF, uV} F :=
  F.canonicalTopologicalData.cuspidalDatumBasisEquiv

/-- Encode multiset support in the actual canonical p-adic lattice. -/
abbrev supportLattice :
    Multiset (PadicField.TopologicalData.CuspidalDatum.{uV, uF}
      F.canonicalTopologicalData) →+ Lattice.{uF, uV} F :=
  F.canonicalTopologicalData.supportLattice

/-- The support relation on the actual canonical p-adic lattice. -/
abbrev IsLatticeSupport {n : ℕ}
    (π : letI := F.canonicalTopologicalData.topology
      SmoothRep.{0, uF, max uF uV} ℂ (GeneralLinear n F.Carrier))
    (x : Lattice.{uF, uV} F) : Prop :=
  F.canonicalTopologicalData.IsLatticeSupport π x

end Langlands.VirtualRepresentation.PadicSupercuspidal

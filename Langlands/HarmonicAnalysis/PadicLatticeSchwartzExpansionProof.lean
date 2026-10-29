import Langlands.HarmonicAnalysis.PadicLatticeSchwartzExpansionStatement
import Langlands.HarmonicAnalysis.PadicLatticeGeometryProof

/-!
# Single-lattice coset expansions of p-adic Schwartz–Bruhat functions

Local constancy and compactness of the support give one valuation lattice under
whose translations a test function is invariant. Finitely many cosets of that
lattice cover the support, and their distinct classes in the quotient give the
expansion with sampled coefficients. See the paired Markdown for the route.
-/

noncomputable section

open Topology

namespace Langlands.HarmonicAnalysis

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Every Schwartz–Bruhat function on a supplied p-adic field is invariant under
the translations by one valuation lattice `T.additiveLattice m`. The level is
derived from local constancy and compact support in the supplied topology. -/
theorem padicSchwartzBruhat_exists_additiveLattice_invariant
    (F : PadicField.{u} p) (T : F.TopologicalData)
    (f : @SchwartzBruhat F.Carrier T.topology) :
    ∃ m : ℤ, ∀ x h : F.Carrier, h ∈ T.additiveLattice m → f (x + h) = f x := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  have hopen (n : ℤ) : IsOpen (T.additiveLattice n : Set F.Carrier) :=
    ((padicLatticeGeometry F T).2 n).2
  have hloc (x : F.Carrier) :
      ∃ n : ℤ, ∀ d ∈ T.additiveLattice n, f (x + d) = f x := by
    have hs : {d : F.Carrier | f (x + d) = f x} ∈ 𝓝 (0 : F.Carrier) :=
      ((f.locallyConstant.isOpen_fiber (f x)).preimage
        (continuous_const.add continuous_id)).mem_nhds (by simp)
    obtain ⟨n, hn⟩ := T.exists_additiveLattice_subset hs
    exact ⟨n, fun d hd => hn hd⟩
  choose n hn using hloc
  have hK : IsCompact (tsupport (f : F.Carrier → ℂ)) := f.hasCompactSupport.isCompact
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover
    (fun x => {z | z - x ∈ T.additiveLattice (n x)})
    (fun x _ => ((hopen (n x)).preimage (continuous_id.sub continuous_const)).mem_nhds
      (by simp))
  obtain ⟨M, hM⟩ := Finset.exists_le (t.image fun x => -n x)
  refine ⟨-M, ?_⟩
  have hsupp : ∀ y ∈ tsupport (f : F.Carrier → ℂ), ∀ h ∈ T.additiveLattice (-M),
      f (y + h) = f y := by
    intro y hy h hh
    obtain ⟨x, hx, hyx⟩ := Set.mem_iUnion₂.mp (htK hy)
    have hyx : y - x ∈ T.additiveLattice (n x) := hyx
    have hle : -M ≤ n x := by
      have := hM _ (Finset.mem_image_of_mem _ hx)
      omega
    have hh' := T.additiveLattice_mono hle hh
    have e1 := hn x (y - x) hyx
    have e2 := hn x (y + h - x) (by
      rw [show y + h - x = (y - x) + h by abel]
      exact (T.additiveLattice (n x)).add_mem hyx hh')
    rw [show x + (y - x) = y by abel] at e1
    rw [show x + (y + h - x) = y + h by abel] at e2
    rw [e1, e2]
  intro y h hh
  by_cases hy : y ∈ tsupport (f : F.Carrier → ℂ)
  · exact hsupp y hy h hh
  by_cases hyh : y + h ∈ tsupport (f : F.Carrier → ℂ)
  · have := hsupp (y + h) hyh (-h) (neg_mem hh)
    rw [add_neg_cancel_right] at this
    exact this.symm
  · rw [image_eq_zero_of_notMem_tsupport hy, image_eq_zero_of_notMem_tsupport hyh]

/-- Every Schwartz–Bruhat function on a supplied p-adic field is, at every point,
a finite linear combination of indicators of cosets of one valuation lattice. -/
theorem padicLatticeSchwartzExpansion (F : PadicField.{u} p) (T : F.TopologicalData) :
    PadicLatticeSchwartzExpansionStatement F T := by
  let := T.topology
  let := T.valuativeRel
  let := T.localField
  classical
  intro f
  obtain ⟨m, hm⟩ := padicSchwartzBruhat_exists_additiveLattice_invariant F T f
  let L := T.additiveLattice m
  have hopen : IsOpen (L : Set F.Carrier) := ((padicLatticeGeometry F T).2 m).2
  have hK : IsCompact (tsupport (f : F.Carrier → ℂ)) := f.hasCompactSupport.isCompact
  obtain ⟨t, -, htK⟩ := hK.elim_nhds_subcover (fun x => {z | z - x ∈ L})
    (fun x _ => (hopen.preimage (continuous_id.sub continuous_const)).mem_nhds (by simp))
  let S : Finset (F.Carrier ⧸ L) :=
    t.image (fun x : F.Carrier => (QuotientAddGroup.mk x : F.Carrier ⧸ L))
  let e := S.equivFin
  refine ⟨m, S.card, fun i => f (e.symm i).1.out, fun i => (e.symm i).1.out, ?_⟩
  intro x
  have hmem (q : F.Carrier ⧸ L) : x - q.out ∈ L ↔ (x : F.Carrier ⧸ L) = q := by
    conv_rhs => rw [← QuotientAddGroup.out_eq' q]
    exact QuotientAddGroup.eq_iff_sub_mem.symm
  have hval : f (x : F.Carrier ⧸ L).out = f x := by
    have h2 := hm (x : F.Carrier ⧸ L).out _ ((hmem _).mpr rfl)
    rw [show (x : F.Carrier ⧸ L).out + (x - (x : F.Carrier ⧸ L).out) = x by abel] at h2
    exact h2.symm
  have hterm (q : F.Carrier ⧸ L) :
      f q.out * ({z : F.Carrier | z - q.out ∈ T.additiveLattice m}.indicator
        (fun _ => (1 : ℂ))) x = if (x : F.Carrier ⧸ L) = q then f q.out else 0 := by
    by_cases hq : (x : F.Carrier ⧸ L) = q
    · have : x ∈ {z : F.Carrier | z - q.out ∈ T.additiveLattice m} := (hmem q).mpr hq
      rw [Set.indicator_of_mem this, mul_one]
      simp [hq]
    · have : x ∉ {z : F.Carrier | z - q.out ∈ T.additiveLattice m} :=
        fun h => hq ((hmem q).mp h)
      rw [Set.indicator_of_notMem this, mul_zero]
      simp [hq]
  rw [Fintype.sum_equiv e.symm _ (fun q : S => f q.1.out *
      ({z : F.Carrier | z - q.1.out ∈ T.additiveLattice m}.indicator
        (fun _ => (1 : ℂ))) x) (fun _ => rfl)]
  rw [Finset.sum_coe_sort S (fun q => f q.out *
      ({z : F.Carrier | z - q.out ∈ T.additiveLattice m}.indicator
        (fun _ => (1 : ℂ))) x)]
  simp_rw [hterm]
  rw [Finset.sum_ite_eq]
  split_ifs with hS
  · exact hval.symm
  · apply image_eq_zero_of_notMem_tsupport
    intro hx
    apply hS
    obtain ⟨y, hy, hxy⟩ := Set.mem_iUnion₂.mp (htK hx)
    have hxy : x - y ∈ L := hxy
    exact Finset.mem_image.mpr ⟨y, hy, (QuotientAddGroup.eq_iff_sub_mem.mpr hxy).symm⟩

end Langlands.HarmonicAnalysis

import Langlands.Representation.Smooth.IrreducibleCompositionFactors
import Langlands.Representation.Filtration.CentralEigenspaceSplitting
import Langlands.Representation.Filtration.MultiplicityFreeSubmoduleLatticeProof

/-! Simple series of subobjects with separated scalar actions. -/

noncomputable section

namespace Langlands.SmoothRep

open IrreducibleGrothendieckProof CentralEigenspaceSplitting

universe uK uG uV

variable {k : Type uK} [Field k] {G : Type uG} [Group G] [TopologicalSpace G]

/-- A finite-length subobject of an object with a scalar-separated simple
series has a simple series with scalars from an injective subfamily. -/
theorem exists_scalarSeparatedSeries_of_injective
    (A B : SmoothRep.{uK,uG,uV} k G) (hB : B.HasFiniteLength)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (ι : B.representation.IntertwiningMap A.representation) (hι : Function.Injective ι) :
    ∃ (m : ℕ) (t : ObjectRepFiltration B.obj m) (e : Fin m → Fin n),
      t.HasSimpleFactors ∧ Function.Injective e ∧
        ∀ i v, (t.gradedRepresentation i).ρ z v = c (e i) • v := by
  classical
  let t := (chosenSeries ⟨B, hB⟩).2.val
  have ht : t.HasSimpleFactors := (chosenSeries ⟨B, hB⟩).2.property
  have hfree : ∀ i j : Fin n,
      Nonempty ((s.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ) →
        i = j := by
    intro i j ⟨E⟩
    obtain ⟨v, hv⟩ := exists_ne_zero_of_isIrreducible (hs i)
    have he := apply_eq_smul_of_equiv E z (c j) (hgr j) v
    have hzero : (c i - c j) • v = 0 := by
      rw [sub_smul, ← hgr i v, ← he, sub_self]
    exact hc (sub_eq_zero.mp ((smul_eq_zero.mp hzero).resolve_right hv))
  have hmono : ∀ τ : Rep.{uV} k G, t.factorMultiplicity τ ≤ s.factorMultiplicity τ :=
    fun τ => jordanHolderInjectiveMonotonicity k G B.obj A.obj τ ι hι _ _
      ⟨_, t, ht, rfl⟩ ⟨n, s, hs, rfl⟩
  have hle : ∀ τ : Rep.{uV} k G, t.factorMultiplicity τ ≤ 1 := fun τ =>
    (hmono τ).trans (MultiplicityFreeSubmoduleLatticeProof.factorMultiplicity_le_one
      s hfree τ)
  have hex : ∀ i, ∃ j, Nonempty
      ((t.gradedRepresentation i).ρ.Equiv (s.gradedRepresentation j).ρ) := by
    intro i
    have hpos : 0 < t.factorMultiplicity (t.gradedRepresentation i) := by
      unfold ObjectRepFiltration.factorMultiplicity
      exact Nat.card_pos_iff.mpr
        ⟨⟨⟨i, ⟨Representation.Equiv.refl _⟩⟩⟩, inferInstance⟩
    have hspos := lt_of_lt_of_le hpos (hmono (t.gradedRepresentation i))
    by_contra hn
    have hnone : ∀ j, IsEmpty
        ((s.gradedRepresentation j).ρ.Equiv (t.gradedRepresentation i).ρ) := by
      intro j
      exact ⟨fun E => hn ⟨j, ⟨E.symm⟩⟩⟩
    have : IsEmpty {j : Fin n //
        Nonempty ((s.gradedRepresentation j).ρ.Equiv (t.gradedRepresentation i).ρ)} :=
      ⟨fun j => (hnone j.val).false j.property.some⟩
    simp [ObjectRepFiltration.factorMultiplicity] at hspos
  choose e he using hex
  have heinj : Function.Injective e := by
    intro i j hij
    have hcard := hle (t.gradedRepresentation i)
    unfold ObjectRepFiltration.factorMultiplicity at hcard
    have hsub : Subsingleton {l //
        Nonempty ((t.gradedRepresentation l).ρ.Equiv (t.gradedRepresentation i).ρ)} :=
      Finite.card_le_one_iff_subsingleton.mp hcard
    obtain ⟨Ei⟩ := he i
    obtain ⟨Ej⟩ := he j
    rw [hij] at Ei
    exact congrArg Subtype.val
      (hsub.elim ⟨i, ⟨Representation.Equiv.refl _⟩⟩ ⟨j, ⟨Ej.trans Ei.symm⟩⟩)
  refine ⟨_, t, e, ht, heinj, ?_⟩
  intro i v
  exact apply_eq_smul_of_equiv (he i).some z (c (e i)) (hgr (e i)) v

/-- Choose an actual scalar-separated simple series for the finite-length
source of an injective intertwiner into a supplied separated series. -/
def scalarSeparatedSeriesOfInjective
    (A B : SmoothRep.{uK,uG,uV} k G) (hB : B.HasFiniteLength)
    {n : ℕ} (s : ObjectRepFiltration A.obj n) (hs : s.HasSimpleFactors)
    (z : G) (c : Fin n → k) (hc : Function.Injective c)
    (hgr : ∀ i v, (s.gradedRepresentation i).ρ z v = c i • v)
    (ι : B.representation.IntertwiningMap A.representation) (hι : Function.Injective ι) :
    Σ m, Σ t : ObjectRepFiltration B.obj m,
      {e : Fin m → Fin n // t.HasSimpleFactors ∧ Function.Injective e ∧
        ∀ i v, (t.gradedRepresentation i).ρ z v = c (e i) • v} :=
  Classical.choice (by
    obtain ⟨m, t, e, ht, he, hgr'⟩ :=
      exists_scalarSeparatedSeries_of_injective A B hB s hs z c hc hgr ι hι
    exact ⟨⟨m, t, e, ht, he, hgr'⟩⟩)

end Langlands.SmoothRep

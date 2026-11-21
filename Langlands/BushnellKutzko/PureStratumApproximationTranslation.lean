import Langlands.BushnellKutzko.RefinementChainTransport
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Strata on index-translated lattice chains

Two lattice chains whose lattices agree after an integer shift of the index define the same
hereditary order, filtration, valuation, stabilizer and period. BK93 identifies such chains
implicitly (a hereditary order determines its chain only up to translation, printed p. 20).
-/

noncomputable section

namespace Langlands.BushnellKutzko.PureApproximation

universe uO uK uV

/-- A stratum moved to an index-translated chain, keeping its integers and element, has the
same coset and period and is pure, respectively simple, exactly when the original is. -/
def ChainTranslationStatement : Prop :=
  ∀ (O : Type uO) (K : Type uK) (V : Type uV) [CommRing O] [Field K] [Algebra O K]
    [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
    (S T : Stratum O K V) (t : ℤ), (∀ i, S.chain.lattice i = T.chain.lattice (i + t)) →
    T.n = S.n → T.r = S.r → T.b = S.b →
      (S.IsPure ↔ T.IsPure) ∧ (S.IsSimple ↔ T.IsSimple) ∧ S.coset = T.coset ∧
        S.chain.period = T.chain.period

section Translate

variable {O : Type uO} {K : Type uK} {V : Type uV} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V]
  {A B : LatticeChain O K V} {t : ℤ}

theorem mem_endFiltration_iff_of_translate (h : ∀ i, A.lattice i = B.lattice (i + t)) {n : ℤ}
    {x : Module.End K V} : x ∈ A.endFiltration n ↔ x ∈ B.endFiltration n := by
  rw [LatticeChain.mem_endFiltration, LatticeChain.mem_endFiltration]
  constructor
  · intro hx i v hv
    have hv' : v ∈ A.lattice (i - t) := by rw [h, sub_add_cancel]; exact hv
    have := hx (i - t) v hv'
    rwa [h, show i - t + n + t = i + n by ring] at this
  · intro hx i v hv
    rw [h] at hv ⊢
    rw [show i + n + t = i + t + n by ring]
    exact hx _ v hv

theorem criticalExponent_eq_of_translate (h : ∀ i, A.lattice i = B.lattice (i + t))
    (β : Module.End K V) : criticalExponent A β = criticalExponent B β := by
  have hadj (k : ℤ) (x : Module.End K V) :
      x ∈ adjointLattice A β k ↔ x ∈ adjointLattice B β k := by
    rw [mem_adjointLattice_iff_mul, mem_adjointLattice_iff_mul,
      mem_endFiltration_iff_of_translate h, mem_endFiltration_iff_of_translate h]
  have hcen (k : ℤ) (x : Module.End K V) :
      x ∈ centralizerLattice A β k ↔ x ∈ centralizerLattice B β k := by
    rw [mem_centralizerLattice_iff_mul, mem_centralizerLattice_iff_mul,
      mem_endFiltration_iff_of_translate h]
  have hset : criticalIndexSet A β = criticalIndexSet B β := by
    ext k
    simp only [criticalIndexSet, Set.mem_ofPred_eq, SetLike.le_def, Submodule.mem_sup, hadj,
      hcen, mem_endFiltration_iff_of_translate h]
  simp only [criticalExponent, hset]

theorem valuation_eq_of_translate (h : ∀ i, A.lattice i = B.lattice (i + t))
    (x : Module.End K V) : A.valuation x = B.valuation x := by
  simp only [LatticeChain.valuation, mem_endFiltration_iff_of_translate h]

theorem mem_stabilizer_iff_of_translate (h : ∀ i, A.lattice i = B.lattice (i + t))
    {g : (Module.End K V)ˣ} : g ∈ A.stabilizer ↔ g ∈ B.stabilizer := by
  rw [LatticeChain.mem_stabilizer, LatticeChain.mem_stabilizer]
  constructor
  · intro hg i
    obtain ⟨j, hj⟩ := hg (i - t)
    refine ⟨j + t, ?_⟩
    rw [h, h, sub_add_cancel] at hj
    exact hj
  · intro hg i
    obtain ⟨j, hj⟩ := hg (i + t)
    refine ⟨j - t, ?_⟩
    rw [h, h, sub_add_cancel]
    exact hj

theorem period_eq_of_translate (h : ∀ i, A.lattice i = B.lattice (i + t)) :
    A.period = B.period := by
  symm
  apply A.period_unique
  intro i
  rw [h, h, show i + (B.period : ℤ) + t = i + t + B.period by ring, B.lattice_add_period]

end Translate

/-- Transfer along an index translation. -/
theorem chainTranslation : ChainTranslationStatement.{uO, uK, uV} := by
  intro O K V _ _ _ _ _ _ _ S T t h hn hr hb
  obtain ⟨A, n, r, b, hrn, hv⟩ := S
  obtain ⟨B, n', r', b', hrn', hv'⟩ := T
  simp only at h hn hr hb
  subst n' r' b'
  have hval : A.valuation b = B.valuation b := valuation_eq_of_translate h b
  have hpure : (Stratum.IsPure ⟨A, n, r, b, hrn, hv⟩) ↔
      (Stratum.IsPure ⟨B, n, r, b, hrn', hv'⟩) := by
    constructor
    · rintro ⟨⟨hf, hu⟩, hvb⟩
      exact ⟨⟨hf, fun a => (mem_stabilizer_iff_of_translate h).mp (hu a)⟩, hval ▸ hvb⟩
    · rintro ⟨⟨hf, hu⟩, hvb⟩
      exact ⟨⟨hf, fun a => (mem_stabilizer_iff_of_translate h).mpr (hu a)⟩, hval.symm ▸ hvb⟩
  refine ⟨hpure, ?_, ?_, period_eq_of_translate h⟩
  · constructor
    · rintro ⟨hp, hk⟩
      refine ⟨hpure.mp hp, ?_⟩
      change criticalExponent B b < _
      rw [← criticalExponent_eq_of_translate h]
      exact hk
    · rintro ⟨hp, hk⟩
      refine ⟨hpure.mpr hp, ?_⟩
      change criticalExponent A b < _
      rw [criticalExponent_eq_of_translate h]
      exact hk
  · ext x
    exact mem_endFiltration_iff_of_translate h

end Langlands.BushnellKutzko.PureApproximation

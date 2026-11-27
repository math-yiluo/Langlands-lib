import Langlands.BushnellKutzko.RefinementChainTransport
import Langlands.BushnellKutzko.PureSimpleStratum

/-! # Strata moved between lattice chains with the same lattices -/

noncomputable section

namespace Langlands.BushnellKutzko

universe uO uO' uK uV

namespace Stratum

variable {O : Type uO} {O' : Type uO'} {K : Type uK} {V : Type uV} [CommRing O] [CommRing O']
  [Field K] [Algebra O K] [Algebra O' K] [AddCommGroup V] [Module K V]
  [Module O V] [IsScalarTower O K V] [Module O' V] [IsScalarTower O' K V]

/-- The stratum with the same integers and element on a second chain with the same
lattice subsets. -/
def chainTransfer (S : Stratum O K V) (L' : LatticeChain O' K V)
    (h : ∀ i, (S.chain.lattice i : Set V) = L'.lattice i) : Stratum O' K V :=
  ⟨L', S.n, S.r, S.b, S.r_lt_n, by
    rw [← LatticeChain.valuation_congr h]
    exact S.valuation_ge⟩

variable (S : Stratum O K V) (L' : LatticeChain O' K V)
  (h : ∀ i, (S.chain.lattice i : Set V) = L'.lattice i)

@[simp] theorem chainTransfer_chain : (S.chainTransfer L' h).chain = L' := rfl
@[simp] theorem chainTransfer_n : (S.chainTransfer L' h).n = S.n := rfl
@[simp] theorem chainTransfer_r : (S.chainTransfer L' h).r = S.r := rfl
@[simp] theorem chainTransfer_b : (S.chainTransfer L' h).b = S.b := rfl

theorem isPure_chainTransfer_iff : (S.chainTransfer L' h).IsPure ↔ S.IsPure := by
  unfold IsPure
  simp only [chainTransfer_b, chainTransfer_chain, chainTransfer_n]
  rw [← LatticeChain.valuation_congr h]
  refine and_congr_left fun _ => exists_congr fun hf => ?_
  letI := hf.toField
  exact forall_congr' fun a => (LatticeChain.mem_stabilizer_congr h).symm

theorem isSimple_chainTransfer_iff : (S.chainTransfer L' h).IsSimple ↔ S.IsSimple := by
  unfold IsSimple
  rw [isPure_chainTransfer_iff]
  simp only [chainTransfer_b, chainTransfer_chain, chainTransfer_r]
  rw [← LatticeChain.criticalExponent_congr h]

theorem coset_chainTransfer : (S.chainTransfer L' h).coset = S.coset := by
  ext x
  change x - S.b ∈ L'.endFiltration (-S.r) ↔ x - S.b ∈ S.chain.endFiltration (-S.r)
  exact (LatticeChain.mem_endFiltration_congr h).symm

end Stratum

end Langlands.BushnellKutzko

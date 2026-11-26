import Langlands.BaseChange.UnramifiedWeylJacquetSupportStatement
import Langlands.Representation.IntegerLattice.GeneralizedWeightGlobalBasisProof

/-! # Trace of a uniformizer diagonal on the normalized Borel Jacquet fixed space -/

noncomputable section

namespace Langlands.BaseChange

open Correspondence Unramified IntegerLattice
open scoped BigOperators

universe u v

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p) {r : ℕ}
  {V : Type v} [AddCommGroup V] [Module ℂ V]

private def uniformizerPowerLevi (r : ℕ) :
    IntegerLattice.Lattice (r + 1) →* (borelShape r).Levi F.Carrier :=
  ((borelShape r).blockScalarLevi F.Carrier).comp
    { toFun := fun n i => F.canonicalTopologicalData.uniformizerUnit ^ n.toAdd i
      map_one' := by
        funext i
        exact zpow_zero _
      map_mul' n m := by
        funext i
        exact zpow_add _ _ _ }

private theorem uniformizerPowerLevi_mem_center (n : IntegerLattice.Lattice (r + 1)) :
    uniformizerPowerLevi F r n ∈ Subgroup.center ((borelShape r).Levi F.Carrier) :=
  (borelShape r).blockScalarLevi_mem_center F.Carrier _

private theorem uniformizerPowerLevi_generator (i : Fin (r + 1)) :
    uniformizerPowerLevi F r (generator (r + 1) i) = borelUniformizerLevi F r i := by
  classical
  let m : Fin (r + 1) → ℤ := Pi.single i 1
  have hexp :
      (fun j => F.canonicalTopologicalData.uniformizerUnit ^ m j) =
        Pi.mulSingle i F.canonicalTopologicalData.uniformizerUnit := by
    dsimp [m]
    funext j
    rcases eq_or_ne j i with rfl | h
    · rw [Pi.single_eq_same, Pi.mulSingle_eq_same, zpow_one]
    · rw [Pi.single_eq_of_ne h, Pi.mulSingle_eq_of_ne h, zpow_zero]
  exact congrArg ((borelShape r).blockScalarLevi F.Carrier) hexp

/-- The normalized action of the diagonal of canonical uniformizer powers on
the integral-diagonal fixed space, regarded as a representation of the lattice. -/
def borelJacquetLatticeAction (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) :
    Representation ℂ (IntegerLattice.Lattice (r + 1)) (borelJacquetIntegralFixed F ρ) :=
  let J := F.canonicalNormalizedJacquet (borelShape r) ρ
  let R : Representation ℂ (IntegerLattice.Lattice (r + 1)) ((borelShape r).JacquetModule ρ) :=
    J.comp (uniformizerPowerLevi F r)
  R.subrepresentation (borelJacquetIntegralFixed F ρ) (by
    intro n x hx k
    let t := uniformizerPowerLevi F r n
    have hcomm := Subgroup.mem_center_iff.mp (uniformizerPowerLevi_mem_center F n)
      (k : (borelShape r).Levi F.Carrier)
    have hFix : J (k : (borelShape r).Levi F.Carrier) x = x := hx k
    change J k (J t x) = J t x
    rw [← Module.End.mul_apply, ← map_mul, hcomm, map_mul, Module.End.mul_apply, hFix])

theorem borelJacquetLatticeAction_apply_coe
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (n : IntegerLattice.Lattice (r + 1))
    (x : borelJacquetIntegralFixed F ρ) :
    (borelJacquetLatticeAction F ρ n x : (borelShape r).JacquetModule ρ) =
      F.canonicalNormalizedJacquet (borelShape r) ρ
        (GeneralLinear.BlockShape.singletonLevi F.Carrier
          (fun i => F.canonicalTopologicalData.uniformizerUnit ^ n.toAdd i)) x := rfl

theorem borelJacquetLatticeAction_generator
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (i : Fin (r + 1)) :
    borelJacquetLatticeAction F ρ (generator (r + 1) i) =
      borelJacquetUniformizerAction F ρ i := by
  ext1 x
  apply Subtype.ext
  change F.canonicalNormalizedJacquet (borelShape r) ρ
      (uniformizerPowerLevi F r (generator (r + 1) i)) x =
    F.canonicalNormalizedJacquet (borelShape r) ρ (borelUniformizerLevi F r i) x
  rw [uniformizerPowerLevi_generator]

/-- On integral-diagonal fixed vectors, the diagonal action depends only on
the orders of the entries. -/
theorem borelJacquetLatticeAction_apply_eq_of_ord
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V) (n : IntegerLattice.Lattice (r + 1))
    (a : Fin (r + 1) → F.Carrierˣ)
    (ha : ∀ i, F.canonicalTopologicalData.ord (a i : F.Carrier) = n.toAdd i)
    (x : borelJacquetIntegralFixed F ρ) :
    (borelJacquetLatticeAction F ρ n x : (borelShape r).JacquetModule ρ) =
      F.canonicalNormalizedJacquet (borelShape r) ρ
        (GeneralLinear.BlockShape.singletonLevi F.Carrier a) x := by
  let D := F.canonicalTopologicalData
  let b (i : Fin (r + 1)) := D.uniformizerUnit ^ n.toAdd i
  let u (i : Fin (r + 1)) := (b i)⁻¹ * a i
  let L : (Fin (r + 1) → F.Carrierˣ) →* (borelShape r).Levi F.Carrier :=
    GeneralLinear.BlockShape.singletonLevi F.Carrier
  let J := F.canonicalNormalizedJacquet (borelShape r) ρ
  have hu : L u ∈ borelIntegralDiagonal F r := by
    apply (singletonLevi_mem_borelIntegralDiagonal_iff F u).2
    intro i
    change D.ord (((b i)⁻¹ * a i : F.Carrierˣ) : F.Carrier) = 0
    rw [Units.val_mul, D.ord_mul (Units.ne_zero _) (Units.ne_zero _),
      Units.val_inv_eq_inv_val, D.ord_inv]
    change -D.ord ((D.uniformizerUnit ^ n.toAdd i : F.Carrierˣ) : F.Carrier) +
      D.ord (a i : F.Carrier) = 0
    rw [Units.val_zpow_eq_zpow_val, D.ord_zpow, D.uniformizerUnit_val, D.ord_uniformizer,
      mul_one, ha i, neg_add_cancel]
  have hbu : b * u = a := by
    funext i
    exact mul_inv_cancel_left (b i) (a i)
  have hFix : J (L u) (x : (borelShape r).JacquetModule ρ) = x := x.2 ⟨L u, hu⟩
  rw [borelJacquetLatticeAction_apply_coe]
  change J (L b) x = J (L a) x
  have hMul : J (L (b * u)) = J (L b) * J (L u) := (J.comp L).map_mul b u
  rw [← hbu, hMul, Module.End.mul_apply, hFix]

/-- The trace of a normalized uniformizer diagonal is the sum, with
multiplicities, of the Jacquet characters at that diagonal. -/
def BorelJacquetWeightTraceStatement : Prop :=
  ∀ (p : ℕ) [Fact p.Prime] (F : PadicField.{u} p) (r : ℕ)
    (V : Type v) [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GeneralLinear (r + 1) F.Carrier) V),
    FiniteDimensional ℂ (borelJacquetIntegralFixed F ρ) →
    ∀ ν : Fin (r + 1) → ℤ,
      LinearMap.trace ℂ (borelJacquetIntegralFixed F ρ)
        (borelJacquetLatticeAction F ρ (Multiplicative.ofAdd ν)) =
      ((borelJacquetMultiset F ρ).map (fun c => ∏ i : Fin (r + 1), (c i : ℂ) ^ ν i)).sum

private theorem trace_lattice_from_multiset {d : ℕ} {W : Type v}
    [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (A : CommutingInvertibleTuple d W) (m : Multiset (Fin d → ℂˣ)) [DecidableEq (Fin d → ℂˣ)]
    (hCount : ∀ c, m.count c = Module.finrank ℂ (generalizedWeightBlock A c))
    (n : IntegerLattice.Lattice d) :
    LinearMap.trace ℂ W (tupleRepresentationEquiv d W A n) =
      (m.map (fun c => (coordinateCharacter c n : ℂ))).sum := by
  classical
  let S := m.toFinset
  let dim (c : Fin d → ℂˣ) := Module.finrank ℂ (generalizedWeightBlock A c)
  have hMem (c : Fin d → ℂˣ) (j : Fin (dim c)) : c ∈ S :=
    Multiset.mem_toFinset.mpr (Multiset.count_pos.mp (hCount c ▸ Nat.zero_lt_of_lt j.isLt))
  let e : (Σ c : S, Fin (dim c)) ≃ (Σ c : Fin d → ℂˣ, Fin (dim c)) :=
    { toFun := fun a => ⟨a.1.val, a.2⟩
      invFun := fun a => ⟨⟨a.1, hMem a.1 a.2⟩, a.2⟩
      left_inv := fun ⟨⟨_, _⟩, _⟩ => rfl
      right_inv := fun ⟨_, _⟩ => rfl }
  obtain ⟨b, B, _, _, _, _, hDiag⟩ := commutingTupleGeneralizedWeightGlobalBasis d W A
  have hTrace :
      LinearMap.trace ℂ W (tupleRepresentationEquiv d W A n) =
        ∑ c : S, (dim c : ℂ) * (coordinateCharacter c.val n : ℂ) := by
    rw [LinearMap.trace_eq_matrix_trace ℂ (B.reindex e.symm), Matrix.trace, Fintype.sum_sigma]
    apply Finset.sum_congr rfl
    intro c hc
    calc
      _ = ∑ _j : Fin (dim c), (coordinateCharacter c.val n : ℂ) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [Matrix.diag_apply, LinearMap.toMatrix_apply, Module.Basis.repr_reindex_apply,
          Module.Basis.reindex_apply, Equiv.symm_symm]
        exact hDiag n c.val j
      _ = _ := by simp [nsmul_eq_mul]
  rw [hTrace, Finset.sum_multiset_map_count]
  simp only [dim, ← hCount, nsmul_eq_mul]
  exact Finset.sum_coe_sort S (fun c => (m.count c : ℂ) * (coordinateCharacter c n : ℂ))

theorem borelJacquetWeightTrace : BorelJacquetWeightTraceStatement.{u, v} := by
  classical
  intro p _ F r V _ _ ρ hdim ν
  let W := borelJacquetIntegralFixed F ρ
  let ρL := borelJacquetLatticeAction F ρ
  let n : IntegerLattice.Lattice (r + 1) := Multiplicative.ofAdd ν
  let A := (tupleRepresentationEquiv (r + 1) W).symm ρL
  have hBlock (c : Fin (r + 1) → ℂˣ) :
      generalizedWeightBlock A c = borelJacquetWeightSpace F ρ c := by
    change (⨅ i, (A.1 i : Module.End ℂ W).maxGenEigenspace (c i : ℂ)) =
      ⨅ i, (borelJacquetUniformizerAction F ρ i).maxGenEigenspace (c i : ℂ)
    refine iInf_congr fun i => ?_
    have hGenerator : (A.1 i : Module.End ℂ W) = borelJacquetUniformizerAction F ρ i :=
      (tupleRepresentationEquiv_symm_apply_coe _ _ ρL i).trans
        (borelJacquetLatticeAction_generator F ρ i)
    rw [hGenerator]
  have hCount (c : Fin (r + 1) → ℂˣ) :
      (borelJacquetMultiset F ρ).count c = Module.finrank ℂ (generalizedWeightBlock A c) := by
    rw [count_borelJacquetMultiset_of_finiteDimensional, hBlock]
    rfl
  have h := trace_lattice_from_multiset A (borelJacquetMultiset F ρ) hCount n
  simpa only [A, tupleRepresentationEquiv_right_inv, ρL, coe_coordinateCharacter, n, toAdd_ofAdd] using h

end Langlands.BaseChange

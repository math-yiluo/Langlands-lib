import Langlands.BushnellKutzko.PureStratumApproximationBlocks
import Langlands.BushnellKutzko.PureStratumApproximationLineChains
import Langlands.BushnellKutzko.RefinementElementExactness
import Langlands.BushnellKutzko.RefinementCore

/-! # Critical exponent under a repeated field-line diagonal

This proves the dilation used in the maximal-generated-subfield reduction in the
opening proof of BK93 (2.4.1)(i), printed p. 66.
-/

noncomputable section

open ValuativeRel

namespace Langlands.BushnellKutzko.PureApproximation

universe uF uE uV

variable {F : Type uF} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
  {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
  (A : LatticeChain 𝒪[F] F V) (C : LatticeChain 𝒪[F] F E)
  {n : ℕ} (w : Module.Basis (Fin n) E V)

section Coordinates

variable [FiniteDimensional F E] (hA : ∀ g : Eˣ, subfieldUnits F E V g ∈ A.stabilizer)
  (hC : ∀ g : Eˣ, subfieldUnits F E E g ∈ C.stabilizer)
  {π : 𝒪[F]} (hπ : Irreducible π) {ϖ : subfieldIntegers F E} (hϖ : Irreducible ϖ)

include hC in
/-- An ambient chain and a line chain normalized by the same field have scaled coordinates.
The offset compensates for the index of `1` in the line chain. -/
theorem scaledLatticeCoordinates_of_normalizing :
    ScaledLatticeCoordinates A C w
      (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
      (fun j => A.index hπ (w j) -
        (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd * C.index hπ 1) := by
  intro j i a
  by_cases ha : a = 0
  · simp [ha]
  let d := (A.fieldShift E hA (subfieldIntegerUnit E hϖ.ne_zero)).toAdd
  have hd : 0 < d := A.fieldShift_uniformizer_pos E hA hϖ
  have hC1 := uniformizerShift_eq_one_of_cyclic C hC hϖ (one_ne_zero : (1 : E) ≠ 0)
    (fun x => ⟨x, by simp⟩)
  let g := Units.mk0 a ha
  obtain ⟨m, u, hu⟩ := subfieldUnit_factorization E hϖ g
  have hAj := index_smul_unit A hA hπ g (w.ne_zero j)
  rw [A.fieldShift_eq_mul_of_factorization E hA hϖ.ne_zero hu] at hAj
  have hCi := index_smul_unit C hC hπ g (one_ne_zero : (1 : E) ≠ 0)
  rw [C.fieldShift_eq_mul_of_factorization E hC hϖ.ne_zero hu, hC1, one_mul,
    smul_eq_mul, mul_one] at hCi
  change A.index hπ (a • w j) = A.index hπ (w j) + d * m at hAj
  change C.index hπ a = C.index hπ 1 + m at hCi
  change a • w j ∈ A.lattice i ↔
    a ∈ C.lattice (ceilDiv (i - (A.index hπ (w j) - d * C.index hπ 1)) d)
  rw [A.mem_iff_le_index hπ (smul_ne_zero ha (w.ne_zero j)), C.mem_iff_le_index hπ ha,
    ceilDiv_le_iff hd, hAj, hCi, mul_add]
  omega

end Coordinates

section Scaling

variable (d : ℤ) (p : Fin n → ℤ)

omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
/-- Generated algebras commute with the repeated diagonal map. -/
theorem elementAlgebra_diagonal (b : Module.End F E) :
    elementAlgebra (diagonal F w b) = (elementAlgebra b).map (diagonal F w) :=
  (AlgHom.map_adjoin_singleton (diagonal F w) b).symm

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem blockEntry_add (x y : Module.End F V) (j l : Fin n) :
    blockEntry w (x + y) j l = blockEntry w x j l + blockEntry w y j l := by
  ext a
  simp

omit [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem blockEntry_zero (j l : Fin n) : blockEntry w (0 : Module.End F V) j l = 0 := by
  ext a
  simp

private theorem ceilDiv_mul (hd : 0 < d) (k : ℤ) : ceilDiv (d * k) d = k := by
  rw [← zero_add (d * k), ceilDiv_add_mul hd, ceilDiv_zero, zero_add]

variable (hw : RelSplits (L := E) A w) (hd : 0 < d)
  (hcoord : ScaledLatticeCoordinates A C w d p) (j₀ : Fin n)

include hw hd hcoord in
private theorem adjointLattice_le_at_scaled_succ (b : Module.End F E)
    (hbn : NormalizingUnits C (elementAlgebra b))
    (k : ℤ) (hk : criticalExponent C b ≤ (k : WithBot ℤ)) :
    adjointLattice A (diagonal F w b) (d * k + 1) ≤
      centralizerLattice A (diagonal F w b) 0 ⊔ A.endFiltration 1 := by
  classical
  let : FiniteDimensional F E := C.finiteDimensional
  obtain ⟨hb, hbnorm⟩ := isField_of_normalizingUnits C hbn
  intro Y hY
  have hY0 : Y ∈ A.endFiltration 0 := hY.1
  have hYcomm : diagonal F w b * Y - Y * diagonal F w b ∈ A.endFiltration (d * k + 1) := hY.2
  have hblock (j l : Fin n) : ∃ z : Module.End F E,
      b * z - z * b = 0 ∧ blockEntry w Y j l - z ∈
        C.endFiltration (ceilDiv (1 + p l - p j) d) := by
    have h := (blockFiltration A C w d p hw hd hcoord _ _).mp hYcomm j l
    rw [blockEntry_commutator,
      show d * k + 1 + p l - p j = (1 + p l - p j) + d * k by omega,
      ceilDiv_add_mul hd] at h
    exact exists_commute_sub_mem C b hb hbnorm hk _ _ h
  choose M hMcomm hMerr using hblock
  let Z := assembleBlocks w M
  have hZ (j l : Fin n) : blockEntry w Z j l = M j l :=
    blockEntry_assembleBlocks w M j l
  have herror : Y - Z ∈ A.endFiltration 1 := by
    apply (blockFiltration A C w d p hw hd hcoord _ _).mpr
    intro j l
    rw [blockEntry_sub, hZ]
    exact hMerr j l
  have hZ0 : Z ∈ A.endFiltration 0 := by
    have h := sub_mem hY0 (A.endFiltration_antitone (show (0 : ℤ) ≤ 1 by decide) herror)
    rwa [sub_sub_cancel] at h
  have hZcomm : diagonal F w b * Z - Z * diagonal F w b = 0 := by
    apply eq_of_blockEntry_eq w
    intro j l
    rw [blockEntry_commutator, hZ, hMcomm, blockEntry_zero]
  exact Submodule.mem_sup.mpr ⟨Z, ⟨hZ0, hZcomm⟩, Y - Z, herror, by abel⟩

include hw hd hcoord j₀ in
omit [TopologicalSpace F] [IsNonarchimedeanLocalField F] in
private theorem scaled_mem_criticalIndexSet {b : Module.End F E} {k : ℤ}
    (hk : k ∈ criticalIndexSet C b) : d * k ∈ criticalIndexSet A (diagonal F w b) := by
  intro hamb
  apply hk
  intro y hy
  have hy0 : y ∈ C.endFiltration 0 := hy.1
  have hycomm : b * y - y * b ∈ C.endFiltration k := hy.2
  have hz0 : diagonal F w y ∈ A.endFiltration 0 := by
    rw [diagonal_mem_endFiltration_iff A C w d p hw hd hcoord j₀, ceilDiv_zero]
    exact hy0
  have hzcomm : diagonal F w b * diagonal F w y - diagonal F w y * diagonal F w b ∈
      A.endFiltration (d * k) := by
    rw [← map_mul, ← map_mul, ← map_sub,
      diagonal_mem_endFiltration_iff A C w d p hw hd hcoord j₀, ceilDiv_mul d hd]
    exact hycomm
  obtain ⟨z, hz, e, he, hze⟩ := Submodule.mem_sup.mp (hamb ⟨hz0, hzcomm⟩)
  have hz₀ : z ∈ A.endFiltration 0 := hz.1
  have hzc : diagonal F w b * z - z * diagonal F w b = 0 := hz.2
  have hentry₀ := (blockFiltration A C w d p hw hd hcoord _ _).mp hz₀ j₀ j₀
  rw [zero_add, sub_self, ceilDiv_zero] at hentry₀
  have hentryc := congrArg (fun Z => blockEntry w Z j₀ j₀) hzc
  rw [blockEntry_commutator, blockEntry_zero] at hentryc
  have hentry₁ := (blockFiltration A C w d p hw hd hcoord _ _).mp he j₀ j₀
  rw [add_sub_cancel_right, ceilDiv_one hd] at hentry₁
  refine Submodule.mem_sup.mpr
    ⟨blockEntry w z j₀ j₀, ⟨hentry₀, hentryc⟩, blockEntry w e j₀ j₀, hentry₁, ?_⟩
  rw [← blockEntry_add, hze, blockEntry_diagonal, ite_eq_left rfl]

/-- Over a nonarchimedean local field `F`, under the split scaled-coordinate hypotheses,
diagonal embedding multiplies the critical exponent by the scale (and preserves the scalar
value `⊥`). Every hypothesis is a binder of this definition, not a section variable. -/
def DiagonalCriticalExponentStatement {F : Type uF} [Field F] [ValuativeRel F]
    [TopologicalSpace F] [IsNonarchimedeanLocalField F] {E : Type uE} [Field E] [Algebra F E]
    {V : Type uV} [AddCommGroup V] [Module F V] [Module E V] [IsScalarTower F E V]
    (A : LatticeChain 𝒪[F] F V) (C : LatticeChain 𝒪[F] F E) {n : ℕ}
    (w : Module.Basis (Fin n) E V) (d : ℤ) (p : Fin n → ℤ) : Prop :=
  RelSplits (L := E) A w → 0 < d → ScaledLatticeCoordinates A C w d p →
    Nonempty (Fin n) → ∀ (b : Module.End F E), NormalizingUnits C (elementAlgebra b) →
      criticalExponent A (diagonal F w b) = WithBot.map (fun k => d * k) (criticalExponent C b)

/-- Entrywise adjoint exactness gives the upper bound; the diagonal lifts a line obstruction. -/
theorem diagonalCriticalExponent : DiagonalCriticalExponentStatement A C w d p := by
  intro hw hd hcoord ⟨j⟩ b hbn
  by_cases hscalar : elementAlgebra b = ⊥
  · have hscalar' : elementAlgebra (diagonal F w b) = ⊥ := by
      rw [elementAlgebra_diagonal, hscalar, Algebra.map_bot]
    unfold criticalExponent
    rw [ite_eq_left hscalar, ite_eq_left hscalar', WithBot.map_bot]
  · let : FiniteDimensional F E := C.finiteDimensional
    obtain ⟨hb, hbnorm⟩ := isField_of_normalizingUnits C hbn
    obtain ⟨k, hk, hkb⟩ := exists_isGreatest_criticalIndexSet C b hb hbnorm hscalar
    have hnon : elementAlgebra (diagonal F w b) ≠ ⊥ := by
      intro h
      apply hscalar
      apply Subalgebra.map_injective (diagonal_injective w j)
      rw [← elementAlgebra_diagonal, h, Algebra.map_bot]
    have hu := adjointLattice_le_at_scaled_succ A C w d p hw hd hcoord b hbn k hkb.le
    have hg : IsGreatest (criticalIndexSet A (diagonal F w b)) (d * k) := by
      refine ⟨scaled_mem_criticalIndexSet A C w d p hw hd hcoord j hk.1, ?_⟩
      intro i hi
      by_contra! h
      apply hi
      intro x hx
      exact hu ⟨hx.1, A.endFiltration_antitone (show d * k + 1 ≤ i by omega) hx.2⟩
    rw [hkb, WithBot.map_coe]
    unfold criticalExponent
    rw [ite_eq_right hnon, hg.csSup_eq]

end Scaling

end Langlands.BushnellKutzko.PureApproximation

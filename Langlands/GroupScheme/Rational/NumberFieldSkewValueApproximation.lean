import Langlands.GroupScheme.Quaternionic.QuaternionicPureCongruenceOpen
import Langlands.GroupScheme.Quaternionic.SkewHermitianRowRepresentation
import Langlands.GroupScheme.Rational.NumberFieldBinarySkewRepresentation
import Langlands.Global.GlobalCompletionWeakApproximation
import Langlands.Global.AdelicSpaceLocalFields

/-! # Simultaneous approximation of opposite skew values -/

noncomputable section

universe u w

open Filter Topology NumberField
open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2700000

namespace Langlands.Global

/-- Weak approximation simultaneously in all coordinates of a finite vector. -/
theorem exists_numberField_vector_mem_open {F : Type u} [Field F] [NumberField F]
    {I : Type w} (S : Finset (FinitePlace F))
    (U : ∀ v : InfinitePlace F, Set (I → v.Completion))
    (W : ∀ v : S, Set (I → FiniteCompletion F v.1))
    (hU : ∀ v, IsOpen (U v)) (hW : ∀ v, IsOpen (W v))
    (hUn : ∀ v, (U v).Nonempty) (hWn : ∀ v, (W v).Nonempty) :
    ∃ a : I → F, (∀ v, (fun i => algebraMap F v.Completion (a i)) ∈ U v) ∧
      ∀ v : S, (fun i => algebraMap F (FiniteCompletion F v.1) (a i)) ∈ W v := by
  let P := (∀ v : InfinitePlace F, v.Completion) × (∀ v : S, FiniteCompletion F v.1)
  let Q := (∀ v : InfinitePlace F, I → v.Completion) × (∀ v : S, I → FiniteCompletion F v.1)
  let transpose (a : I → P) : Q := ⟨fun v i => (a i).1 v, fun v i => (a i).2 v⟩
  have hsurj : Function.Surjective transpose := fun a => ⟨fun i => ⟨fun v => a.1 v i, fun v => a.2 v i⟩, rfl⟩
  have hcont : Continuous transpose :=
    (continuous_pi fun v => continuous_pi fun i =>
      (continuous_apply v).comp (continuous_fst.comp (continuous_apply i))).prodMk
      (continuous_pi fun v => continuous_pi fun i =>
        (continuous_apply v).comp (continuous_snd.comp (continuous_apply i)))
  have hd := hsurj.denseRange.comp
    (DenseRange.piMap fun _ : I => denseRange_numberFieldFiniteCompletionDiagonal F S) hcont
  obtain ⟨a, ha⟩ := hd.exists_mem_open
    ((isOpen_set_pi Set.finite_univ fun v _ => hU v).prod
      (isOpen_set_pi Set.finite_univ fun v _ => hW v))
    ((Set.univ_pi_nonempty_iff.mpr hUn).prod (Set.univ_pi_nonempty_iff.mpr hWn))
  exact ⟨a, fun v => ha.1 v (Set.mem_univ v), fun v => ha.2 v (Set.mem_univ v)⟩

end Langlands.Global

namespace Langlands.GroupScheme.Quaternionic.FirstKindInvolution

open FiniteAlgebraUnits.MatrixPoints

section Coordinates

variable {F D R : Type u} [Field F] [DivisionRing D] [Algebra F D] [CommRing R] [Algebra F R]
  [FiniteDimensional F D] {n : ℕ} (τ : FirstKindInvolution F D)

local notation "A" => R ⊗[F] D
local notation "bD" => Module.finBasis F D
local notation "J" => Fin n × Fin (Module.finrank F D)

private def rowOfCoordinates (a : J → R) : Fin n → A :=
  fun i => ((bD).baseChange R).equivFun.symm (fun j => a (i, j))

private theorem rowOfCoordinates_algebraMap (a : J → F) :
    rowOfCoordinates (D := D) (fun p => algebraMap F R (a p)) =
      fun i => ((1 : R) ⊗ₜ[F] (bD).equivFun.symm (fun j => a (i, j))) := by
  funext i
  apply ((bD).baseChange R).equivFun.injective
  rw [rowOfCoordinates, LinearEquiv.apply_symm_apply]
  funext j
  change algebraMap F R (a (i, j)) =
    ((bD).baseChange R).repr ((1 : R) ⊗ₜ[F] (bD).equivFun.symm (fun k => a (i, k))) j
  rw [Module.Basis.baseChange_repr_tmul, Algebra.smul_def, mul_one]
  congr 1
  exact (congrFun ((bD).equivFun.apply_symm_apply (fun k => a (i, k))) j).symm

omit [FiniteDimensional F D] in
private theorem matrixSesqBilin_tmul (G : Matrix (Fin n) (Fin n) D) (x y : Fin n → D) :
    (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G))
      (fun i => (1 : R) ⊗ₜ[F] x i) (fun i => (1 : R) ⊗ₜ[F] y i) =
      (1 : R) ⊗ₜ[F] τ.sesqForm G x y := by
  simp only [matrixSesqBilin_apply, coefficientEquiv_tmul, baseChange_tmul,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, sesqForm, TensorProduct.tmul_sum]

end Coordinates

section Local

variable {F D R : Type u} [Field F] [DivisionRing D] [Algebra F D] [CommRing R] [Algebra F R]
  {n : ℕ} (τ : FirstKindInvolution F D)
  (H : Matrix (Fin 2) (Fin 2) D) (G : Matrix (Fin n) (Fin n) D)

local notation "A" => R ⊗[F] D
local notation "barR" => FirstKindInvolution.baseChange τ R
local notation "valueR[" M "]" => matrixSesqBilin barR (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] M))

/-- The two skew Gram matrices have opposite invertible values over the coefficient field. -/
def HasOppositeUnitValues : Prop :=
  ∃ (x : Fin n → A) (y : Fin 2 → A), IsUnit (-(valueR[G] x x)) ∧ valueR[H] y y = -(valueR[G] x x)

private theorem neg_self_is_skew (hG : τ.IsAntihermitian G) (x : Fin n → A) :
    barR (-(valueR[G] x x)) = -(-(valueR[G] x x)) := by
  have hG' : (barR).matrix (Fin n) (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G)) =
      -(coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G)) := by
    ext i j
    have h : τ (G j i) = -(G i j) := congrArg (fun M : Matrix (Fin n) (Fin n) D => M i j) hG.1
    rw [FirstKindInvolution.matrix_apply, Matrix.neg_apply, coefficientEquiv_tmul,
      coefficientEquiv_tmul, baseChange_tmul, h, TensorProduct.tmul_neg]
  rw [FirstKindInvolution.map_neg, neg_neg]
  exact ((barR).matrixSesqBilin_swap_of_skew hG' x x).symm

end Local

section OpenValues

variable {F D R : Type u} [Field F] [CharZero F] [DivisionRing D] [Algebra F D]
  [Algebra.IsCentral F D] [FiniteDimensional F D] [NontriviallyNormedField R] [CompleteSpace R] [Algebra F R]
  {n : ℕ} (σ : FirstKindInvolution F D) (hdim : Module.finrank F D = 4)
  (hsym : Module.finrank F σ.symmetricSubspace = 3)
  (H : Matrix (Fin 2) (Fin 2) D) (G : Matrix (Fin n) (Fin n) D)

local notation "τ" => σ.quaternionConjugation hdim hsym
local notation "A" => R ⊗[F] D
local notation "J" => Fin n × Fin (Module.finrank F D)
local notation "barR" => FirstKindInvolution.baseChange τ R
local notation "valueR[" M "]" => matrixSesqBilin barR (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] M))

private theorem exists_open_coordinates_of_opposite_unit (hG : (τ).IsAntihermitian G)
    (h : HasOppositeUnitValues (R := R) τ H G) :
    ∃ U : Set (J → R), IsOpen U ∧ U.Nonempty ∧ ∀ a ∈ U,
      let x := rowOfCoordinates (D := D) a
      IsUnit (-(valueR[G] x x)) ∧ ∃ y, valueR[H] y y = -(valueR[G] x x) := by
  obtain ⟨x, y, hx, hy⟩ := h
  let : TopologicalSpace A := moduleTopology R A
  let : IsModuleTopology R A := ⟨rfl⟩
  let : IsTopologicalRing A := IsModuleTopology.isTopologicalRing R A
  let e := ((Module.finBasis F D).baseChange R).equivFun
  let a₀ : J → R := fun i => e (x i.1) i.2
  have hx₀ : rowOfCoordinates (D := D) a₀ = x := by
    funext i
    change e.symm (e (x i)) = x i
    exact e.symm_apply_apply (x i)
  let f : (J → R) → A := fun a => -(valueR[G] (rowOfCoordinates a) (rowOfCoordinates a))
  have hc : Continuous f := by
    have hrow (i : Fin n) : Continuous (fun a : J → R => rowOfCoordinates (D := D) a i) :=
      (IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap).comp
        (continuous_pi fun j => continuous_apply (i, j))
    have hbar : Continuous (barR).toLinearMap := IsModuleTopology.continuous_of_linearMap _
    change Continuous (fun a : J → R => -(valueR[G] (rowOfCoordinates a) (rowOfCoordinates a)))
    simp only [matrixSesqBilin_apply]
    exact (continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hrow i).mul continuous_const).mul (hbar.comp (hrow j))).neg
  have hf₀ : f a₀ = -(valueR[G] x x) := by
    change -(valueR[G] (rowOfCoordinates a₀) (rowOfCoordinates a₀)) = _
    rw [hx₀]
  have hskew : barR (hx.unit : A) = -(hx.unit : A) := by
    rw [hx.unit_spec]
    exact neg_self_is_skew τ G hG x
  obtain ⟨O, hO, hOo, hxc⟩ := mem_nhds_iff.mp (quaternionicPureCongruenceOpen F D R σ hdim hsym hx.unit hskew)
  have hmem : f a₀ ∈ O := by rw [hf₀, ← hx.unit_spec]; exact hxc
  refine ⟨f ⁻¹' O, hOo.preimage hc, ⟨a₀, hmem⟩, fun a ha => ?_⟩
  have hnew : barR (f a) = -(f a) := neg_self_is_skew τ G hG _
  obtain ⟨u, hu⟩ := hO ha hnew
  rw [hx.unit_spec] at hu
  have hu' : IsUnit (barR (u : A)) :=
    ⟨⟨barR (u : A), barR (↑u⁻¹ : A),
      by rw [← (barR).map_mul, Units.inv_mul, (barR).map_one],
      by rw [← (barR).map_mul, Units.mul_inv, (barR).map_one]⟩, rfl⟩
  refine ⟨?_, fun i => (u : A) * y i, ?_⟩
  · change IsUnit (f a)
    rw [← hu]
    exact (u.isUnit.mul hx).mul hu'
  · rw [(barR).matrixSesqBilin_mul_left, (barR).matrixSesqBilin_mul_right, hy, ← mul_assoc]
    exact hu

end OpenValues

/-- Opposite local units and almost-everywhere binary representation give
  a global complementary row whose nonzero opposite value is locally represented everywhere. -/
def NumberFieldSkewValueApproximationStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [Algebra.IsCentral F D] [FiniteDimensional F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (n : ℕ) (H : Matrix (Fin 2) (Fin 2) D) (G : Matrix (Fin n) (Fin n) D),
    τ.IsAntihermitian G →
    (∀ v : Global.Place F, HasOppositeUnitValues (R := Global.placeCompletion F v) τ H G) →
    (∀ᶠ v : Global.FinitePlace F in cofinite, let R := Global.FiniteCompletion F v
      ∀ c : R ⊗[F] D, τ.baseChange R c = -c →
        ∃ y, (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)) y y = c) →
    ∃ x : Fin n → D, let c := -(τ.sesqForm G x x)
      c ≠ 0 ∧ c ∈ τ.alternatingSubspace ∧ τ.IsLocallyRepresented H c

theorem numberFieldSkewValueApproximation : NumberFieldSkewValueApproximationStatement.{u} := by
  classical
  intro F D _ _ _ _ _ _ σ hdim hsym τ n H G hG hl hg
  let J := Fin n × Fin (Module.finrank F D)
  let good (v : Global.FinitePlace F) : Prop :=
    let R := Global.FiniteCompletion F v
    ∀ c : R ⊗[F] D, τ.baseChange R c = -c →
      ∃ y, (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)) y y = c
  have hbad : {v | ¬ good v}.Finite := Filter.eventually_cofinite.mp hg
  let S := hbad.toFinset
  have hg' (v : Global.FinitePlace F) (hv : v ∉ S) : good v :=
    of_not_not (fun hn => hv (hbad.mem_toFinset.mpr hn))
  have localOpen (R : Type u) [NontriviallyNormedField R] [CompleteSpace R] [Algebra F R]
      (h : HasOppositeUnitValues (R := R) τ H G) :
      ∃ U : Set (J → R), IsOpen U ∧ U.Nonempty ∧ ∀ a ∈ U,
        let x := rowOfCoordinates (D := D) a
        let c := -((τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G)) x x)
        IsUnit c ∧ ∃ y, (τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] H)) y y = c :=
    exists_open_coordinates_of_opposite_unit (R := R) σ hdim hsym H G hG h
  have hi (v : InfinitePlace F) := by
    let : NontriviallyNormedField v.Completion := Global.AdelicSpaceLocalFields.infiniteNormedField F v
    exact localOpen v.Completion (hl (.inl v))
  have hf (v : S) := by
    let : NontriviallyNormedField (Global.FiniteCompletion F v.1) :=
      Global.AdelicSpaceLocalFields.normedField (𝓞 F) F v.1
    exact localOpen (Global.FiniteCompletion F v.1) (hl (.inr v.1))
  choose U hU hUn hUok using hi
  choose W hW hWn hWok using hf
  obtain ⟨a, hai, haf⟩ := Global.exists_numberField_vector_mem_open S U W hU hW hUn hWn
  let x : Fin n → D := fun i => (Module.finBasis F D).equivFun.symm (fun j => a (i, j))
  let c := -(τ.sesqForm G x x)
  have htx (R : Type u) [CommRing R] [Algebra F R] :
      let xR := rowOfCoordinates (D := D) (fun p => algebraMap F R (a p));
      -((τ.baseChange R).matrixSesqBilin (coefficientEquiv F D R ((1 : R) ⊗ₜ[F] G)) xR xR) =
        (1 : R) ⊗ₜ[F] c := by
    dsimp only
    rw [rowOfCoordinates_algebraMap, matrixSesqBilin_tmul, TensorProduct.tmul_neg]
  have hci (v : InfinitePlace F) : IsUnit ((1 : v.Completion) ⊗ₜ[F] c) ∧
      ∃ y, (τ.baseChange v.Completion).matrixSesqBilin
        (coefficientEquiv F D v.Completion ((1 : v.Completion) ⊗ₜ[F] H)) y y = (1 : v.Completion) ⊗ₜ[F] c := by
    have h := hUok v _ (hai v)
    dsimp only at h
    rw [htx v.Completion] at h
    exact h
  have hc : c ≠ 0 := by
    intro h
    let v : InfinitePlace F := Classical.choice inferInstance
    have hv := (hci v).1.ne_zero
    rw [h, TensorProduct.tmul_zero] at hv
    exact hv rfl
  have hca : c ∈ τ.alternatingSubspace :=
    τ.alternatingSubspace.neg_mem (τ.sesqForm_self_mem_alternatingSubspace hG x)
  refine ⟨x, hc, hca, fun v => ?_⟩
  rcases v with v | v
  · exact (hci v).2
  · let R := Global.FiniteCompletion F v
    by_cases hv : v ∈ S
    · have h := hWok ⟨v, hv⟩ _ (haf ⟨v, hv⟩)
      dsimp only at h
      rw [htx R] at h
      exact h.2
    · apply hg' v hv
      rw [FirstKindInvolution.baseChange_tmul, τ.map_eq_neg_of_mem_alternating hca, TensorProduct.tmul_neg]

end Langlands.GroupScheme.Quaternionic.FirstKindInvolution

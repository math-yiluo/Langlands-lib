import Langlands.BaseChange.Norm
import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.Eigenspace.Semisimple
import Mathlib.LinearAlgebra.Eigenspace.Zero
import Mathlib.LinearAlgebra.Matrix.Block
import Mathlib.LinearAlgebra.Trace
import Mathlib.RingTheory.Artinian.Module
import Mathlib.RingTheory.Trace.Basic

/-!
# Surjectivity in the upper triangular twisted conjugation map

The right-translated differential at the two identity matrices is onto at a
σ-regular parameter. See the paired Markdown for the trace-pairing argument.
-/

noncomputable section

universe u v

namespace Langlands.BaseChange

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E]
variable {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) E

/-- The algebra of upper triangular matrices giving the tangent directions of the
upper triangular subgroup. -/
def upperTriangularSubalgebra (F : Type u) (E : Type v) [Field F] [CommRing E]
    [Algebra F E] (n : ℕ) : Subalgebra F (Matrix (Fin n) (Fin n) E) where
  carrier := {X | X.IsUpperTriangular}
  mul_mem' := Matrix.BlockTriangular.mul
  one_mem' := Matrix.blockTriangular_one
  add_mem' := Matrix.BlockTriangular.add
  zero_mem' := Matrix.blockTriangular_zero
  algebraMap_mem' a := by
    intro i j hij
    change j < i at hij
    simp [Matrix.algebraMap_matrix_apply, ne_of_gt hij]

@[simp]
theorem mem_upperTriangularSubalgebra (X : Mat) :
    X ∈ upperTriangularSubalgebra F E n ↔ ∀ i j : Fin n, j < i → X i j = 0 :=
  Iff.rfl

/-- The linear automorphism `X ↦ δ σ(X) δ⁻¹` on the full matrix algebra. -/
def twistedMatrixConj (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) : Mat ≃ₗ[F] Mat :=
  σ.mapMatrix.toLinearEquiv.trans
    ((δ.mulLeftLinearEquiv F Mat).trans (δ⁻¹.mulRightLinearEquiv F))

@[simp]
theorem twistedMatrixConj_apply (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) (X : Mat) :
    twistedMatrixConj σ δ X = (δ : Mat) * σ.mapMatrix X * ((δ⁻¹ : GeneralLinear n E) : Mat) :=
  rfl

/-- The partial differential `X − Ad(δ)σ(X) + Ad(δ)σ(Y)`, with upper triangular `Y`. -/
def twistedTriangularDifferential (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) :
    (Mat × upperTriangularSubalgebra F E n) →ₗ[F] Mat :=
  let T := (twistedMatrixConj σ δ).toLinearMap
  ((LinearMap.id - T).comp (LinearMap.fst F _ _)) +
    T.comp ((upperTriangularSubalgebra F E n).val.toLinearMap.comp (LinearMap.snd F _ _))

@[simp]
theorem twistedTriangularDifferential_apply
    (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) (X : Mat) (Y : upperTriangularSubalgebra F E n) :
    twistedTriangularDifferential σ δ (X, Y) =
      X - twistedMatrixConj σ δ X + twistedMatrixConj σ δ Y :=
  rfl

section Trace

variable [CharZero F] [Module.Finite F E] [IsReduced E]

private theorem eq_zero_of_trace_mul_eq_zero (a : E)
    (ha : ∀ b : E, Algebra.trace F E (a * b) = 0) : a = 0 := by
  classical
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let S (i : MaximalSpectrum E) := E ⧸ i.asIdeal
  let (i : MaximalSpectrum E) : Field (S i) := IsArtinianRing.fieldOfSubtypeIsMaximal E i
  let e : E ≃+* ∀ i, S i := IsArtinianRing.equivPi E
  let b := e.symm fun i => (e a i)⁻¹
  let d := a * b
  have hd (i : MaximalSpectrum E) : e d i = e a i * (e a i)⁻¹ := by
    simp [d, b]
  have hdd : IsIdempotentElem d := by
    apply e.injective
    funext i
    rw [map_mul, Pi.mul_apply, hd]
    by_cases hi : e a i = 0 <;> simp [hi, mul_inv_cancel₀]
  have hmul : IsIdempotentElem (Algebra.lmul F E d) := by
    change _ * _ = _
    rw [← map_mul, hdd.eq]
  have hzero := (LinearMap.IsIdempotentElem.trace_eq_zero_iff hmul).mp (ha b)
  have hd0 : d = 0 := by
    simpa using LinearMap.congr_fun hzero (1 : E)
  apply e.injective
  funext i
  by_contra hi
  have : e d i = 1 := (hd i).trans (mul_inv_cancel₀ (by simpa using hi))
  simp [hd0] at this

/-- Matrix trace followed by coefficient trace, applied to a product. -/
def adjointTracePairing (F : Type u) (E : Type v) [Field F] [CommRing E]
    [Algebra F E] (n : ℕ) : LinearMap.BilinForm F (Matrix (Fin n) (Fin n) E) :=
  LinearMap.compr₂ (LinearMap.mul F _) ((Algebra.trace F E).comp (Matrix.traceLinearMap (Fin n) F E))

omit [CharZero F] [Module.Finite F E] [IsReduced E] in
theorem adjointTracePairing_apply (X Y : Mat) :
    adjointTracePairing F E n X Y = Algebra.trace F E (Matrix.trace (X * Y)) :=
  rfl

private theorem matrixTracePairing_separates (Z : Mat)
    (hZ : ∀ X : Mat, adjointTracePairing F E n Z X = 0) : Z = 0 := by
  ext i j
  change Z i j = 0
  apply eq_zero_of_trace_mul_eq_zero (F := F)
  intro a
  simpa [adjointTracePairing_apply, Matrix.trace_mul_single, smul_eq_mul, mul_comm a] using
    hZ (Matrix.single j i a)

private theorem matrixTracePairing_nondegenerate : (adjointTracePairing F E n).Nondegenerate := by
  refine ⟨matrixTracePairing_separates, ?_⟩
  intro Z hZ
  apply matrixTracePairing_separates (F := F)
  intro X
  rw [adjointTracePairing_apply, Matrix.trace_mul_comm, ← adjointTracePairing_apply]
  exact hZ X

omit [CharZero F] [Module.Finite F E] [IsReduced E] in
/-- Twisted matrix conjugation preserves the trace pairing. -/
theorem adjointTracePairing_preserved
    (σ : E ≃ₐ[F] E) (δ : GeneralLinear n E) (X Y : Mat) :
    adjointTracePairing F E n (twistedMatrixConj σ δ X) (twistedMatrixConj σ δ Y) =
      adjointTracePairing F E n X Y := by
  have hmul : twistedMatrixConj σ δ X * twistedMatrixConj σ δ Y =
      twistedMatrixConj σ δ (X * Y) := by
    simp only [twistedMatrixConj_apply, map_mul, mul_assoc, Units.inv_mul_cancel_left]
  rw [adjointTracePairing_apply, hmul, twistedMatrixConj_apply, Matrix.trace_mul_comm,
    ← mul_assoc, Units.inv_mul, one_mul, AlgEquiv.mapMatrix_apply,
    ← AddMonoidHom.map_trace σ, Algebra.trace_eq_of_algEquiv, adjointTracePairing_apply]

private theorem isNilpotent_of_annihilates_upperTriangular (Z : Mat)
    (h : ∀ Y : upperTriangularSubalgebra F E n, adjointTracePairing F E n Z Y = 0) :
    IsNilpotent Z := by
  have hbelow (i j : Fin n) (hij : j ≤ i) : Z i j = 0 := by
    apply eq_zero_of_trace_mul_eq_zero (F := F)
    intro a
    have hu : Matrix.single j i a ∈ upperTriangularSubalgebra F E n := by
      intro p q hpq
      apply Matrix.single_apply_of_ne
      rintro ⟨rfl, rfl⟩
      exact (not_lt_of_ge hij hpq)
    simpa [adjointTracePairing_apply, Matrix.trace_mul_single, smul_eq_mul, mul_comm a] using
      h ⟨Matrix.single j i a, hu⟩
  have hpow (k : ℕ) : ∀ i j : Fin n, (j : ℕ) < i + k → (Z ^ k) i j = 0 := by
    induction k with
    | zero =>
      intro i j hij
      have hne : i ≠ j := by
        rintro rfl
        omega
      simp [Matrix.one_apply_ne hne]
    | succ k ih =>
      intro i j hij
      rw [pow_succ, Matrix.mul_apply]
      apply Finset.sum_eq_zero
      intro p _
      by_cases hp : (p : ℕ) < i + k
      · rw [ih _ _ hp, zero_mul]
      · have hpj : j ≤ p := by
          change (j : ℕ) ≤ p
          omega
        rw [hbelow _ _ hpj, mul_zero]
  refine ⟨n, Matrix.ext fun i j => hpow n i j ?_⟩
  have := j.isLt
  omega

end Trace

section Centralizer

open Module

private theorem linearMap_eq_zero_of_nilpotent_of_finrank_le_one
    {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (hV : finrank K V ≤ 1) {g : End K V} (hg : IsNilpotent g) : g = 0 := by
  obtain ⟨v, hv⟩ := finrank_le_one_iff.mp hV
  obtain ⟨c, hc⟩ := hv (g v)
  have hpow (k : ℕ) : (g ^ k) v = c ^ k • v := by
    induction k with
    | zero => simp
    | succ k ih => rw [pow_succ', End.mul_apply, ih, map_smul, ← hc, smul_smul, pow_succ]
  obtain ⟨k, hk⟩ := hg
  have hz : c ^ k • v = 0 := by rw [← hpow, hk, LinearMap.zero_apply]
  have hgv : g v = 0 := by
    rcases smul_eq_zero.mp hz with hc0 | hv0
    · rw [← hc, eq_zero_of_pow_eq_zero hc0, zero_smul]
    · rw [hv0, map_zero]
  ext x
  obtain ⟨a, ha⟩ := hv x
  rw [← ha, map_smul, hgv, smul_zero, LinearMap.zero_apply]

private theorem matrix_eq_zero_of_commute_of_separable_of_isAlgClosed
    {K : Type*} [Field K] [IsAlgClosed K] {A B : Matrix (Fin n) (Fin n) K}
    (hA : A.charpoly.Separable) (hAB : Commute A B) (hB : IsNilpotent B) : B = 0 := by
  let f : End K (Fin n → K) := A.toLin'
  let g : End K (Fin n → K) := B.toLin'
  have hf : f.charpoly.Separable := by simpa only [f, Matrix.charpoly_toLin'] using hA
  have hss := End.isSemisimple_of_squarefree_aeval_eq_zero hf.squarefree f.aeval_self_charpoly
  have hfg : Commute f g := hAB.map Matrix.toLinAlgEquiv'
  have hgn : IsNilpotent g := hB.map Matrix.toLinAlgEquiv'
  have hle (c : K) : f.eigenspace c ≤ LinearMap.ker g := by
    have hm : Set.MapsTo g (f.eigenspace c) (f.eigenspace c) :=
      End.mapsTo_genEigenspace_of_comm hfg c 1
    have hr : finrank K (f.eigenspace c) ≤ 1 :=
      (LinearMap.finrank_eigenspace_le f c).trans (Polynomial.rootMultiplicity_le_one_of_separable hf c)
    have hzero := linearMap_eq_zero_of_nilpotent_of_finrank_le_one hr (End.isNilpotent.restrict hm hgn)
    intro x hx
    exact LinearMap.mem_ker.mpr (congrArg Subtype.val (LinearMap.congr_fun hzero ⟨x, hx⟩))
  have hg : g = 0 := LinearMap.ker_eq_top.mp <| top_le_iff.mp <| by
    rw [← hss.iSup_eigenspace_eq_top]
    exact iSup_le hle
  exact Matrix.toLinAlgEquiv'.injective (hg.trans (map_zero Matrix.toLinAlgEquiv').symm)

private theorem matrix_eq_zero_of_commute_baseChange_of_separable [Module.Finite F E] [IsReduced E]
    {A : Matrix (Fin n) (Fin n) F} {B : Mat} (hA : A.charpoly.Separable)
    (hAB : Commute (A.map (algebraMap F E)) B) (hB : IsNilpotent B) : B = 0 := by
  classical
  let : IsArtinianRing E := IsArtinianRing.of_finite F E
  let S (i : MaximalSpectrum E) := E ⧸ i.asIdeal
  let (i : MaximalSpectrum E) : Field (S i) := IsArtinianRing.fieldOfSubtypeIsMaximal E i
  let e : E ≃+* ∀ i, S i := IsArtinianRing.equivPi E
  ext p q
  apply e.injective
  funext i
  let L := AlgebraicClosure (S i)
  let φ : E →+* L := (algebraMap (S i) L).comp ((Pi.evalRingHom S i).comp e.toRingHom)
  have hf : (A.map ((φ.comp (algebraMap F E)))).charpoly.Separable := by
    rw [Matrix.charpoly_map]
    exact hA.map
  have hc : Commute (A.map (φ.comp (algebraMap F E))) (B.map φ) := hAB.map φ.mapMatrix
  have hz := matrix_eq_zero_of_commute_of_separable_of_isAlgClosed hf hc (hB.map φ.mapMatrix)
  apply (algebraMap (S i) L).injective
  simpa [φ] using congrArg (fun X : Matrix (Fin n) (Fin n) L => X p q) hz

private theorem commute_cyclicNorm_of_fixed (σ : E ≃ₐ[F] E)
    (l : ℕ) (δ : GeneralLinear n E) (hσ : σ ^ l = 1) (Z : Mat)
    (hZ : twistedMatrixConj σ δ Z = Z) : Commute Z (cyclicNorm σ l δ : Mat) := by
  have hp (k : ℕ) :
      Z = (cyclicNorm σ k δ : Mat) * (σ ^ k).mapMatrix Z *
        ((cyclicNorm σ k δ)⁻¹ : GeneralLinear n E) := by
    induction k with
    | zero =>
      simp only [cyclicNorm_zero, pow_zero, inv_one, Units.val_one, one_mul, mul_one]
      rfl
    | succ k ih =>
      have hf : (σ ^ k).mapMatrix Z =
          ((entrywiseAut (σ ^ k) n δ : GeneralLinear n E) : Mat) *
            (σ ^ (k + 1)).mapMatrix Z *
            ((entrywiseAut (σ ^ k) n δ)⁻¹ : GeneralLinear n E) := by
        have h := congrArg (fun X : Mat => (σ ^ k).mapMatrix X) hZ.symm
        rw [twistedMatrixConj_apply, map_mul, map_mul] at h
        have hcomp : (σ ^ k).mapMatrix (σ.mapMatrix Z) = (σ ^ (k + 1)).mapMatrix Z := by
          ext i j
          simp [pow_succ, AlgEquiv.mul_apply]
        rw [hcomp] at h
        rw [← map_inv]
        exact h
      calc
        Z = _ := ih
        _ = _ := by rw [hf, cyclicNorm_succ, mul_inv_rev]; simp only [Units.val_mul, mul_assoc]
  have h := hp l
  rw [hσ] at h
  change Z = (cyclicNorm σ l δ : Mat) * Z * ((cyclicNorm σ l δ)⁻¹ : GeneralLinear n E) at h
  change Z * (cyclicNorm σ l δ : Mat) = (cyclicNorm σ l δ : Mat) * Z
  nth_rw 1 [h]
  simp [mul_assoc]

private theorem matrix_eq_zero_of_isNilpotent_of_fixed [Module.Finite F E] [IsReduced E]
    (σ : E ≃ₐ[F] E) (l : ℕ) (δ : GeneralLinear n E) (hσ : σ ^ l = 1)
    (hδ : IsSigmaRegular σ l δ) (Z : Mat) (hn : IsNilpotent Z)
    (hz : twistedMatrixConj σ δ Z = Z) : Z = 0 := by
  obtain ⟨γ, ⟨g, hg⟩, hγ⟩ := hδ
  let N : GeneralLinear n E := cyclicNorm σ l δ
  let Z' : Mat := (g⁻¹ : GeneralLinear n E) * Z * (g : Mat)
  have hn' : IsNilpotent Z' := by
    obtain ⟨k, hk⟩ := hn
    refine ⟨k, ?_⟩
    change ((g⁻¹ : GeneralLinear n E) * Z * (g : Mat)) ^ k = 0
    rw [g.conj_pow', hk, mul_zero, zero_mul]
  have hc : Z * (N : Mat) = (N : Mat) * Z :=
    (commute_cyclicNorm_of_fixed σ l δ hσ Z hz).eq
  have hN : (g⁻¹ : GeneralLinear n E) * (N : Mat) * (g : Mat) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E) := congrArg Units.val hg
  have hc' : Commute ((γ : Matrix (Fin n) (Fin n) F).map (algebraMap F E)) Z' := by
    rw [← hN]
    change (_ * _ * _) * Z' = Z' * (_ * _ * _)
    calc
      _ = (g⁻¹ : GeneralLinear n E) * ((N : Mat) * Z) * (g : Mat) := by
        simp [Z', mul_assoc]
      _ = _ := by rw [← hc]; simp [Z', mul_assoc]
  have hzero := matrix_eq_zero_of_commute_baseChange_of_separable hγ hc' hn'
  calc
    Z = (g : Mat) * Z' * (g⁻¹ : GeneralLinear n E) := by simp [Z', mul_assoc]
    _ = 0 := by rw [hzero, mul_zero, zero_mul]

end Centralizer

/-- Surjectivity of the upper triangular differential at σ-regular parameters,
over finite reduced algebras in characteristic zero. -/
def TwistedTriangularDifferentialStatement : Prop :=
  ∀ (F : Type u) [Field F] [CharZero F] (E : Type v) [CommRing E] [Algebra F E]
    [Module.Finite F E] [IsReduced E] (n l : ℕ) (σ : E ≃ₐ[F] E),
    σ ^ l = 1 → ∀ δ : GeneralLinear n E, IsSigmaRegular σ l δ →
      Function.Surjective (twistedTriangularDifferential σ δ)

theorem twistedTriangularDifferential_surjective : TwistedTriangularDifferentialStatement.{u, v} := by
  intro F _ _ E _ _ _ _ n l σ hσ δ hδ
  let D := twistedTriangularDifferential σ δ
  let T := twistedMatrixConj σ δ
  let B := adjointTracePairing F E n
  let e := B.toDual matrixTracePairing_nondegenerate
  apply LinearMap.range_eq_top.mp
  rw [← Submodule.dualAnnihilator_eq_bot_iff]
  refine (Submodule.eq_bot_iff _).mpr fun f hf => ?_
  obtain ⟨Z, rfl⟩ := e.surjective f
  have hann (X : Matrix (Fin n) (Fin n) E) (Y : upperTriangularSubalgebra F E n) :
      B Z (D (X, Y)) = 0 :=
    (Submodule.mem_dualAnnihilator (e Z)).mp hf _ (LinearMap.mem_range_self D (X, Y))
  have hinv (X Y : Matrix (Fin n) (Fin n) E) : B (T X) (T Y) = B X Y :=
    adjointTracePairing_preserved σ δ X Y
  have hfix : T Z = Z := by
    apply eq_of_sub_eq_zero
    apply matrixTracePairing_separates (F := F)
    intro X
    obtain ⟨Y, rfl⟩ := T.surjective X
    change B (T Z - Z) (T Y) = 0
    rw [LinearMap.BilinForm.sub_left, hinv]
    simpa [D, T] using hann Y 0
  have htri (Y : upperTriangularSubalgebra F E n) : B Z Y = 0 := by
    rw [← hinv, hfix]
    simpa [D, T] using hann 0 Y
  have hz := matrix_eq_zero_of_isNilpotent_of_fixed σ l δ hσ hδ Z
    (isNilpotent_of_annihilates_upperTriangular Z htri) hfix
  simp [hz]

end Langlands.BaseChange

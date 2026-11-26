import Langlands.BaseChange.ExactRegularNormCentralizer
import Langlands.BaseChange.RegularNormCentralizerAlgebra
import Langlands.BaseChange.TwistedTriangularDifferential

/-! # The fixed space of the matrix adjoint action at a σ-regular element -/

noncomputable section

namespace Langlands.BaseChange

open JacquetLanglands Matrix Module _root_.Polynomial

universe u v

variable {F : Type u} [Field F] {E : Type v} [CommRing E] [Algebra F E] {n : ℕ}

local notation "Mat" => Matrix (Fin n) (Fin n) E
local notation "G" => GeneralLinear n E

/-- The adjoint actions compose by the semidirect product law. -/
theorem twistedMatrixConj_mul (σ τ : E ≃ₐ[F] E) (δ ε : G) :
    twistedMatrixConj σ δ * twistedMatrixConj τ ε =
      twistedMatrixConj (σ * τ) (δ * entrywiseAut σ n ε) := by
  apply LinearEquiv.ext
  intro X
  change twistedMatrixConj σ δ (twistedMatrixConj τ ε X) = _
  have hcomp : σ.mapMatrix (τ.mapMatrix X) = (σ * τ).mapMatrix X := rfl
  have hmap (g : G) : σ.mapMatrix (g : Mat) = (entrywiseAut σ n g : Mat) := rfl
  simp only [twistedMatrixConj_apply, map_mul, hcomp, hmap, _root_.mul_inv_rev, Units.val_mul, map_inv,
    mul_assoc]

/-- The `k`th adjoint power corresponds to the partial cyclic norm. -/
theorem twistedMatrixConj_pow (σ : E ≃ₐ[F] E) (δ : G) (k : ℕ) :
    twistedMatrixConj σ δ ^ k = twistedMatrixConj (σ ^ k) (cyclicNorm σ k δ) := by
  induction k with
  | zero =>
    apply LinearEquiv.ext
    intro X
    simp only [pow_zero, cyclicNorm_zero, twistedMatrixConj_apply, inv_one, Units.val_one,
      one_mul, mul_one]
    rfl
  | succ k ih => rw [pow_succ, ih, twistedMatrixConj_mul, ← pow_succ, cyclicNorm_succ]

variable (σ : E ≃ₐ[F] E)

/-- The fixed subspace in the matrix Lie algebra, taken over the base field. -/
def twistedAdjointFixed (δ : G) : Submodule F Mat :=
  Module.End.eigenspace (twistedMatrixConj σ δ).toLinearMap 1

@[simp]
theorem mem_twistedAdjointFixed {δ : G} {X : Mat} :
    X ∈ twistedAdjointFixed σ δ ↔ twistedMatrixConj σ δ X = X := by
  simp [twistedAdjointFixed]

private theorem commute_norm_of_adjointFixed {l : ℕ} (hσ : σ ^ l = 1) (δ : G) {X : Mat}
    (hX : X ∈ twistedAdjointFixed σ δ) : Commute X (cyclicNorm σ l δ : Mat) := by
  have hfix := (mem_twistedAdjointFixed σ).1 hX
  have hp (k : ℕ) : (twistedMatrixConj σ δ ^ k) X = X := by
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [pow_succ', LinearEquiv.mul_apply, ih, hfix]
  have h := hp l
  rw [twistedMatrixConj_pow, hσ, twistedMatrixConj_apply] at h
  change (cyclicNorm σ l δ : Mat) * X * ((cyclicNorm σ l δ)⁻¹ : G) = X at h
  change X * (cyclicNorm σ l δ : Mat) = (cyclicNorm σ l δ : Mat) * X
  nth_rw 1 [← h]
  simp [mul_assoc]

/-- Twisted conjugation gives a linear equivalence between fixed subspaces. -/
def twistedAdjointFixedConjEquiv (x δ : G) :
    twistedAdjointFixed σ δ ≃ₗ[F] twistedAdjointFixed σ (x⁻¹ * δ * entrywiseAut σ n x) := by
  let e := twistedMatrixConj (1 : E ≃ₐ[F] E) x⁻¹
  let d := x⁻¹ * δ * entrywiseAut σ n x
  have hc : e * twistedMatrixConj σ δ = twistedMatrixConj σ d * e := by
    rw [show e = twistedMatrixConj (1 : E ≃ₐ[F] E) x⁻¹ from rfl,
      twistedMatrixConj_mul, twistedMatrixConj_mul, one_mul, mul_one, entrywiseAut_one_apply]
    congr 1
    dsimp [d]
    rw [map_inv, mul_assoc, mul_inv_cancel, mul_one]
  have hact (X : Mat) : e (twistedMatrixConj σ δ X) = twistedMatrixConj σ d (e X) :=
    DFunLike.congr_fun hc X
  let f : twistedAdjointFixed σ δ →ₗ[F] twistedAdjointFixed σ d :=
    (e.toLinearMap.comp (twistedAdjointFixed σ δ).subtype).codRestrict _ fun X => by
      rw [mem_twistedAdjointFixed, LinearMap.comp_apply, Submodule.subtype_apply,
        LinearEquiv.coe_coe, ← hact, (mem_twistedAdjointFixed σ).1 X.property]
  apply LinearEquiv.ofBijective f
  refine ⟨fun X Y h => Subtype.ext (e.injective (congrArg Subtype.val h)), ?_⟩
  intro Y
  obtain ⟨X, hX⟩ := e.surjective Y.val
  have hfix : X ∈ twistedAdjointFixed σ δ := by
    apply (mem_twistedAdjointFixed σ).2
    apply e.injective
    rw [hact, hX, (mem_twistedAdjointFixed σ).1 Y.property]
  exact ⟨⟨X, hfix⟩, Subtype.ext hX⟩

/-- When the norm already equals a regular base matrix, evaluating its characteristic
algebra and extending scalars identifies that algebra with the adjoint fixed space. -/
def twistedAdjointFixedEquivRootOfNorm {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (δ : G) (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ)
    (hnorm : cyclicNorm σ l δ = baseChange F E n γ) :
    AdjoinRoot γ.val.charpoly ≃ₗ[F] twistedAdjointFixed σ δ := by
  let _ : Module.Finite F E := hE.1
  let _ : Nontrivial E := Module.finrank_pos_iff.mp (hE.2.1.symm ▸ hE.pos)
  let A := (baseChange F E n γ).val
  let j : Matrix (Fin n) (Fin n) F →ₐ[F] Mat := (Algebra.ofId F E).mapMatrix
  have hj : Function.Injective j := by
    intro X Y h
    exact Matrix.ext fun i k =>
      (algebraMap F E).injective (congrArg (fun Z : Mat => Z i k) h)
  have hσj (Y : Matrix (Fin n) (Fin n) F) : σ.mapMatrix (j Y) = j Y :=
    Matrix.ext fun i k => σ.commutes (Y i k)
  have hσA : σ.mapMatrix A = A := hσj γ.val
  have hδ : Commute δ (baseChange F E n γ) :=
    commute_of_cyclicNorm_eq_baseChange hE.pow_eq_one hnorm
  have hδA : Commute (δ : Mat) A := hδ.map (Units.coeHom _)
  let w := (regularCyclicBasis F n γ.val hγ).choose
  have hw : IsUnit (cyclicBasisMatrix γ.val w) :=
    (regularCyclicBasis F n γ.val hγ).choose_spec
  have hwE : IsUnit (cyclicBasisMatrix A (algebraMap F E ∘ w)) := by
    change IsUnit (cyclicBasisMatrix (γ.val.map (algebraMap F E)) (algebraMap F E ∘ w))
    rw [← cyclicBasisMatrix_map]
    exact hw.map (algebraMap F E).mapMatrix
  have hact (X : Mat) (hX : Commute X A) : twistedMatrixConj σ δ X = σ.mapMatrix X := by
    have hXσ := hX.map σ.mapMatrix
    rw [hσA] at hXσ
    have h := commute_of_commute_cyclicBasisMatrix hwE hXσ hδA
    rw [twistedMatrixConj_apply, ← h.eq]
    simp [mul_assoc]
  let ev := charpolyRootEvaluation γ.val
  let f := j.comp ev
  have hf (z : AdjoinRoot γ.val.charpoly) : f z ∈ twistedAdjointFixed σ δ := by
    have hc : Commute (ev z) γ.val := by
      have h := (Commute.all z (AdjoinRoot.root γ.val.charpoly)).map ev
      simpa only [ev, charpolyRootEvaluation_root] using h
    exact (mem_twistedAdjointFixed σ).2 ((hact (f z) (hc.map j)).trans (hσj _))
  let e := f.toLinearMap.codRestrict (twistedAdjointFixed σ δ) hf
  apply LinearEquiv.ofBijective e
  refine ⟨fun x y h => charpolyRootEvaluation_injective γ.val w hw
    (hj (congrArg Subtype.val h)), ?_⟩
  intro X
  have hXA : Commute X.val A := by
    simpa only [hnorm, A] using commute_norm_of_adjointFixed σ hE.pow_eq_one δ X.property
  have hXσ : σ.mapMatrix X.val = X.val :=
    (hact X.val hXA).symm.trans ((mem_twistedAdjointFixed σ).1 X.property)
  have hx (i k : Fin n) : ∃ y : F, algebraMap F E y = X.val i k :=
    hE.2.2.2.2 _ (congrArg (fun M : Mat => M i k) hXσ)
  choose y hy using hx
  let Y := Matrix.of y
  have hY : j Y = X.val := Matrix.ext hy
  have hYA : Commute Y γ.val := by
    apply hj
    rw [map_mul, map_mul, hY]
    exact hXA.eq
  obtain ⟨c, hc⟩ := exists_sum_pow_of_commute hw hYA
  let p : F[X] := ∑ i : Fin n, monomial (i : ℕ) (c i)
  have hev : ev (AdjoinRoot.mk _ p) = Y := by
    change charpolyRootEvaluation γ.val (AdjoinRoot.mk _ p) = Y
    rw [charpolyRootEvaluation_mk, hc, show p = ∑ i : Fin n, monomial (i : ℕ) (c i)
      from rfl, map_sum]
    simp only [aeval_monomial, Algebra.smul_def]
  refine ⟨AdjoinRoot.mk γ.val.charpoly p, ?_⟩
  apply Subtype.ext
  change j (ev (AdjoinRoot.mk _ p)) = X.val
  rw [hev, hY]

@[simp]
theorem twistedAdjointFixedEquivRootOfNorm_apply {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (δ : G) (γ : GeneralLinear n F) (hγ : IsRegularSemisimple γ)
    (hnorm : cyclicNorm σ l δ = baseChange F E n γ) (a : AdjoinRoot γ.val.charpoly) :
    (twistedAdjointFixedEquivRootOfNorm σ hE δ γ hγ hnorm a).val =
      (charpolyRootEvaluation γ.val a).map (algebraMap F E) :=
  rfl

/-- The fixed adjoint space at a σ-regular element has dimension `n` over `F`. -/
theorem finrank_twistedAdjointFixed_of_sigmaRegular {l : ℕ} (hE : IsCyclicAlgebra σ l)
    (δ : G) (hδ : IsSigmaRegular σ l δ) :
    Module.finrank F (twistedAdjointFixed σ δ) = n := by
  obtain ⟨γ, ⟨x, hx⟩, hγ⟩ := hδ
  let d := x⁻¹ * δ * entrywiseAut σ n x
  have hd : cyclicNorm σ l d = baseChange F E n γ := by
    rw [show d = x⁻¹ * δ * entrywiseAut σ n x from rfl,
      cyclicNorm_twistedConj, hE.pow_eq_one, entrywiseAut_one_apply, hx]
  rw [(twistedAdjointFixedConjEquiv σ x δ).finrank_eq,
    ← (twistedAdjointFixedEquivRootOfNorm σ hE d γ hγ hd).finrank_eq]
  rw [(AdjoinRoot.powerBasis' γ.val.charpoly_monic).finrank]
  change γ.val.charpoly.natDegree = n
  simp [Matrix.charpoly_natDegree_eq_dim]

end Langlands.BaseChange

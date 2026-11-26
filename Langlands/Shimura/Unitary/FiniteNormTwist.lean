import Langlands.Shimura.Unitary.FiniteSignedDeterminant
import Langlands.Shimura.Unitary.LocalHermitianWitt
import Langlands.Shimura.Unitary.SymmetricReducedCharpoly
import Langlands.Algebra.ReducedNormFiniteChart

/-! # A norm correction gives a maximal-Witt chart after a symmetric twist -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.CentralSimple
open Langlands.Global (FiniteCompletion)
open Langlands.Global.AdelicFunctoriality Langlands.LocalClassField
open scoped TensorProduct FiniteExtension

universe u v

section Matrix

variable {F : Type u} {L : Type v} [Field F] [Field L] [Algebra F L] {n : ℕ}
  (c : AlgebraInvolution F L)

local notation "M" => Matrix (Fin n) (Fin n) L
local notation "θ" => matrixTranspose c n

private theorem exists_scalar_of_same_adjoint (hn : 0 < n) (H J : Mˣ)
    (hH : θ (H : M) = H) (hJ : θ (J : M) = J)
    (h : ∀ X : M, (θ).adjoint H hH X = (θ).adjoint J hJ X) :
    ∃ a : Lˣ, c (a : L) = a ∧ (J : M) = (a : L) • (H : M) := by
  let : Nonempty (Fin n) := ⟨⟨0, hn⟩⟩
  let Δ := J * H⁻¹
  have hcen : Δ ∈ Subgroup.center Mˣ := by
    apply Subgroup.mem_center_iff.mpr
    intro X
    have hX : H⁻¹ * X * H = J⁻¹ * X * J := by
      apply Units.ext
      have h' := h (θ (X : M))
      simpa only [AlgebraInvolution.adjoint_apply, AlgebraInvolution.apply_apply, Units.val_mul] using h'
    have h' := congrArg (fun Y : Mˣ => J * Y * H⁻¹) hX
    simpa [Δ, mul_assoc] using h'.symm
  change Δ ∈ Subgroup.center (Matrix.GeneralLinearGroup (Fin n) L) at hcen
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hcen
  obtain ⟨a, ha⟩ := hcen
  have hscalar : (J : M) = (a : L) • (H : M) := by
    have h' := congrArg (fun X : Mˣ => X * H) ha
    rw [show Δ * H = J by dsimp only [Δ]; group] at h'
    have hval : algebraMap L M (a : L) * (H : M) = (J : M) := congrArg Units.val h'
    rw [Algebra.smul_def]
    exact hval.symm
  have hθ (l : L) (X : M) : θ (l • X) = c l • θ X := by
    ext i j
    change c (l * X j i) = c l * c (X j i)
    rw [AlgebraInvolution.apply_mul, mul_comm]
  have ha' := congrArg θ hscalar
  rw [hJ, hθ, hH, hscalar] at ha'
  exact ⟨a, (smul_left_injective L (Units.ne_zero H) ha').symm, hscalar⟩

private theorem fixedPow {a : L} (ha : c a = a) (m : ℕ) : c (a ^ m) = a ^ m := by
  induction m with
  | zero => simp
  | succ m hm => rw [pow_succ, AlgebraInvolution.apply_mul, hm, ha, mul_comm]

end Matrix

section CM

variable {E : Type u} {K A : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  [FiniteDimensional K A] [Algebra.IsCentral K A] [IsSimpleRing A]
  (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p) {n : ℕ}
  (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
  (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)

local notation "F" => FiniteCompletion E p
local notation "L" => FiniteCompletion K (Subtype.val (placeAbove K p))
local notation "V" => LocalAlgebra E A p
local notation "M" => Matrix (Fin n) (Fin n) L
local notation "c" => nonsplitCoefficientInvolution p hp
local notation "θ" => matrixTranspose (nonsplitCoefficientInvolution p hp) n
local notation "G" => nonsplitHermitianChart p D hn hp hz

attribute [local instance] FiniteExtension.local_finite

set_option maxRecDepth 4096 in
include hp hn hz in
private theorem det_chart_tmul (a : A) :
    ((G).equiv (1 ⊗ₜ[E] a)).det = algebraMap K L (reducedNorm K A K (1 ⊗ₜ[K] a)) := by
  let C := nonsplitCompletionCenterEquiv p hp
  have hcen (k : K) : (G).equiv (1 ⊗ₜ[E] algebraMap K A k) = algebraMap L M (algebraMap K L k) := by
    let y : LocalCenter E K p := 1 ⊗ₜ[E] k
    have hy := (G).center_eq (C y)
    change (G).equiv (localCenterMap E K A p (C.symm (C y))) = Matrix.scalar (Fin n) (C y) at hy
    rw [C.symm_apply_apply] at hy
    change _ = Matrix.scalar (Fin n) (algebraMap K L k)
    simpa only [y, localCenterMap_tmul, C, nonsplitCompletionCenterEquiv_apply,
      completedCenterMap_tmul, map_one, one_mul] using hy
  let f := matrixChartOfCenterCompatible D.dimension (G).equiv.toAlgHom (G).equiv.surjective hcen
  have h := reducedNorm_naturality K A (Algebra.ofId K L) (1 ⊗ₜ[K] a)
  rw [Algebra.TensorProduct.map_tmul, map_one, AlgHom.id_apply,
    reducedNorm_eq_chart_det_fintype K A f.val] at h
  rw [f.property a] at h
  exact h

variable (t : Aˣ) (ht : D.involution (t : A) = t)

private def twistedData : CentralSimpleUnitaryData E K A n :=
  { D with toSecondKindInvolution := D.toSecondKindInvolution.twist t ht }

local notation "D'" => twistedData D t ht
local notation "G'" => nonsplitHermitianChart p (twistedData D t ht) hn hp hz

set_option maxRecDepth 8192 in
private theorem exists_signedNorm_twistedGram (he : Even n) (d : Eˣ)
    (hd : reducedNorm K A K (1 ⊗ₜ[K] (t : A)) = algebraMap E K (d : E))
    (hN : (nonsplitSignedDeterminant p hp D hn hz).val ∈ normSubgroup F L ↔
      Units.map (algebraMap E F).toMonoidHom d ∈ normSubgroup F L) :
    ∃ b : L, c b * b = (-1) ^ (n / 2) * ((G').gram : M).det := by
  let j : A →ₐ[E] V := Algebra.TensorProduct.includeRight
  let T : Mˣ := Units.map ((G).equiv.toMonoidHom.comp j.toMonoidHom) t
  have hdetT : (T : M).det = algebraMap F L (algebraMap E F (d : E)) := by
    change ((G).equiv (1 ⊗ₜ[E] (t : A))).det = _
    rw [det_chart_tmul p hp D hn hz, hd, ← IsScalarTower.algebraMap_apply E K L,
      IsScalarTower.algebraMap_apply E F L]
  have hT : (θ).adjoint (G).gram (G).hermitian (T : M) = T := by
    change (θ).adjoint (G).gram (G).hermitian ((G).equiv (1 ⊗ₜ[E] (t : A))) = _
    rw [← (G).adjoint_eq, localInvolution_tmul, ht]
    rfl
  let H := (G).gram * T
  have hH : θ (H : M) = H := AlgebraInvolution.adjoint_gram_mul θ (G).gram T (G).hermitian hT
  have hchange (x : V) : (G).equiv (localInvolution (D').toSecondKindInvolution p x) =
      (θ).adjoint H hH ((G).equiv x) := by
    rw [← AlgebraInvolution.adjoint_adjoint_apply θ (G).gram T (G).hermitian hT hH]
    change (G).equiv ((D.involution.adjoint t ht).baseChange F x) = _
    rw [AlgebraInvolution.baseChange_adjoint_apply D.involution t ht F x, map_mul, map_mul]
    change (G).equiv (j (↑t⁻¹ : A)) * (G).equiv (localInvolution D.toSecondKindInvolution p x) *
      (G).equiv (j (t : A)) = _
    rw [(G).adjoint_eq]
    rfl
  have hequiv : (G').equiv = (G).equiv := rfl
  have hsame (X : M) : (θ).adjoint H hH X = (θ).adjoint (G').gram (G').hermitian X := by
    obtain ⟨x, rfl⟩ := (G).equiv.surjective X
    have hx := (G').adjoint_eq x
    rw [hequiv] at hx
    exact (hchange x).symm.trans hx
  obtain ⟨a, ha, hJ⟩ := exists_scalar_of_same_adjoint c hn H (G').gram hH (G').hermitian hsame
  let δ := nonsplitSignedDeterminant p hp D hn hz
  let dₚ := Units.map (algebraMap E F).toMonoidHom d
  have hprod := nonsplitCompletion_mul_mem_normSubgroup p hp δ.val dₚ hN
  obtain ⟨b, hb⟩ := hprod
  have hb' : c (b : L) * (b : L) = (-1) ^ (n / 2) * ((G).gram : M).det * (T : M).det := by
    have hh := congrArg (fun z : Fˣ => algebraMap F L (z : F)) hb
    change algebraMap F L (Algebra.norm F (b : L)) =
      algebraMap F L ((δ.val : F) * algebraMap E F (d : E)) at hh
    rw [nonsplitCompletion_norm_apply p hp, map_mul, δ.property, ← hdetT] at hh
    exact hh
  have he' : n / 2 + n / 2 = n := by obtain ⟨i, hi⟩ := he; omega
  have hapow : (a : L) ^ n = (a : L) ^ (n / 2) * (a : L) ^ (n / 2) := by
    rw [← pow_add, he']
  refine ⟨(a : L) ^ (n / 2) * (b : L), ?_⟩
  rw [AlgebraInvolution.apply_mul, fixedPow c ha, hJ, Matrix.det_smul, Fintype.card_fin]
  change c (b : L) * (a : L) ^ (n / 2) * ((a : L) ^ (n / 2) * (b : L)) =
    (-1) ^ (n / 2) * ((a : L) ^ n * (((G).gram : M) * (T : M)).det)
  rw [Matrix.det_mul, hapow]
  calc
    _ = (a : L) ^ (n / 2) * (a : L) ^ (n / 2) * (c (b : L) * (b : L)) := by ring
    _ = _ := by rw [hb']; ring

set_option maxRecDepth 8192 in
/-- An even-degree nonsplit chart becomes maximal Witt if the reduced-norm
factor of a symmetric twist has the same norm class as the signed determinant. -/
def maximalWittChartOfNormTwist (he : Even n) (d : Eˣ)
    (hd : reducedNorm K A K (1 ⊗ₜ[K] (t : A)) = algebraMap E K (d : E))
    (hN : (nonsplitSignedDeterminant p hp D hn hz).val ∈ normSubgroup F L ↔
      Units.map (algebraMap E F).toMonoidHom d ∈ normSubgroup F L) :
    {e : V ≃ₐ[F] Matrix (Fin n) (Fin n) (LocalCenter E K p) //
      (∀ z, e (localCenterMap E K A p z) = Matrix.scalar (Fin n) z) ∧
      (∀ x, e (localInvolution (D').toSecondKindInvolution p x) =
        maxWittAdjoint (localConjugation E K p) n (e x))} :=
  evenNonsplitMaxWittChart p hp (D') hn he hz
    (exists_signedNorm_twistedGram p hp D hn hz t ht he d hd hN)

end CM

end Langlands.Shimura.FiniteUnitary

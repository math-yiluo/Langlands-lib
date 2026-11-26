import Langlands.Shimura.Unitary.HermitianCoordinates
import Langlands.GroupScheme.Examples.SU3RootParametersQuadratic
import Langlands.ClassFieldTheory.Local.Artin.FiniteArtin

/-! # Signed Gram determinants and norms at nonsplit finite places -/

noncomputable section

namespace Langlands.Shimura.FiniteUnitary

open NumberField _root_.Algebra Langlands.Global.AdelicFunctoriality
open Langlands.Global (FiniteCompletion)
open Langlands.GroupScheme.SU3Root Langlands.LocalClassField
open Langlands.ClassFieldTheory.Local.Artin
open scoped FiniteExtension

universe u v w

variable {E : Type u} {K : Type v}
  [Field E] [NumberField E] [IsTotallyReal E]
  [Field K] [NumberField K] [IsTotallyComplex K] [Algebra E K] [IsQuadraticExtension E K]
  (p : Langlands.Global.FinitePlace E) (hp : ¬ IsSplitPlace E K p)

local notation "F" => FiniteCompletion E p
local notation "L" => FiniteCompletion K (Subtype.val (placeAbove K p))
local notation "c" => nonsplitCoefficientInvolution p hp

attribute [local instance] FiniteExtension.local_finite

private def coefficientAut : L ≃ₐ[F] L where
  toFun := c
  invFun := c
  left_inv := (c).apply_apply
  right_inv := (c).apply_apply
  map_add' := (c).apply_add
  map_mul' x y := ((c).apply_mul x y).trans (mul_comm _ _)
  commutes' := (c).apply_algebraMap

include hp in
private theorem coefficientAut_ne_one : coefficientAut p hp ≠ 1 := by
  let C := nonsplitCompletionCenterEquiv p hp
  obtain ⟨z, hz⟩ := exists_localConjugation_ne (K := K) p
  intro h
  have h' : (localConjugation E K p).transport C (C z) = C z :=
    congrArg (fun g : L ≃ₐ[F] L => g (C z)) h
  exact hz (C.injective ((AlgebraInvolution.transport_equiv _ C z).symm.trans h'))

include hp in
private theorem coefficientAut_eq_conjugation :
    letI : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
    letI : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
    coefficientAut p hp = conjugation F L := by
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  exact conjugation_unique F L _ (coefficientAut_ne_one p hp)

include hp in
/-- The norm at a nonsplit completion is the product with the actual CM conjugate. -/
theorem nonsplitCompletion_norm_apply (z : L) :
    algebraMap F L (Algebra.norm F z) = c z * z := by
  classical
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  have hu : (Finset.univ : Finset (L ≃ₐ[F] L)) = {1, coefficientAut p hp} := by
    ext g
    have hg : g = 1 ∨ g = coefficientAut p hp := by
      by_cases h : g = 1
      · exact Or.inl h
      · exact Or.inr ((conjugation_unique F L g h).trans (coefficientAut_eq_conjugation p hp).symm)
    exact ⟨fun _ => Finset.mem_insert.mpr (hg.imp_right Finset.mem_singleton.mpr),
      fun _ => Finset.mem_univ _⟩
  rw [Algebra.norm_eq_prod_automorphisms, hu,
    Finset.prod_pair (Ne.symm (coefficientAut_ne_one p hp))]
  exact mul_comm _ _

include hp in
private theorem exists_scalar_of_fixed {z : L} (hz : c z = z) :
    ∃ a : F, algebraMap F L a = z := by
  classical
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  apply (IsGalois.mem_range_algebraMap_iff_fixed z).mpr
  intro g
  by_cases h : g = 1
  · rw [h]
    rfl
  · rw [conjugation_unique F L g h, ← coefficientAut_eq_conjugation p hp]
    exact hz

include hp in
/-- Two units with equal membership status in the quadratic norm subgroup have
product in that subgroup. -/
theorem nonsplitCompletion_mul_mem_normSubgroup (a b : Fˣ)
    (h : a ∈ normSubgroup F L ↔ b ∈ normSubgroup F L) : a * b ∈ normSubgroup F L := by
  classical
  let : ValuativeRel F := FiniteCompletion.valuativeRel p
  let : IsNonarchimedeanLocalField F := FiniteCompletion.isNonarchimedeanLocalField p
  let : IsQuadraticExtension F L := ⟨nonsplitCompletion_finrank p hp⟩
  let : CharZero F := charZero_of_injective_algebraMap (algebraMap E F).injective
  have hcard : Nat.card (L ≃ₐ[F] L) = 2 := by
    rw [IsGalois.card_aut_eq_finrank, nonsplitCompletion_finrank p hp]
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : IsCyclic (L ≃ₐ[F] L) := isCyclic_of_prime_card hcard
  let : IsAbelianGalois F L := ⟨⟩
  let φ := arithmeticFiniteArtin F L
  have hφ (a : Fˣ) : φ a = 1 ↔ a ∈ normSubgroup F L := arithmeticFiniteArtin_eq_one_iff F L a
  by_cases ha : φ a = 1
  · exact (normSubgroup F L).mul_mem ((hφ a).mp ha) (h.mp ((hφ a).mp ha))
  have hb : φ b ≠ 1 := fun hb => ha ((hφ a).mpr (h.mpr ((hφ b).mp hb)))
  obtain ⟨g, -, hg⟩ := (Nat.card_eq_two_iff' (1 : L ≃ₐ[F] L)).mp hcard
  apply (hφ (a * b)).mp
  rw [map_mul, hg _ ha, hg _ hb, ← pow_two, ← hcard]
  exact pow_card_eq_one'

section Gram

variable {A : Type w} [Ring A] [Algebra E A] [Algebra K A] [IsScalarTower E K A]
  {n : ℕ} (D : CentralSimpleUnitaryData E K A n) (hn : 0 < n)
  (hz : ∀ q : FinitePlacesAbove K p, HasCompletedBrauerInvariant K A q.val 0)

local notation "H" => HermitianMatrixChart.gram (nonsplitHermitianChart p D hn hp hz)
local notation "M" => Matrix (Fin n) (Fin n) L

include hp in
private theorem exists_nonsplitSignedDeterminant :
    ∃ d : Fˣ, algebraMap F L (d : F) = (-1) ^ (n / 2) * (H : M).det := by
  let G := nonsplitHermitianChart p D hn hp hz
  let g := coefficientAut p hp
  have hdet : c (G.gram : M).det = (G.gram : M).det := by
    change g.toRingHom (G.gram : M).det = _
    rw [g.toRingHom.map_det, ← Matrix.det_transpose]
    change (matrixTranspose c n (G.gram : M)).det = _
    rw [G.hermitian]
  have hsign : c ((-1 : L) ^ (n / 2) * (G.gram : M).det) =
      (-1 : L) ^ (n / 2) * (G.gram : M).det := by
    change g ((-1 : L) ^ (n / 2) * (G.gram : M).det) = _
    rw [map_mul, map_pow, map_neg, map_one]
    exact congrArg (fun x => (-1 : L) ^ (n / 2) * x) hdet
  obtain ⟨d, hd⟩ := exists_scalar_of_fixed p hp hsign
  have hd₀ : d ≠ 0 := by
    intro he
    rw [he, map_zero, eq_comm, mul_eq_zero] at hd
    exact hd.elim (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
      (Matrix.GeneralLinearGroup.det_ne_zero G.gram)
  exact ⟨Units.mk0 d hd₀, hd⟩

/-- The signed determinant of the nonsplit Hermitian chart, as a unit of the
actual base completion with its scalar-extension equation. -/
def nonsplitSignedDeterminant :
    {d : Fˣ // algebraMap F L (d : F) = (-1) ^ (n / 2) * (H : M).det} :=
  ⟨(exists_nonsplitSignedDeterminant p hp D hn hz).choose,
    (exists_nonsplitSignedDeterminant p hp D hn hz).choose_spec⟩

end Gram

end Langlands.Shimura.FiniteUnitary

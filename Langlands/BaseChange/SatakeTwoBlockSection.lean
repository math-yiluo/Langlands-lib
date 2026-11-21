import Langlands.BaseChange.SatakePrincipalSeriesSection
import Langlands.Representation.Classification.NestedInductionProof
import Langlands.Representation.Parabolic.FlattenedRefinementModulusCalculation
import Langlands.Representation.Parabolic.RefinedInductionTensorNormalization
import Langlands.Representation.Unramified.TwoBlockSphericalIntegration

/-! The normalized spherical section in two-block parabolic coordinates. -/

noncomputable section

namespace Langlands.BaseChange

open Langlands.Correspondence Langlands.GeneralLinear Langlands.Geometric
open Langlands.GodementJacquet.TwoBlock Langlands.NestedInductionProof
open Langlands.RankinSelberg Langlands.RankinSelberg.TwoBlockJacquet Langlands.Unramified
open scoped NNReal

universe u

private theorem flatten_singletons {n : ℕ} (B : BlockShape n) :
    B.flatten (fun i => BlockShape.singletons (B.size i)) = BlockShape.singletons n := by
  let S : BlockRefinement B := fun i => BlockShape.singletons (B.size i)
  have hlength : (B.flatten S).length = n := B.sum_eq
  have hsize (i : Fin (B.flatten S).length) : (B.flatten S).size i = 1 := rfl
  generalize hB : B.flatten S = C at hlength hsize ⊢
  rcases C with ⟨d, sizes, hp, hs⟩
  dsimp only at hlength hsize
  subst d
  have he : sizes = fun _ => 1 := funext hsize
  subst sizes
  rfl

private theorem parabolicHalfModulus_congr {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
    {n : ℕ} {B C : BlockShape n} (hBC : B = C) {g : GeneralLinear n F.Carrier}
    (hgB : g ∈ B.parabolic F.Carrier) (hgC : g ∈ C.parabolic F.Carrier) :
    F.canonicalTopologicalData.parabolicHalfModulus B ⟨g, hgB⟩ =
      F.canonicalTopologicalData.parabolicHalfModulus C ⟨g, hgC⟩ := by
  subst C
  rfl

private theorem determinant_singleton_projection_val {R : Type u} [CommRing R]
    {n : ℕ} (b : (BlockShape.singletons n).parabolic R) (j : Fin n) :
    (GeneralLinear.determinant ((BlockShape.singletons n).leviProjection R b j) : R) =
      b.val j j := by
  change ((BlockShape.singletons n).leviProjection R b j).val.det = _
  rw [Matrix.det_fin_one, BlockShape.leviProjection_apply, BlockShape.singletons_index]

section Padic

variable {p : ℕ} [Fact p.Prime] (F : PadicField.{u} p)
variable {t : ℕ} {m : Fin 2 → ℕ} (h : ∑ i, (m i + 1) = t + 1)

local notation "B" => succBlockShape m h
local notation "T" => PadicField.canonicalTopologicalData F

variable (z : Fin (t + 1) → ℂˣ)

private theorem parabolicPoint_diagonal
    (L : (B).Levi F.Carrier) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (i : Fin 2) (a : Fin (m i + 1)) :
    (parabolicPoint h (L, x)).val ((B).index i a) ((B).index i a) = (L i).val a a := by
  fin_cases i
  · change (parabolicPoint h (L, x)).val ((B).index 0 a) ((B).index 0 a) = (L 0).val a a
    simp only [← blockEquiv_inl h, parabolicPoint_val, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₁₁]
  · change (parabolicPoint h (L, x)).val ((B).index 1 a) ((B).index 1 a) = (L 1).val a a
    simp only [← blockEquiv_inr h, parabolicPoint_val, Matrix.reindex_apply, Matrix.submatrix_apply,
      Equiv.symm_apply_apply, Matrix.fromBlocks_apply₂₂]

set_option maxHeartbeats 800000 in
private theorem sphericalPrincipalSeriesSection_of_upperBlocks
    (L : (B).Levi F.Carrier) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier)
    (hL : ∀ i : Fin 2, (L i).val.IsUpperTriangular) :
    sphericalPrincipalSeriesSection F z (parabolicPoint h (L, x)) =
      ((T).leviHalfModulus B L : ℂ) *
        ∏ i : Fin 2, sphericalPrincipalSeriesSection F (fun a => z ((B).index i a)) (L i) := by
  let S : BlockRefinement B := fun i => BlockShape.singletons ((B).size i)
  have he : (B).flatten S = borelShape t := flatten_singletons B
  let b : (B).parabolic F.Carrier := ⟨parabolicPoint h (L, x), parabolicPoint_mem h _⟩
  have hPr : (B).leviProjection F.Carrier b = L :=
    congrArg Prod.fst (parabolicCoord_parabolicPoint h (L, x))
  have hRef : L ∈ refinedParabolic F.Carrier B S :=
    (mem_refinedParabolic F.Carrier B S L).mpr fun i =>
      (BlockShape.singletons ((B).size i)).mem_parabolic_of_isUpperTriangular (L i) (hL i)
  let bR : refinedParabolic F.Carrier B S := ⟨L, hRef⟩
  have hPrMem : (B).leviProjection F.Carrier b ∈ refinedParabolic F.Carrier B S :=
    hPr.symm ▸ hRef
  have hFlat : b.val ∈ ((B).flatten S).parabolic F.Carrier := by
    rw [← composedParabolic_flatten F.Carrier B S]
    change b.val ∈ Parabolic.leviPreimage F.Carrier B (refinedParabolic F.Carrier B S)
    exact (Parabolic.mem_leviPreimage_iff _ _ _ _).mpr ⟨b.property, hPrMem⟩
  have hBor : b.val ∈ (borelShape t).parabolic F.Carrier := he ▸ hFlat
  let bBor : (borelShape t).parabolic F.Carrier := ⟨b.val, hBor⟩
  let bBlock (i : Fin 2) : (borelShape (m i)).parabolic F.Carrier :=
    refinedParabolicEval F.Carrier B S i bR
  let bFlat : ((B).flatten S).parabolic F.Carrier := ⟨b.val, hFlat⟩
  let d := ((B).flatten S).leviProjection F.Carrier bFlat
  have hProj : flattenedLeviEquiv F.Carrier B S d =
      refinedLeviProjection F.Carrier B S bR := by
    have hp := flattenedLeviEquiv_leviProjection F.Carrier B S b.val hFlat b.property hPrMem
    have hr : (⟨(B).leviProjection F.Carrier b, hPrMem⟩ : refinedParabolic F.Carrier B S) = bR :=
      Subtype.ext hPr
    rw [hr] at hp
    exact hp
  have hMod := DFunLike.congr_fun ((T).composedLeviModulus_flattened B S) d
  change (T).composedLeviModulus B S (flattenedLeviEquiv F.Carrier B S d) =
    (T).leviModulus ((B).flatten S) d at hMod
  have hHalf := congrArg
    (Jacquet.complexCharacter (Jacquet.positiveHalfCharacter (MonoidHom.id (ℝ≥0ˣ)))) hMod
  change (T).composedLeviHalfModulus B S (flattenedLeviEquiv F.Carrier B S d) =
    (T).parabolicHalfModulus ((B).flatten S) bFlat at hHalf
  have hFactor : (T).parabolicHalfModulus (borelShape t) bBor =
      (T).leviHalfModulus B L * ∏ i : Fin 2, (T).parabolicHalfModulus (borelShape (m i)) (bBlock i) := by
    rw [← parabolicHalfModulus_congr F he hFlat hBor, ← hHalf, hProj,
      (T).composedLeviHalfModulus_eq, MonoidHom.mul_apply, (T).refinedOuterHalfModulus_projection]
    exact congrArg ((T).leviHalfModulus B L * ·) ((T).refinedParabolicHalfModulus_eq_prod B S bR)
  let χ (j : Fin (t + 1)) : ℂ := character F (z j)
    (GeneralLinear.determinant ((borelShape t).leviProjection F.Carrier bBor j))
  let χBlock (i : Fin 2) (a : Fin (m i + 1)) : ℂ := character F (z ((B).index i a))
    (GeneralLinear.determinant ((borelShape (m i)).leviProjection F.Carrier (bBlock i) a))
  have hχ (i : Fin 2) (a : Fin (m i + 1)) : χ ((B).index i a) = χBlock i a := by
    have ha : GeneralLinear.determinant
        ((borelShape t).leviProjection F.Carrier bBor ((B).index i a)) =
        GeneralLinear.determinant ((borelShape (m i)).leviProjection F.Carrier (bBlock i) a) := by
      apply Units.ext
      exact (determinant_singleton_projection_val bBor ((B).index i a)).trans
        ((parabolicPoint_diagonal F h L x i a).trans
          (determinant_singleton_projection_val (bBlock i) a).symm)
    exact congrArg (fun d : F.Carrierˣ => (character F (z ((B).index i a)) d : ℂ)) ha
  have hprod : ∏ j, χ j = ∏ i, ∏ a, χBlock i a := by
    rw [← Fintype.prod_sigma']
    exact (Fintype.prod_equiv (B).indexEquiv _ _ (fun q => (hχ q.1 q.2).symm)).symm
  change sphericalPrincipalSeriesSection F z bBor.val = _
  rw [sphericalPrincipalSeriesSection_borel F z bBor, hFactor, Units.val_mul, Units.coe_prod]
  change (((T).leviHalfModulus B L : ℂ) * ∏ i : Fin 2,
      ((T).parabolicHalfModulus (borelShape (m i)) (bBlock i) : ℂ)) * (∏ j, χ j) = _
  rw [hprod, mul_assoc, ← Finset.prod_mul_distrib]
  congr 1
  apply Finset.prod_congr rfl
  intro i _
  exact (sphericalPrincipalSeriesSection_borel F (fun a => z ((B).index i a)) (bBlock i)).symm

attribute [local instance] heckeFieldTopology heckeFieldValuativeRel heckeFieldLocalField
  heckeGeneralLinearTopology heckeGeneralLinearTopologicalGroup heckeGeneralLinearT2
  heckeGeneralLinearMeasurable heckeGeneralLinearBorel

set_option maxHeartbeats 800000 in
/-- In two-block parabolic coordinates the normalized section is the product of the
normalized block sections times the outer parabolic half modulus. -/
theorem sphericalPrincipalSeriesSection_parabolicPoint
    (L : (B).Levi F.Carrier) (x : Matrix (Fin (m 0 + 1)) (Fin (m 1 + 1)) F.Carrier) :
    sphericalPrincipalSeriesSection F z (parabolicPoint h (L, x)) =
      ((T).leviHalfModulus B L : ℂ) *
        ∏ i : Fin 2, sphericalPrincipalSeriesSection F (fun a => z ((B).index i a)) (L i) := by
  have hdec (i : Fin 2) : ∃ (b : GeneralLinear (m i + 1) F.Carrier),
      b.val.IsUpperTriangular ∧ ∃ k ∈ sphericalOpenSubgroup F (m i), L i = b * k :=
    GeneralLinear.Iwasawa.exists_upperTriangular_mul (ValuativeRel.valuation F.Carrier) (L i)
  choose b hb k hk hL using hdec
  have hL' : L = b * k := funext hL
  let y := (k 0).val * x * ((k 1)⁻¹ : GeneralLinear (m 1 + 1) F.Carrier).val
  have hp : parabolicPoint h (L, x) = parabolicPoint h (b, y) * (B).leviEmbedding F.Carrier k := by
    rw [hL']
    exact parabolicPoint_mul_levi_right h b k x
  have hK := leviEmbedding_mem_spherical_of_forall F h k hk
  have hHalf := leviHalfModulus_eq_one_of_forall_spherical F h k hk
  rw [hp, sphericalPrincipalSeriesSection_rightInvariant F z _
      ⟨(B).leviEmbedding F.Carrier k, hK⟩, sphericalPrincipalSeriesSection_of_upperBlocks F h z b y hb]
  congr 1
  · rw [hL', map_mul, hHalf, mul_one]
  · apply Finset.prod_congr rfl
    intro i _
    rw [hL i]
    exact (sphericalPrincipalSeriesSection_rightInvariant F (fun a => z ((B).index i a))
      (b i) ⟨k i, hk i⟩).symm

end Padic

end Langlands.BaseChange

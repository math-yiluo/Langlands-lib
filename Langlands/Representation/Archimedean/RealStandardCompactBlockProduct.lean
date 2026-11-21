import Langlands.Representation.Archimedean.RealStandardCompactProjectionOnSubgroup
import Langlands.Representation.Archimedean.RealLeviProducts
import Langlands.Representation.Archimedean.RealLeviParabolicIntegration
import Langlands.Representation.Archimedean.RealInductionStagesSlice

/-! # Lifting a pure compact block product to a real standard vector -/

noncomputable section

open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Archimedean

open Langlands.LocalFactor.Archimedean
open RealLeviChart RealLeviSlices GramFormula
open OrthogonalFinitePolynomial PrincipalSeriesExtension RealStandardCompactAverage
open RealLeviProducts RealInducedBlockBound RealInducedStandardBound

private abbrev G (n : ℕ) := Langlands.GeneralLinear n ℝ
private abbrev O (n : ℕ) := Matrix.unitaryGroup (Fin n) ℝ

section Geometry

variable {c : ℕ} (s : Fin c → ℕ)

private theorem embedded_mem_blockOrth (i : Fin c) {g : G (s i)}
    (hg : g ∈ unitaryCompact ℝ (s i)) : emb s i g ∈ blockOrth s := by
  let gK : unitaryCompact ℝ (s i) := ⟨g, hg⟩
  let ks : ∀ j, unitaryCompact ℝ (s j) := Pi.mulSingle i gK
  have he : (fun j => ((ks j : unitaryCompact ℝ (s j)) : G (s j))) = Pi.mulSingle i g := by
    funext j
    by_cases hj : j = i
    · subst j
      simp [ks, gK]
    · simp [ks, Pi.mulSingle_eq_of_ne hj]
  rw [emb_eq, ← he]
  exact blockDiagGL_mem_blockOrth _

private theorem emb_signReflection (i : Fin c) (a : Fin (s i)) :
    emb s i (Unitary.toUnits (signReflection (s i) a)) =
      Unitary.toUnits (signReflection (∑ j, s j) (pos s i a)) := by
  apply Units.ext
  rw [emb_val, embA]
  change blockDiagHom s (Pi.mulSingle i (signReflection (s i) a).val) =
    Matrix.diagonal (fun j => if j = pos s i a then (-1 : ℝ) else 1)
  ext p q
  obtain ⟨⟨j, b⟩, rfl⟩ := finSigmaFinEquiv.surjective p
  obtain ⟨⟨k, d⟩, rfl⟩ := finSigmaFinEquiv.surjective q
  change (blockDiagHom s _) (pos s j b) (pos s k d) =
    Matrix.diagonal (fun x => if x = pos s i a then (-1 : ℝ) else 1) (pos s j b) (pos s k d)
  by_cases hjk : j = k
  · subst k
    rw [blockDiagHom_pos_pos_self]
    have hd : pos s j b = pos s j d ↔ b = d := by
      simp only [Fin.ext_iff, val_pos, Nat.add_left_cancel_iff]
    by_cases hji : j = i
    · subst j
      have ha : pos s i b = pos s i a ↔ b = a := by
        simp only [Fin.ext_iff, val_pos, Nat.add_left_cancel_iff]
      rw [Pi.mulSingle_eq_same, signReflection_val]
      simp only [Matrix.diagonal_apply, hd, ha]
    · have ha : pos s j b ≠ pos s i a := fun he => hji (by
        simpa only [cls_pos] using congrArg (cls s) he)
      rw [Pi.mulSingle_eq_of_ne hji]
      simp only [Matrix.one_apply, Matrix.diagonal_apply, hd, ha, ↓reduceIte]
  · have he : pos s j b ≠ pos s k d := fun he => hjk (by
      simpa only [cls_pos] using congrArg (cls s) he)
    rw [blockDiagHom_pos_pos_of_ne s _ hjk, Matrix.diagonal_apply_ne _ he]

end Geometry

section Product

variable {c : ℕ} (dss : Fin c → List RealBlock)

local notation "s" => sz dss
local notation "N" => ∑ i, sz dss i

private theorem exists_local_position {p : ℕ} {d : ComplexCharacterData}
    (hd : realInducedBlockAt (flat dss) p = some d) :
    ∃ (i : Fin c) (j : ℕ), p = start s i + j ∧
      realInducedBlockAt (dss i) j = some d := by
  have hp : p < N := by
    have h := realInducedBlockAt_lt hd
    rw [realRank_flat] at h
    omega
  obtain ⟨⟨i, j⟩, he⟩ := finSigmaFinEquiv.surjective (⟨p, hp⟩ : Fin N)
  have hpos : (pos s i j).val = p := congrArg Fin.val he
  rw [val_pos] at hpos
  refine ⟨i, j.val, hpos.symm, ?_⟩
  rw [← realInducedBlockAt_flat dss i _ j.isLt, hpos]
  exact hd

private theorem exists_product_polynomial (f : ∀ i, InductionStages.KFin (s i) (dss i)) :
    ∃ φ : polynomialFunctions N, ∀ (κ : ∀ i, G (s i)),
      (∀ i, κ i ∈ unitaryCompact ℝ (s i)) →
      extension 0 φ (blockDiagGL s κ) = ∏ i, (f i).val (κ i) := by
  have hP (i : Fin c) := exists_mvPolynomial_of_mem_kFiniteVectors
    (RealPrincipalSeriesDuality.continuous_of_mem_kFiniteFunctions (f i).2) (f i).2.2 1
  choose P hEval using hP
  let Q := ∏ i : Fin c, MvPolynomial.rename (fun ij : Fin (s i) × Fin (s i) =>
    (pos s i ij.1, pos s i ij.2)) (P i)
  let Φ := MvPolynomial.aeval (fun ij => (entry N ij : O N → ℂ)) Q
  have hΦ : Φ ∈ polynomialFunctions N := by
    change Φ ∈ Algebra.adjoin ℂ (Set.range fun ij => (entry N ij : O N → ℂ))
    rw [Algebra.adjoin_range_eq_range_aeval]
    exact ⟨Q, rfl⟩
  have hΦEval (k : O N) :
      Φ k = MvPolynomial.eval (fun ij : Fin N × Fin N => (k.val ij.1 ij.2 : ℂ)) Q := by
    have he := congrArg (fun A => A Q) (MvPolynomial.comp_aeval (R := ℂ)
      (fun ij => (entry N ij : O N → ℂ)) (Pi.evalAlgHom ℂ (fun _ : O N => ℂ) k))
    exact he
  refine ⟨⟨Φ, hΦ⟩, fun κ hκ => ?_⟩
  have hK := blockDiagGL_mem_unitaryCompact (fun i => (⟨κ i, hκ i⟩ : unitaryCompact ℝ (s i)))
  let k : O N := ⟨(blockDiagGL s κ : Matrix (Fin N) (Fin N) ℝ), hK⟩
  have hk : Unitary.toUnits k = blockDiagGL s κ := Units.ext rfl
  rw [← hk, extension_unitary]
  change Φ k = _
  rw [hΦEval, show Q = _ from rfl, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  have hi := hEval i (⟨(κ i : Matrix (Fin (s i)) (Fin (s i)) ℝ), hκ i⟩ : O (s i))
  rw [one_mul, RealReverseTransfer.toUnits_mk (hκ i)] at hi
  rw [MvPolynomial.eval_rename, hi]
  apply congrArg (fun v : Fin (s i) × Fin (s i) → ℂ => MvPolynomial.eval v (P i))
  funext ij
  change ((blockDiagGL s κ : Matrix (Fin N) (Fin N) ℝ) (pos s i ij.1) (pos s i ij.2) : ℂ) = _
  rw [blockDiagGL_val, blockDiagHom_pos_pos_self]

private theorem product_split (f : ∀ i, InductionStages.KFin (s i) (dss i))
    (κ : ∀ i, G (s i)) (i : Fin c) :
    (∏ j, (f j).val (κ j)) =
      (f i).val (κ i) * ∏ j ∈ Finset.univ \ {i}, (f j).val (κ j) := by
  simpa only [Function.update_eq_self] using prod_apply_update (fun j => (f j).val) κ i (κ i)

/-- Every pure product of block standard vectors on the compact Levi group
is the compact restriction of an actual ambient standard vector. -/
def RealStandardCompactBlockProductStatement : Prop :=
  ∀ {c : ℕ} (dss : Fin c → List RealBlock)
    (f : ∀ i, InductionStages.KFin (sz dss i) (dss i)),
    ∃ F : InductionStages.KFin (∑ j, sz dss j) (flat dss),
      ∀ κ : ∀ i, unitaryCompact ℝ (sz dss i),
        F.val (blockDiagGL (sz dss) (fun i => (κ i).val)) = ∏ i, (f i).val (κ i).val

theorem realStandardCompactBlockProduct : RealStandardCompactBlockProductStatement := by
  intro c dss f
  obtain ⟨φ, hφ⟩ := exists_product_polynomial dss f
  refine ⟨compactProjection (realRank_flat dss) φ, ?_⟩
  have hfix := realStandardCompactProjectionOnSubgroup (realRank_flat dss) (blockOrth (sz dss))
    (fun _ hg => mem_unitaryCompact_of_mem_blockOrth hg) ?_ ?_ φ ?_ ?_
  · intro κ
    exact (hfix (blockDiagGL_mem_blockOrth κ)).trans (hφ _ fun i => (κ i).2)
  · intro p
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    change Unitary.toUnits (signReflection (∑ a, sz dss a) (pos (sz dss) i j)) ∈
      blockOrth (sz dss)
    rw [← emb_signReflection (sz dss) i j]
    exact embedded_mem_blockOrth _ i (signReflection _ j).2
  · intro t ht θ
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots ht
    obtain ⟨i, j, he, hj⟩ := exists_local_position dss hd
    change blockRotation (∑ a, sz dss a) p θ ∈ blockOrth (sz dss)
    rw [he, RealLeviProducts.blockRotation_start_add _ i (realInducedBlockAt_lt hj)]
    exact embedded_mem_blockOrth _ i (blockRotation_mem_unitaryCompact _ _ _)
  · intro p x hx
    obtain ⟨⟨i, j⟩, rfl⟩ := finSigmaFinEquiv.surjective p
    obtain ⟨κ, rfl⟩ := RealLeviParabolicIntegration.exists_blockDiagGL_eq hx
    let k : ∀ i, G (sz dss i) := fun i => (κ i).val
    have hK (i : Fin c) : k i ∈ unitaryCompact ℝ (sz dss i) := (κ i).2
    let z := Unitary.toUnits (signReflection (sz dss i) j)
    have hz : z * k i ∈ unitaryCompact ℝ (sz dss i) :=
      mul_mem (signReflection _ j).2 (hK i)
    change extension 0 φ
      (Unitary.toUnits (signReflection _ (pos (sz dss) i j)) * blockDiagGL (sz dss) k) =
      realPositionCharacter (flat dss) (pos (sz dss) i j).val (-1) *
        extension 0 φ (blockDiagGL (sz dss) k)
    rw [← emb_signReflection, emb_mul_blockDiagGL,
      hφ _ (fun a => update_mem_unitaryCompact hK hz a), hφ _ hK,
      prod_apply_update, product_split dss f k i, val_pos,
      realPositionCharacter_flat _ i _ j.isLt]
    rw [RealBlockFourierFinite.apply_signReflection_mul
      (RealStrictCharacterLanglandsQuotient.realPositionCharacter_one (dss i)) (f i).2.1.1]
    ring
  · intro t ht m hm x hx
    obtain ⟨p, hp, d, hd, rfl⟩ := mem_slots ht
    obtain ⟨i, j, he, hj⟩ := exists_local_position dss hd
    obtain ⟨κ, rfl⟩ := RealLeviParabolicIntegration.exists_blockDiagGL_eq hx
    let k : ∀ i, G (sz dss i) := fun i => (κ i).val
    have hK (i : Fin c) : k i ∈ unitaryCompact ℝ (sz dss i) := (κ i).2
    have hmode : |m| < |d.weight| := by
      simpa only [mem_lowModes, mkSlot, Int.abs_eq_natAbs d.weight] using hm
    change blockFourierCoefficient _ p m (extension 0 φ) (blockDiagGL _ k) = 0
    calc
      _ = blockFourierCoefficient (sz dss i) j m (f i).val (k i) *
          ∏ a ∈ Finset.univ \ {i}, (f a).val (k a) := by
        unfold blockFourierCoefficient
        rw [← intervalIntegral.integral_mul_const]
        refine intervalIntegral.integral_congr fun θ _ => ?_
        have hθ : blockRotation (sz dss i) j θ * k i ∈ unitaryCompact ℝ (sz dss i) :=
          mul_mem (blockRotation_mem_unitaryCompact _ _ _) (hK i)
        rw [he, RealLeviProducts.blockRotation_start_add _ i (realInducedBlockAt_lt hj),
          emb_mul_blockDiagGL, hφ _ (fun a => update_mem_unitaryCompact hK hθ a),
          prod_apply_update]
        ring
      _ = 0 := by rw [(f i).2.1.2 j d hj m hmode, zero_mul]

end Product

end Langlands.Archimedean

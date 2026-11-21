import Langlands.GroupScheme.Rational.NumberFieldRankThreeSkewComponent
import Langlands.GroupScheme.Rational.NumberFieldRankThreeHermitianNormValue
import Langlands.GroupScheme.Quaternionic.QuaternionicComplementBasis
import Langlands.GroupScheme.Quaternionic.RankThreeHermitianValue
import Langlands.GroupScheme.Quaternionic.SkewHermitianTensorBasis

/-! # The number-field isotropy principle for rank-three quaternionic skew forms -/

noncomputable section

universe u

open NumberField Matrix
open scoped TensorProduct

namespace Langlands.GroupScheme.KneserThree.QuatData

open QuadField Quaternionic Langlands.SymmetricBilinear

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 2300000

variable {F D : Type u} [Field F] [DivisionRing D] [Algebra F D]
  (Q : QuatData F D) (τ : FirstKindInvolution F D) (hbar : ∀ z, τ z = Q.bar z)
  {H : Matrix (Fin 3) (Fin 3) D} (hH : τ.IsAntihermitian H)

local notation "E" => field Q.c
local notation "V" => Fin 3 → D
local notation "κ" => SU3Root.conjugation F E
local notation "r" => (root : E)
local notation "B" => AntihermitianForm.ofMatrix hH

private instance componentModule : Module (field Q.c) (Fin 3 → D) := Module.compHom _ Q.ι.toRingHom

private theorem root_ne_zero : r ≠ 0 := by
  intro hr
  have hx := Q.basis.ne_zero 1
  rw [show Q.basis 1 = Q.x from congrFun Q.basis_eq 1, ← Q.ι_root, hr, map_zero] at hx
  exact hx rfl

private theorem rootSquare_ne_zero : Q.c ≠ 0 := by
  intro h
  have hx : r * r = 0 := QuadField.root_mul_self.trans
    ((congrArg (algebraMap F E) h).trans (map_zero _))
  exact mul_ne_zero Q.root_ne_zero Q.root_ne_zero hx

private theorem generatorSquare_ne_zero : Q.δ ≠ 0 := by
  have hj := Q.basis.ne_zero 2
  rw [show Q.basis 2 = Q.j from congrFun Q.basis_eq 2] at hj
  intro h
  exact mul_ne_zero hj hj (by rw [Q.j_mul_j, h, map_zero])

private def restrictedHermitian (W : Submodule E V) : W →ₗ[E] (W →ₛₗ[(κ).toRingHom] E) :=
  (((Q.inducedHermitian B hbar).comp W.subtype).compl₂ W.subtype)

private theorem scaled_pairing_eq_hermitian (W : Submodule E V)
    (hW : ∀ x ∈ W, ∀ y ∈ W, Q.symmetricComponent B hbar x y = 0) (x y : W) :
    (-Q.c) • B (x : V) (y : V) = Q.ι (r * Q.restrictedHermitian τ hbar hH W x y) := by
  have hs : Q.snd (B (x : V) (y : V)) = 0 := (κ).injective (by
    rw [map_zero, ← Q.symmetricComponent_apply B hbar]
    exact hW x x.property y y.property)
  have hf : Q.ι (Q.fst (B (x : V) (y : V))) = B (x : V) (y : V) := by
    have h := Q.decompose (B (x : V) (y : V))
    rwa [hs, map_zero, mul_zero, add_zero] at h
  have hG : Q.restrictedHermitian τ hbar hH W x y = r * -(Q.fst (B (x : V) (y : V))) := by
    change Q.inducedHermitian B hbar x y = _
    rw [Q.inducedHermitian_apply, Q.symmetricComponent_jAction_right]
  rw [hG, ← mul_assoc, mul_neg, QuadField.root_mul_self, ← neg_mul, ← map_neg, map_mul,
    Q.ι.commutes, hf, Algebra.smul_def]

private theorem norm_of_rootCoordinates (a b : F) :
    let z := algebraMap F E a + algebraMap F E b * r
    z * κ z = algebraMap F E (a ^ 2 - Q.c * b ^ 2) := by
  dsimp only
  rw [map_add, map_mul, AlgEquiv.commutes, AlgEquiv.commutes, QuadField.conjugation_root,
    mul_neg, ← sub_eq_add_neg]
  rw [show ∀ x y : E, (x + y) * (x - y) = x ^ 2 - y ^ 2 by intro x y; ring,
    mul_pow, _root_.sq r, QuadField.root_mul_self, map_sub, map_mul, map_pow, map_pow]
  ring

private theorem exists_represented_hermitian_value (W : Submodule E V)
    (b : Module.Basis (Fin 3) E W) (a : Fin 3 → F)
    (hb : ∀ i j, i ≠ j → Q.restrictedHermitian τ hbar hH W (b i) (b j) = 0)
    (ha : ∀ i, Q.restrictedHermitian τ hbar hH W (b i) (b i) = algebraMap F E (a i))
    (z : (Fin 3 ⊕ Fin 3) → F)
    (hz : QuadraticMap.weightedSumSquares F (rankThreeNormWeights a Q.c) z = -(∏ i, a i) * Q.δ) :
    ∃ w : W, Q.restrictedHermitian τ hbar hH W w w =
      -algebraMap F E (∏ i, a i) * algebraMap F E Q.δ := by
  let G := Q.restrictedHermitian τ hbar hH W
  let x := fun i : Fin 3 => algebraMap F E (z (.inl i)) + algebraMap F E (z (.inr i)) * r
  let w := b.equivFun.symm x
  refine ⟨w, ?_⟩
  have hq : QuadraticMap.weightedSumSquares F (rankThreeNormWeights a Q.c) z =
      ∑ i, a i * (z (.inl i) ^ 2 - Q.c * z (.inr i) ^ 2) := by
    rw [QuadraticMap.weightedSumSquares_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i hi
    simp only [rankThreeNormWeights_inl, rankThreeNormWeights_inr, smul_eq_mul]
    ring
  have hcoords (i : Fin 3) : b.repr w i = x i := by
    rw [← b.equivFun_apply, show w = b.equivFun.symm x from rfl, b.equivFun.apply_symm_apply]
  have hsum (i : Fin 3) :
      ∑ j, x i * G (b i) (b j) * κ (x j) = algebraMap F E
          (a i * (z (.inl i) ^ 2 - Q.c * z (.inr i) ^ 2)) := by
    rw [Finset.sum_eq_single i]
    · rw [ha i, map_mul, ← Q.norm_of_rootCoordinates (z (.inl i)) (z (.inr i))]
      ring
    · intro j _ hij
      rw [hb i j (Ne.symm hij), mul_zero, zero_mul]
    · simp
  change G w w = _
  rw [HermitianPairing.apply_eq_sum_repr G b, show (∑ i, ∑ j, b.repr w i * G (b i) (b j) *
    κ (b.repr w j)) = ∑ i, algebraMap F E (a i * (z (.inl i) ^ 2 - Q.c * z (.inr i) ^ 2)) by
    simp only [hcoords, hsum], ← map_sum, ← hq, hz, map_mul, map_neg]

variable [NumberField F]

private theorem hasNonzeroSkewNormZero_at_real (hτ : ∀ z, τ z = Q.bar z) (hu : IsUnit H) (hl : τ.IsLocallyNonsingularIsotropic H)
    (b : Module.Basis (Fin 3) D V) (a : Fin 3 → F)
    (hdiag : ∀ i j, (-Q.c) • B (b i) (b j) = if i = j then a i • Q.x else 0)
    (v : InfinitePlace F) :
    HasNonzeroSkewNormZero (algebraMap F v.Completion ∘ a)
      (algebraMap F v.Completion Q.c) (algebraMap F v.Completion Q.δ) := by
  classical
  let R := v.Completion
  let f := algebraMap F R
  obtain ⟨x, i, hi, hx⟩ := hl (.inl v)
  obtain ⟨t, s, ht, hts⟩ := τ.tensorGram_exists_isotropic_with_partner hH R hu hi hx
  have ht0 : t ≠ 0 := by
    intro h
    rw [h, map_zero, LinearMap.zero_apply] at hts
    have hinj : Function.Injective (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D) :=
      Algebra.TensorProduct.includeRight_injective (algebraMap F R).injective
    exact one_ne_zero (hinj (hts.symm.trans (map_zero (Algebra.TensorProduct.includeRight : D →ₐ[F] R ⊗[F] D)).symm))
  let e := AntihermitianForm.tensorBasisCoordinates (F := F) b R
  let z := e t
  have hz : z ≠ 0 := fun h => ht0 (e.injective (h.trans (map_zero e).symm))
  have hpair := (B).tensor_pairing_in_basis_scaled b R (-Q.c) t t
  rw [ht, smul_zero] at hpair
  have hrow (i : Fin 3) :
      ∑ j, z i * ((1 : R) ⊗ₜ[F] ((-Q.c) • B (b i) (b j))) * τ.baseChange R (z j) =
        z i * ((f (a i)) ⊗ₜ[F] Q.x) * τ.baseChange R (z i) := by
    rw [Finset.sum_eq_single i]
    · have hs : (a i) • (1 : R) = f (a i) := by rw [Algebra.smul_def, mul_one]
      rw [hdiag, ite_eq_left rfl, ← TensorProduct.smul_tmul, hs]
    · intro j _ hij
      rw [hdiag, ite_eq_right (Ne.symm hij), TensorProduct.tmul_zero, mul_zero, zero_mul]
    · simp
  have hsum : ∑ i, z i * (f (a i) ⊗ₜ[F] Q.x) * τ.baseChange R (z i) = 0 := by
    simpa only [← hrow, z, e] using hpair.symm
  exact Q.exists_normCoordinates_of_pureDiagonal_isotropic R τ hτ (f ∘ a) z hz hsum

/-- The arithmetic value argument in the complementary-subspace case. -/
theorem exists_skewIsotropic_of_hyperbolic_component (hu : IsUnit H) (hl : τ.IsLocallyNonsingularIsotropic H)
    (hC : (threeHyperbolicPlanes E).Equivalent (Q.symmetricComponent B hbar).toQuadraticMap) :
    ∃ x : V, x ≠ 0 ∧ B x x = 0 := by
  have h2 : (2 : E) ≠ 0 := by
    simpa only [map_ofNat] using (map_ne_zero_iff _ (algebraMap F E).injective).mpr
      (two_ne_zero : (2 : F) ≠ 0)
  rcases Q.exists_skewIsotropic_or_complement B hbar h2 hC with h | ⟨W, hdim, hW, hcomp⟩
  · exact h
  let G := Q.restrictedHermitian τ hbar hH W
  have hG (x y : W) : κ (G x y) = G y x := Q.inducedHermitian_conj B hbar x y
  have hsep : ∀ x : W, (∀ y : W, G x y = 0) → x = 0 := by
    intro x hx
    apply Subtype.ext
    apply Q.inducedHermitian_separating_on_subspace B hbar
      (AntihermitianForm.ofMatrix_separatingLeft hH hu) W hW (Q.exists_add_jAction_of_isCompl W hcomp) x x.property
    intro y hy
    exact hx ⟨y, hy⟩
  let : Module F W := Module.restrictScalars F E W
  let : IsScalarTower F E W := IsScalarTower.restrictScalars F E W
  let : FiniteDimensional E W := .of_finrank_pos (by rw [hdim]; decide)
  obtain ⟨b, hb, hvals⟩ := HermitianPairing.exists_orthogonalBasis G hdim hG hsep
  choose a ha using fun i => SU3Root.exists_algebraMap_eq_of_conjugation_eq F E (hG (b i) (b i))
  have ha0 (i : Fin 3) : a i ≠ 0 := by
    intro h
    exact hvals i (by rw [← ha i, h, map_zero])
  obtain ⟨bD, hbD⟩ := Q.exists_quaternionicBasis W hcomp b
  have hdiag (i j : Fin 3) : (-Q.c) • B (bD i) (bD j) = if i = j then a i • Q.x else 0 := by
    rw [hbD i, hbD j, Q.scaled_pairing_eq_hermitian τ hbar hH W hW]
    change Q.ι (r * G (b i) (b j)) = _
    by_cases hij : i = j
    · subst j
      rw [ite_eq_left rfl, ← ha i, map_mul, Q.ι_root, Q.ι.commutes, Algebra.smul_def]
      exact (Algebra.commutes (a i) Q.x).symm
    · rw [ite_eq_right hij, hb i j hij, mul_zero, map_zero]
  obtain ⟨z, hz⟩ := numberFieldRankThreeHermitianNormValue F a Q.c Q.δ ha0
    Q.rootSquare_ne_zero Q.generatorSquare_ne_zero
    (fun v _ => Q.hasNonzeroSkewNormZero_at_real τ hH hbar hu hl bD a hdiag v)
  obtain ⟨w, hw⟩ := Q.exists_represented_hermitian_value τ hbar hH W b a hb (fun i => (ha i).symm) z hz
  have hdet : (HermitianPairing.gram G b).det = algebraMap F E (∏ i, a i) := by
    rw [HermitianPairing.det_gram_eq_prod G b hb, map_prod]
    simp only [ha]
  have hdet0 : (HermitianPairing.gram G b).det ≠ 0 := by
    rw [hdet]
    exact (map_ne_zero_iff _ (algebraMap F E).injective).mpr (Finset.prod_ne_zero_iff.mpr fun i _ => ha0 i)
  obtain ⟨u, v, hv, huv, hval⟩ := HermitianPairing.rankThreeHermitianValue F E W G b hG hsep
    (algebraMap F E Q.δ) ((map_ne_zero_iff _ (algebraMap F E).injective).mpr Q.generatorSquare_ne_zero)
    hdet0 w (by rw [hdet]; exact hw)
  refine ⟨(u : V) + Q.jAction (v : V), ?_, ?_⟩
  · intro h
    exact hv (Q.eq_zero_of_add_jAction_eq_zero W hcomp u v h).2
  · exact (Q.skew_self_add_jAction_eq_zero_iff_inducedHermitian B hbar h2 (u : V) (v : V)
      (hW u u.property u u.property) (hW v v.property v v.property) (hW u u.property v v.property)).mpr
      ⟨huv, hval⟩

end Langlands.GroupScheme.KneserThree.QuatData

namespace Langlands.GroupScheme.Quaternionic

/-- A nonsingular rank-three skew-hermitian matrix over a quaternion division
  algebra is isotropic if it is nonsingularly isotropic at every completion. -/
def NumberFieldRankThreeSkewIsotropyStatement : Prop :=
  ∀ (F D : Type u) [Field F] [NumberField F] [DivisionRing D] [Algebra F D]
    [FiniteDimensional F D] [Algebra.IsCentral F D] (σ : FirstKindInvolution F D)
    (hdim : Module.finrank F D = 4) (hsym : Module.finrank F σ.symmetricSubspace = 3),
    let τ := σ.quaternionConjugation hdim hsym
    ∀ (H : Matrix (Fin 3) (Fin 3) D) (_ : τ.IsAntihermitian H),
    IsUnit H → τ.IsLocallyNonsingularIsotropic H →
    ∃ x : Fin 3 → D, x ≠ 0 ∧ τ.sesqForm H x x = 0

theorem numberFieldRankThreeSkewIsotropy : NumberFieldRankThreeSkewIsotropyStatement.{u} := by
  intro F D _ _ _ _ _ _ σ hdim hsym τ H hH hu hl
  obtain ⟨Q, hbar, _, hC⟩ := numberFieldRankThreeSkewComponent F D σ hdim hsym H hH hu hl
  exact Q.exists_skewIsotropic_of_hyperbolic_component τ hbar hH hu hl hC

end Langlands.GroupScheme.Quaternionic

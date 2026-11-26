import Langlands.Global.AdelicPolynomialCosetRepresentatives
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.AdelicIntertwiningConvergenceReduction
import Langlands.Global.EisensteinConstantTerm.Height
import Langlands.GroupScheme.Dynamic.UnipotentUnipotenceProof

/-! # Decay of regular Iwasawa powers on an opposite adelic radical -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry Set
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.PointTopology
open scoped CategoryTheory.MonObj Matrix

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.Global.RepresentationGrowth

open Langlands.GroupScheme AdelicGroupPoints AdelicMatrixHeight

variable {F : Type u} [Field F] [NumberField F]
  {G Q H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine H.X.left]
  {q : Q ⟶ G}
  {N m : ℕ} (rho : MatrixRepresentation G (Fin N))
  (σ : MatrixRepresentation G (Fin (m + 1))) (j : Fin (m + 1))

set_option maxHeartbeats 800000 in
/-- The polynomial bound for the *opposite* representative of a rational
parabolic coset, using the inverse of the open cell of the flag quotient. -/
theorem exists_oppositeRationalHeightBound
    (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hstab : σ.HasExactCoordinateLineStabilizer (SubgroupFunctor.range q) j)
    (ζ : (Gm (Spec (CommRingCat.of F))).toGrp ⟶ G)
    (hQ : (Dynamic.parabolic ζ).IsRepresentedBy q)
    (iH : H ⟶ G) (hH : (Dynamic.unipotent (Dynamic.oppositeCocharacter ζ)).IsRepresentedBy iH) :
    ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ,
      ∀ x : AdelicSubgroupPoints.rationalPoints F G (SubgroupFunctor.range iH),
        adelicHeightAtLeastOne rho (rational F G x.val) ≤ C *
          (parabolicRationalProjectiveEmbedding σ j hstab
            (Quotient.mk _ ⟨rational F G x.val, ⟨x.val, rfl⟩⟩)).mulHeight ^ d := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let : IsAffineHom G.X.hom := hG.isAffineHom
  let : Mono q.hom.hom := hQ.1
  let D := parabolicProjectiveSections q σ j hG hq hstab
  let : IsProper D.quotient.hom := D.proper
  let : IsNoetherian D.quotient.left :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian D.quotient.hom
      toCompactSpace := QuasiCompact.compactSpace_of_compactSpace D.quotient.hom }
  let : IsClosedImmersion D.polynomialEmbedding := D.isClosedImmersion_polynomialEmbedding
  let : Smooth D.projection.left := D.smoothProjection
  let : Surjective D.projection.left := D.surjectiveProjection
  let : QuasiCompact D.projection.left := D.quasiCompactProjection
  let : IsOpenImmersion (QuotientCell.multiplication q iH.hom.hom).left :=
    oppositeCellStatement F G ζ H Q iH q hH hQ
  let cell := iH.hom.hom ≫ D.projection
  let : IsOpenImmersion cell.left :=
    QuotientCell.isOpenImmersion q iH.hom.hom D.projection D.fibers
  let Chart := ProjectiveSectionChart D.polynomialEmbedding cell
  obtain ⟨t, hcover⟩ := ProjectiveSectionChart.exists_finite_cover_of_openImmersion
    (q := cell) D.polynomialEmbedding_toSpec
  let a (x : RationalPoint F H.X) : Fin (m + 1) → F :=
    (σ.rationalMatrix (x ≫ iH.hom.hom)).val *ᵥ Pi.single j 1
  let I (S : Chart) := {x : RationalPoint F H.X //
    (x ≫ cell).left (IsLocalRing.closedPoint F) ∈ S.inclusion.left.opensRange}
  have hbound (S : Chart) :
      ∃ C : ℝ, 0 < C ∧ ∃ d : ℕ, ∀ x : I S,
        max 1 (AdelicMatrixHeight.height F N
            (AdelicGL.rational F N ((rho.restrict iH).rationalMatrix x.val))) ≤
          C * Height.mulHeight (a x.val) ^ d := by
    apply exists_rational_height_powerBound F (fun x : I S => (rho.restrict iH).rationalMatrix x.val)
      (fun x => Height.mulHeight (a x.val)) (fun x => Height.one_le_mulHeight (a x.val))
    intro b
    have h := S.regularFunction_mem_polynomialHeightBounded D.polynomialEmbedding_toSpec
      (fun x : I S => x.val ≫ cell) (fun x => x.property)
      (fun x => a x.val) (fun x => D.hasCoordinates (x.val ≫ iH.hom.hom))
      (matrixAndInverseEntryFunction (rho.restrict iH) b)
    have hlift (x : I S) : S.pointLift (x.val ≫ cell) x.property ≫ S.lift = x.val := by
      let : Mono cell := Over.mono_of_mono_left _
      apply (cancel_mono cell).mp
      rw [Category.assoc, S.lift_comp, S.pointLift_comp]
    simpa only [hlift, matrixAndInverseEntryFunction_eval] using h
  choose C hC d hd using hbound
  let C₀ := 1 + ∑ S ∈ t, C S
  let d₀ := t.sup d
  have hCs : 0 ≤ ∑ S ∈ t, C S := Finset.sum_nonneg fun S _ => (hC S).le
  refine ⟨C₀, by dsimp [C₀]; linarith, d₀, fun x => ?_⟩
  obtain ⟨x₀, hx₀⟩ := SubgroupFunctor.mem_range.mp x.property
  let E := FlagCore.baseAffineTestIso (R := CommRingCat.of F)
  let y : RationalPoint F H.X := E.hom ≫ x₀⁻¹
  obtain ⟨S, hS, hy⟩ := hcover y
  have hm : (rho.restrict iH).rationalMatrix y = rationalMatrix F G rho x.val⁻¹ := by
    rw [MatrixRepresentation.rationalMatrix_restrict]
    have h : y ≫ iH.hom.hom = E.hom ≫ x.val⁻¹ := by
      simp only [y, Category.assoc, GrpObj.inv_comp, hx₀]
    rw [h]
    exact FlagCore.rationalMatrix_baseAffineTestIso rho _
  have hσ : σ.rationalMatrix (y ≫ iH.hom.hom) = rationalMatrix F G σ x.val⁻¹ := by
    have h : y ≫ iH.hom.hom = E.hom ≫ x.val⁻¹ := by
      simp only [y, Category.assoc, GrpObj.inv_comp, hx₀]
    rw [h]
    exact FlagCore.rationalMatrix_baseAffineTestIso σ _
  have hC₀ : C S ≤ C₀ :=
    (Finset.single_le_sum (fun L _ => (hC L).le) hS).trans (le_add_of_nonneg_left zero_le_one)
  have hh := Height.one_le_mulHeight (a y)
  have hb := (hd S ⟨y, hy⟩).trans (mul_le_mul hC₀
    (pow_le_pow_right₀ hh (Finset.le_sup hS)) (pow_nonneg (zero_le_one.trans hh) _)
    (by dsimp [C₀]; linarith))
  change max 1 (AdelicMatrixHeight.height F N
    (AdelicGL.rational F N ((rho.restrict iH).rationalMatrix y))) ≤ C₀ * Height.mulHeight (a y) ^ d₀ at hb
  rw [hm] at hb
  rw [adelicHeightAtLeastOne, ← adelicHeight_inv F G rho (rational F G x.val), ← map_inv,
    adelicHeight, adelicMatrix_rational, parabolicRationalProjectiveEmbedding_mk,
    rationalOrbitPoint, Projectivization.mulHeight_mk, ← hσ]
  exact hb

end Langlands.Global.RepresentationGrowth

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme RepresentationGrowth

variable {F : Type u} [Field F] [NumberField F]
  {G Q M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine Q.X.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] {l : M ⟶ Q} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation q l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact q K)

set_option maxHeartbeats 1000000 in
/-- On the opposite radical, sufficiently regular Iwasawa powers decay faster
than any prescribed inverse power of the ambient adelic matrix height. -/
theorem IsIwasawaCompact.exists_decay_on_oppositeRadical (hG : IsConnectedReductive G)
    {N : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N) (s : ℝ) (hs : 0 ≤ s) :
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      ∃ B : ℝ, 0 < B ∧ ∀ x : AdelicGroupPoints F G,
        x ∈ (Dynamic.unipotent (Dynamic.oppositeCocharacter
          (CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ q))).carrier _ →
        ‖hK.heightPower lam x‖ ≤ B * adelicHeight F G rho x ^ (-s) := by
  classical
  let : Smooth G.X.hom := hG.smooth
  let ζ := CommGroupScheme.groupHom r.splitComponentCocharacter ≫ a ≫ l ≫ q
  let ξ := Dynamic.oppositeCocharacter ζ
  let H := Dynamic.Affine.unipotentScheme ξ
  let iH := Dynamic.Affine.unipotentHom ξ
  let hH := Dynamic.Affine.isRepresentedBy_unipotentHom ξ
  let : IsAffineHom H.X.hom := (Dynamic.Affine.isClosedSubgroup_unipotentHom ξ).isAffineHom
  let : IsAffine H.X.left := isAffine_of_isAffineHom H.X.hom
  have hQ : (Dynamic.parabolic ζ).IsRepresentedBy q :=
    ⟨Over.mono_of_mono_left _, r.parabolic_eq_splitComponentCocharacter⟩
  obtain ⟨n, j, σ, hstab⟩ := Chevalley.exists_line_stabilizer F G Q q
    r.isCompatible.parabolic.isClosedSubgroup
  obtain ⟨C, hC, d, hd⟩ :=
    exists_oppositeRationalHeightBound rho σ j hG r.isCompatible.parabolic hstab ζ hQ iH hH
  obtain ⟨Ω, hΩ, hcov⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F iH
    ((dynamicSmooth F G ξ H iH).2.2 hH)
    (DynamicConnected.connectedSpace_of_isRepresentedBy_unipotent G ξ hH)
    (dynamicUnipotentUnipotence F G ξ H iH hH)
  let Cpt : Set (AdelicGroupPoints F G) := Subtype.val '' Ω
  have hCpt : IsCompact Cpt := hΩ.image continuous_subtype_val
  obtain ⟨L₀, hL₀⟩ := (hCpt.image (continuous_adelicHeight F G rho hN)).bddAbove
  let L := max L₀ 1
  have hL : 0 < L := zero_lt_one.trans_le (le_max_right _ _)
  obtain ⟨R, hR⟩ := hK.exists_norm_heightPower_rational_le_projectiveHeight r hA hT hG σ j hstab
    (s * d) (mul_nonneg hs (Nat.cast_nonneg d))
  refine ⟨R, fun lam hlam => ?_⟩
  obtain ⟨k, ⟨e⟩⟩ := exists_complexParameterEquiv hG r.isCompatible.parabolic
  let Λ : Set (Fin k → ℂ) := {e.symm lam}
  have hΛ : IsCompact Λ := isCompact_singleton
  have hreg : ∀ t ∈ Λ, r.IsRegularParameter hA hT R (e t) := by
    intro t ht
    rw [show t = e.symm lam from ht, e.apply_symm_apply]
    exact hlam
  obtain ⟨B, hB, hBound⟩ := hR k e.toLinearMap Λ hΛ hreg
  obtain ⟨E, hE, hMult⟩ := hK.exists_norm_heightPower_mul_le hCpt e.toLinearMap hΛ
  refine ⟨E * B * (C * L) ^ s, by positivity, fun x hx => ?_⟩
  have hx' : x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range iH) :=
    hH.2.symm ▸ hx
  let y : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range iH) := ⟨x, hx'⟩
  obtain ⟨δ, hδ, hδy⟩ := hcov y
  obtain ⟨v, hv⟩ := hδ
  let ω := δ * y
  have hω : (ω : AdelicGroupPoints F G) ∈ Cpt := ⟨ω, hδy, rfl⟩
  have hxy : x = rational F G (v⁻¹).val * (ω : AdelicGroupPoints F G) := by
    change x = (rational F G v.val⁻¹) * (ω : AdelicGroupPoints F G)
    rw [map_inv]
    rw [← AdelicSubgroupPoints.rational_coe, hv]
    change x = ((δ⁻¹ * (δ * y) :
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range iH)) : AdelicGroupPoints F G)
    rw [inv_mul_cancel_left]
  let b := (parabolicRationalProjectiveEmbedding σ j hstab
    (Quotient.mk _ ⟨rational F G (v⁻¹).val, ⟨(v⁻¹).val, rfl⟩⟩)).mulHeight
  have hb : 0 < b := Projectivization.mulHeight_pos _
  have hlω : adelicHeight F G rho (ω : AdelicGroupPoints F G) ≤ L :=
    (hL₀ ⟨_, hω, rfl⟩).trans (le_max_left _ _)
  have hxB : adelicHeight F G rho x ≤ (C * L) * b ^ d := by
    rw [hxy]
    exact (adelicHeight_mul_le F G rho hN _ _).trans
      ((mul_le_mul (by simpa only [adelicHeightAtLeastOne_eq hN] using hd v⁻¹) hlω
        (zero_le_one.trans (one_le_adelicHeight F G rho hN _)) (by positivity)).trans_eq (by ring))
  have hpow : b ^ (-(s * d)) ≤ (C * L) ^ s * adelicHeight F G rho x ^ (-s) := by
    have hX := one_le_adelicHeight F G rho hN x
    have hdivide : adelicHeight F G rho x / (C * L) ≤ b ^ d :=
      (div_le_iff₀ (mul_pos hC hL)).mpr (by simpa only [mul_comm] using hxB)
    rw [show -(s * (d : ℝ)) = (d : ℝ) * (-s) by ring, Real.rpow_mul hb.le,
      Real.rpow_natCast]
    refine (Real.rpow_le_rpow_of_nonpos (by positivity) hdivide (neg_nonpos.mpr hs)).trans_eq ?_
    rw [Real.div_rpow (zero_le_one.trans hX) (mul_pos hC hL).le, Real.rpow_neg (mul_pos hC hL).le,
      div_inv_eq_mul, mul_comm]
  have h₁ := hMult (rational F G (v⁻¹).val) _ hω (e.symm lam) (mem_singleton _)
  have h₂ := hBound (v⁻¹).val (e.symm lam) (mem_singleton _)
  simp only [LinearEquiv.coe_coe, e.apply_symm_apply] at h₁ h₂
  calc
    ‖hK.heightPower lam x‖ =
        ‖hK.heightPower lam (rational F G (v⁻¹).val * (ω : AdelicGroupPoints F G))‖ :=
      congrArg (fun g => ‖hK.heightPower lam g‖) hxy
    _ ≤ E * (B * b ^ (-(s * d))) :=
      h₁.trans (mul_le_mul_of_nonneg_left h₂ hE.le)
    _ ≤ _ := by
      rw [← mul_assoc]
      exact (mul_le_mul_of_nonneg_left hpow (mul_nonneg hE.le hB.le)).trans_eq (by ring)

end Langlands.Global.AdelicGroupPoints

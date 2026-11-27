import Langlands.Global.AdelicCentralPositiveHeightProof
import Langlands.Global.AdelicOpenIwasawaCompact
import Langlands.Global.InfiniteAdelicGroupManifold
import Langlands.Global.InfinitePlaceRealizationSmooth
import Langlands.Global.RelativeRootChamber

/-! # Smooth logarithmic coordinates on the adelic split center -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped CategoryTheory.MonObj Manifold ContDiff NNReal Matrix.Norms.Operator

set_option maxHeartbeats 650000
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.PositiveRealTorus

open Langlands.GroupScheme AdelicGroupPoints RepresentationGrowth

variable (F : Type u) [Field F] [NumberField F]
  (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left]
  (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
  {r : ℕ} (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r)))

/-- Exponentiate real coordinates in the supplied splitting of the actual torus. -/
def logarithmicPoint (x : (ULift.{u} (Fin r) → ℝ)) : AdelicGroupPoints F G :=
  positivePointMap F G T i (fullIntrinsic F T (ULift.{u} (Fin r)) e fun j => expUnit (x j))

omit [IsAffine G.X.left] in
private theorem logarithmicPoint_apply (x : (ULift.{u} (Fin r) → ℝ)) :
    logarithmicPoint F G T i e x = AdelicGroupPoints.map F T.toGrp G i
      (full F (ULift.{u} (Fin r)) T e fun j => expUnit (x j)) := rfl

private theorem expUnit_add (x y : ℝ) : expUnit (x + y) = expUnit x * expUnit y := by
  apply Units.ext
  apply NNReal.eq
  simp only [coe_expUnit, Units.val_mul, NNReal.coe_mul, Real.exp_add]

omit [IsAffine G.X.left] in
private theorem logarithmicPoint_add (x y : (ULift.{u} (Fin r) → ℝ)) :
    logarithmicPoint F G T i e (x + y) =
      logarithmicPoint F G T i e x * logarithmicPoint F G T i e y := by
  simp only [logarithmicPoint_apply, Pi.add_apply, expUnit_add]
  rw [show (fun j : ULift (Fin r) => expUnit (x j) * expUnit (y j)) =
    (fun j => expUnit (x j)) * (fun j => expUnit (y j)) from rfl, map_mul, map_mul]

omit [IsAffine G.X.left] in
private theorem logarithmicPoint_zero : logarithmicPoint F G T i e 0 = 1 := by
  have he : (fun _ : ULift.{u} (Fin r) => expUnit 0) = 1 := by
    funext j
    apply Units.ext
    apply NNReal.eq
    exact Real.exp_zero
  unfold logarithmicPoint
  change positivePointMap F G T i (fullIntrinsic F T _ e (fun _ => expUnit 0)) = 1
  rw [he, map_one, map_one]

/-- Logarithmic coordinates give a smooth map to the original infinite point group. -/
theorem contMDiff_infinite_logarithmicPoint {d : ℕ} (hsmooth : SmoothOfRelativeDimension d G.X.hom) :
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    ContMDiff 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞
      (fun x => infinite F G (logarithmicPoint F G T i e x)) := by
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.smoothChartedSpace F G v hsmooth
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  apply (InfiniteAdelicGroupPoints.contMDiff_iff_places F G 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) hsmooth _).mpr
  intro v
  apply (InfinitePlaceGroupPoints.contMDiff_iff_coordinateSmooth F G v 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) hsmooth _).mpr
  let A := CommAlgCat.of F (Adeles F)
  let T' : GroupScheme (Spec (CommRingCat.of F)) := T.toGrp
  let p (x : (ULift.{u} (Fin r) → ℝ)) : T'.affinePoints A := full F (ULift.{u} (Fin r)) T e fun j => expUnit (x j)
  let D : MatrixRepresentation T' (Fin r) :=
    e.hom ≫ GeneralLinear.diagonalTorus (Fin r) (CommRingCat.of F)
  let c : A →+* v.Completion := infiniteProjection F v
  have hp : T'.CoordinateSmooth A c 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) p := by
    apply MatrixRepresentation.coordinateSmooth_of_postcomp D
      ((IsClosedSubgroup.of_iso e).comp (GeneralLinear.isClosedSubgroup_diagonalTorus _ _))
    apply (GeneralLinear.coordinateSmooth_iff_contMDiff (Fin r) (CommRingCat.of F) A
      (B := v.Completion) c 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) (fun x => p x ≫ D.hom.hom)).mpr
    apply ContMDiff.of_comp_isOpenEmbedding Units.isOpenEmbedding_val
    let L : (Fin r → Fin r → v.Completion) →L[ℝ] Matrix (Fin r) (Fin r) v.Completion :=
      { toLinearMap := LinearMap.id, cont := continuous_id }
    change ContMDiff 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) 𝓘(ℝ, Matrix (Fin r) (Fin r) v.Completion) ∞
      (fun x => L (fun a b => infiniteProjection F v ((adelicMatrix F T.toGrp D (p x)).val a b)))
    apply L.contDiff.contMDiff.comp
    apply contMDiff_pi_module_iff.mpr
    intro a
    apply contMDiff_pi_module_iff.mpr
    intro b
    simp only [D, p, adelicMatrix_diagonalTorus_full, Matrix.diagonal_apply]
    by_cases hab : a = b
    · simp only [hab, ite_true]
      change ContMDiff 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) 𝓘(ℝ, v.Completion) ∞
        (fun x : ULift.{u} (Fin r) → ℝ => PositiveRealIdeles.realEmbedding F v (Real.exp (x ⟨b⟩)))
      let R : ℝ →L[ℝ] v.Completion :=
        { (PositiveRealIdeles.realEmbedding F v).toAddMonoidHom.toRealLinearMap
            (PositiveRealIdeles.continuous_realEmbedding F v) with
          cont := PositiveRealIdeles.continuous_realEmbedding F v }
      let q := ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : ULift.{u} (Fin r) => ℝ) ⟨b⟩
      exact R.contDiff.contMDiff.comp ((Real.contDiff_exp.comp q.contDiff).contMDiff)
    · simp only [hab, ite_false, map_zero, contMDiff_const]
  have hG := hp.postcomp i.hom.hom
  intro a
  convert hG a using 2 with x
  dsimp only
  rw [← atInfinitePlace_eq_atPlace_infinite, RingHom.id_apply, atInfinitePlace_evaluation,
    logarithmicPoint_apply]
  rfl

/-- Smooth additive parameters for the actual split central factor. The exponential of
its coordinate norm is bounded by one polynomial in the full height. -/
def CentralLogParameterStatement : Prop :=
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffine G.X.left] {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom),
    IsConnectedReductive G → IsClosedSubgroup rho → 0 < N →
    letI := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
    ∃ (r : ℕ) (c : (ULift.{u} (Fin r) → ℝ) → InfiniteAdelicGroupPoints F G),
      ContMDiff 𝓘(ℝ, ULift.{u} (Fin r) → ℝ) 𝓘(ℝ, InfiniteAdelicGroupPoints.smoothModel F d) ∞ c ∧
      c 0 = 1 ∧ (∀ x y, c (x + y) = c x * c y) ∧
      (∀ x g, Commute (c x) g) ∧
      ∃ (C : ℝ) (k : ℕ), 0 < C ∧ ∀ g : AdelicGroupPoints F G,
        ∃ (x : ULift.{u} (Fin r) → ℝ) (n : normOneSubgroup F G),
          g = n.val * ofInfinite F G (c x) ∧ Real.exp ‖x‖ ≤ C * adelicHeight F G rho g ^ k

/-- The matrix height controls the logarithmic parameter through the restrictions of
ambient rational characters to the split component. -/
theorem centralLogParameter : CentralLogParameterStatement.{u} := by
  intro F _ _ G _ N d rho hsmooth hG hρ hN
  classical
  let := fun v : InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := InfiniteAdelicGroupPoints.smoothChartedSpace F G hsmooth
  have : Smooth G.X.hom := hG.smooth
  obtain ⟨T, i, hi, E, hE⟩ := adelicPositiveDecompositionStatement F G hG
  have hT : IsSplitTorus T.toGrp := hi.1.1.1
  have hrestr : (characterRestrict i).range.FiniteIndex :=
    characterRestrictionFiniteIndexStatement F G hG T i hi
  obtain ⟨I, _, ⟨e₀⟩⟩ := hT
  let : Fintype I := Fintype.ofFinite I
  let r := Fintype.card I
  let σ : ULift.{u} (Fin r) ≃ I := Equiv.ulift.trans (Fintype.equivFin I).symm
  let e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) (ULift.{u} (Fin r)) :=
    e₀ ≪≫ LocalSplitCell.exponentEquivGroupIso _ (LinearEquiv.funCongrLeft ℤ ℤ σ)
  let a (x : (ULift.{u} (Fin r) → ℝ)) := logarithmicPoint F G T i e x
  let c (x : (ULift.{u} (Fin r) → ℝ)) := infinite F G (a x)
  have ha (x : (ULift.{u} (Fin r) → ℝ)) (g : AdelicGroupPoints F G) : Commute (a x) g :=
    positivePointMap_commute F G T i hi.1.2 _ g
  have hfin (x : (ULift.{u} (Fin r) → ℝ)) : finite F G (a x) = 1 :=
    finite_positivePointMap F T i hi.1.1.1 _
  have hc (x : (ULift.{u} (Fin r) → ℝ)) : ofInfinite F G (c x) = a x := by
    rw [ofInfinite_eq_pair, show c x = infinite F G (a x) from rfl,
      ← hfin x, pair_projections]
  refine ⟨r, c, contMDiff_infinite_logarithmicPoint F G T i e hsmooth, ?_, ?_, ?_, ?_⟩
  · simp only [c, a, logarithmicPoint_zero, map_one]
  · intro x y
    simp only [c, a, logarithmicPoint_add, map_mul]
  · intro x g
    have h := (ha x (ofInfinite F G g)).map (infinite F G).toMonoidHom
    change Commute (c x) (infinite F G (ofInfinite F G g)) at h
    rwa [infinite_ofInfinite] at h
  obtain ⟨m, hm, hχ⟩ := exists_characterNorm_full F T i e
  choose χ hχ using hχ
  choose C hC k hk using fun j => exists_characterNorm_le F rho hN hρ (χ j)
  let M : ℝ := 1 + ∑ j, C j
  let K : ℕ := ∑ j, k j
  have hM : 1 ≤ M := le_add_of_nonneg_right (Finset.sum_nonneg fun j _ => zero_le_one.trans (hC j))
  refine ⟨M, K, zero_lt_one.trans_le hM, fun g => ?_⟩
  let p := E.symm g
  obtain ⟨y, hy⟩ := fullIntrinsic_surjective F T _ e p.1
  let x : (ULift.{u} (Fin r) → ℝ) := fun j => Real.log ((y j : ℝ≥0) : ℝ)
  have hay : a x = positivePointMap F G T i p.1 := by
    change positivePointMap F G T i (fullIntrinsic F T _ e fun j => expUnit (x j)) = _
    have hx : (fun j => expUnit (x j)) = y := funext fun j => expUnit_log (y j)
    rw [hx, hy]
  have hg : g = a x * p.2.val := by rw [hay, ← hE, E.apply_symm_apply]
  refine ⟨x, p.2, ?_, ?_⟩
  · rw [hc]
    exact hg.trans (ha x _).eq
  let H := adelicHeight F G rho g
  have hH : 1 ≤ H := one_le_adelicHeight F G rho hN g
  let q := m * Module.finrank ℚ F
  have hq : 0 < q := Nat.mul_pos hm Module.finrank_pos
  have hnorm (j : ULift.{u} (Fin r)) : characterNorm F G (χ j).toMul g = y j ^ q := by
    rw [hg, map_mul, (mem_normOneSubgroup F G _).mp p.2.property, mul_one]
    change characterNorm F G (χ j).toMul (logarithmicPoint F G T i e x) = _
    rw [logarithmicPoint_apply, hχ]
    exact congrArg (fun z : ℝ≥0ˣ => z ^ q) (expUnit_log (y j))
  have hb (j : ULift.{u} (Fin r)) :
      (max (((y j : ℝ≥0ˣ) : ℝ≥0) : ℝ) (((((y j)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) : ℝ)) ≤ M * H ^ K := by
    have h1 := (hk j g).1
    have h2 := (hk j g).2
    rw [hnorm j] at h1 h2
    have hbound : C j * H ^ k j ≤ M * H ^ K := by
      apply mul_le_mul _ _ (pow_nonneg (zero_le_one.trans hH) _) (zero_le_one.trans hM)
      · exact (Finset.single_le_sum (fun j _ => zero_le_one.trans (hC j)) (Finset.mem_univ j)).trans
          (le_add_of_nonneg_left zero_le_one)
      · exact pow_le_pow_right₀ hH (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j))
    have hmax := max_inv_pow_le (y j) q _ (h1.trans hbound) (h2.trans hbound)
    simp only [NNReal.coe_max] at hmax
    have hmax1 : 1 ≤ max (((y j : ℝ≥0ˣ) : ℝ≥0) : ℝ) (((((y j)⁻¹ : ℝ≥0ˣ) : ℝ≥0)) : ℝ) := by
      exact_mod_cast one_le_max_inv (y j)
    simpa only [pow_one] using (pow_le_pow_right₀ hmax1 hq).trans hmax
  have hMH : 1 ≤ M * H ^ K := one_le_mul_of_one_le_of_one_le hM (one_le_pow₀ hH)
  have hn : ‖x‖ ≤ Real.log (M * H ^ K) := by
    apply pi_norm_le_iff_of_nonneg (Real.log_nonneg hMH) |>.2
    intro j
    rw [Real.norm_eq_abs, abs_le]
    have hyj : (0 : ℝ) < ((y j : ℝ≥0) : ℝ) := by
      exact_mod_cast (pos_iff_ne_zero.mpr (y j).ne_zero)
    refine ⟨?_, Real.log_le_log hyj ((le_max_left _ _).trans (hb j))⟩
    have hinv : (((y j)⁻¹ : ℝ≥0ˣ) : ℝ≥0) = ((y j : ℝ≥0) : ℝ≥0)⁻¹ := Units.val_inv_eq_inv_val _
    have hleft := Real.log_le_log (inv_pos.mpr hyj) (show (((y j : ℝ≥0) : ℝ)⁻¹) ≤ M * H ^ K by
      have h := (le_max_right _ _).trans (hb j)
      rwa [hinv, NNReal.coe_inv] at h)
    rw [Real.log_inv] at hleft
    exact neg_le.mp hleft
  exact (Real.exp_le_exp.mpr hn).trans (Real.exp_log (zero_lt_one.trans_le hMH)).le

end Langlands.Global.PositiveRealTorus

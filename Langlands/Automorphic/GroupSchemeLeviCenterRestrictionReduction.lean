import Langlands.Automorphic.GroupSchemeLeviCenterRestriction
import Langlands.Automorphic.GroupSchemePointDifferential
import Langlands.Automorphic.GroupSchemePlotSmoothRightCovariance
import Langlands.Automorphic.GroupSchemeAutomorphicLeftTranslation
import Langlands.Algebra.ParabolicCenterProjectionExistence

/-! # Finite Levi restriction of the archimedean enveloping centres, from two tangent inputs -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField
open scoped Classical CategoryTheory.MonObj Manifold ContDiff TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.InfiniteAdelicGroupPoints Langlands.GroupScheme
  Langlands.Geometry.Manifold

attribute [local instance 100] LieRing.ofAssociativeRing

variable {F : Type u} [Field F] [NumberField F]
  {G Q M V : GroupScheme (Spec (CommRingCat.of F))}
  {q : Q ⟶ G} {iV : V ⟶ Q} {l : M ⟶ Q}

local notation "A∞" => CommAlgCat.of F (InfiniteAdeleRing F)

omit [NumberField F] in
/-- Levi points normalize the radical points: `l(m) ψ(v) = ψ(v') l(m)`. -/
theorem exists_radical_conj (hiV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (m : InfiniteAdelicGroupPoints F M) (v : InfiniteAdelicGroupPoints F V) :
    ∃ v' : InfiniteAdelicGroupPoints F V,
      M.affinePointsTarget (l ≫ q) A∞ m * V.affinePointsTarget (iV ≫ q) A∞ v =
        V.affinePointsTarget (iV ≫ q) A∞ v' * M.affinePointsTarget (l ≫ q) A∞ m := by
  let lm := M.affinePointsTarget l A∞ m
  let iv := V.affinePointsTarget iV A∞ v
  obtain ⟨v', hv'⟩ := hiV.1.isNormal _ lm iv (Subgroup.mem_top _) ⟨v, rfl⟩
  refine ⟨v', ?_⟩
  let qA := Q.affinePointsTarget q A∞
  have h1 : M.affinePointsTarget (l ≫ q) A∞ m = qA lm := rfl
  have h2 : V.affinePointsTarget (iV ≫ q) A∞ v = qA iv := rfl
  have h3 : V.affinePointsTarget (iV ≫ q) A∞ v' = qA (lm * iv * lm⁻¹) := by
    rw [← hv']
    rfl
  rw [h1, h2, h3, ← map_mul, ← map_mul]
  congr 1
  group

/-- Left invariance under the radical points. -/
def IsRadicalLeftInvariant [IsAffine G.X.left] (q : Q ⟶ G) (iV : V ⟶ Q)
    (u : InfinitePlotSmoothFunctions F G) : Prop :=
  ∀ (v : InfiniteAdelicGroupPoints F V) (x : InfiniteAdelicGroupPoints F G),
    u.val (V.affinePointsTarget (iV ≫ q) A∞ v * x) = u.val x

variable [IsAffine G.X.left] [IsAffine M.X.left] [IsAffine V.X.left] {d e c : ℕ}

omit [IsAffine M.X.left] in
/-- A radical tangent derivative of a radical-invariant function vanishes along the Levi. -/
theorem pointPullback_differential_radical (hiV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hG : SmoothOfRelativeDimension d G.X.hom) (hV : SmoothOfRelativeDimension c V.X.hom)
    (u : InfinitePlotSmoothFunctions F G) (hu : IsRadicalLeftInvariant q iV u)
    (Y : smoothModel F c) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothChartedSpace F V hV
    Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (plotSmoothDifferential F G hG
        (mfderiv 𝓘(ℝ, smoothModel F c) 𝓘(ℝ, smoothModel F d)
          (V.affinePointsTarget (iV ≫ q) A∞) 1 Y) u) = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let := smoothChartedSpace F V hV
  let := smoothLieGroup F V hV
  apply Subtype.ext
  funext m
  let φm := M.affinePointsTarget (l ≫ q) A∞ m
  let ψ := V.affinePointsTarget (iV ≫ q) A∞
  have hsmooth := (isPlotSmooth_iff_contMDiff F G hG u.val).mp u.property
  have hshift : ContMDiff 𝓘(ℝ, smoothModel F d) 𝓘(ℝ, ℂ) ∞ (fun x => u.val (φm * x)) :=
    hsmooth.comp (contMDiff_mul_left (a := φm))
  have hconst : (fun v => u.val (φm * ψ v)) = fun _ => u.val φm := by
    funext v
    obtain ⟨v', hv'⟩ := exists_radical_conj (F := F) (q := q) (l := l) hiV m v
    rw [show φm * ψ v = ψ v' * φm from hv']
    exact hu v' φm
  change groupDirectionalValue 𝓘(ℝ, smoothModel F d)
      (groupHomTangent 𝓘(ℝ, smoothModel F c) 𝓘(ℝ, smoothModel F d) ψ Y) u.val φm = 0
  have h1 := groupDirectionalValue_leftTranslation 𝓘(ℝ, smoothModel F d)
    (groupHomTangent 𝓘(ℝ, smoothModel F c) 𝓘(ℝ, smoothModel F d) ψ Y) φm u.val 1
  rw [mul_one] at h1
  rw [← h1]
  have h2 := groupDirectionalValue_comp_hom 𝓘(ℝ, smoothModel F c) 𝓘(ℝ, smoothModel F d) ψ
    (contMDiff_affinePointsTarget F hV hG (iV ≫ q)) Y hshift 1
  rw [map_one] at h2
  rw [← h2, hconst]
  simp [groupDirectionalValue, mvfderiv_const]

omit [IsAffine M.X.left] [IsAffine V.X.left] in
/-- The enveloping action preserves radical left invariance. -/
theorem IsRadicalLeftInvariant.envelopingAction (hG : SmoothOfRelativeDimension d G.X.hom)
    (hcG : AdelicDifferentialCommutator F G hG) {u : InfinitePlotSmoothFunctions F G}
    (hu : IsRadicalLeftInvariant q iV u) (w : AdelicEnvelopingAlgebra F G hG) :
    IsRadicalLeftInvariant q iV (plotSmoothEnvelopingAction F G hG hcG w u) := by
  intro v x
  have hfix : plotSmoothLeftTranslation F G (V.affinePointsTarget (iV ≫ q) A∞ v) u = u :=
    Subtype.ext (funext fun y => hu v y)
  have h := congrArg (fun s : InfinitePlotSmoothFunctions F G => s.val x)
    (plotSmoothEnvelopingAction_leftTranslation hcG (V.affinePointsTarget (iV ≫ q) A∞ v) w u)
  rw [hfix] at h
  exact h.symm

omit [IsAffine M.X.left] in
/-- The right ideal generated by the positive eigenvectors acts by operators whose Levi
restriction vanishes on radical-invariant functions. -/
theorem pointPullback_positiveRightIdeal (hiV : LeviSubgroup.IsGeometricUnipotentRadical iV)
    (hG : SmoothOfRelativeDimension d G.X.hom) (hV : SmoothOfRelativeDimension c V.X.hom)
    (hcG : AdelicDifferentialCommutator F G hG) (H : AdelicComplexLieAlgebra F G hG) :
    letI := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
    letI := smoothChartedSpace F G hG
    letI := smoothLieGroup F G hG
    letI : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
      (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
    LinearMap.range (complexPointDifferential F hV hG (iV ≫ q)) =
        Submodule.span ℂ {Y : AdelicComplexLieAlgebra F G hG |
          ∃ k : ℕ, ⁅H, Y⁆ = ((k + 1 : ℕ) : ℂ) • Y} →
    ∀ x ∈ Langlands.Algebra.ParabolicCenterProjection.positiveRightIdeal H,
    ∀ u : InfinitePlotSmoothFunctions F G, IsRadicalLeftInvariant q iV u →
      Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (plotSmoothEnvelopingAction F G hG hcG x u) = 0 := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let := smoothChartedSpace F V hV
  let := smoothLieGroup F V hV
  intro hrad x hx u hu
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, Y, hY, w, rfl⟩ := hx
    rw [map_mul, Module.End.mul_apply]
    have hu' := hu.envelopingAction hG hcG w
    generalize plotSmoothEnvelopingAction F G hG hcG w u = u' at hu' ⊢
    have hYr : Y ∈ LinearMap.range (complexPointDifferential F hV hG (iV ≫ q)) := by
      rw [hrad]
      exact Submodule.subset_span ⟨k, hY⟩
    obtain ⟨Y', rfl⟩ := hYr
    clear hY
    rw [plotSmoothEnvelopingAction_generator]
    induction Y' using TensorProduct.inductionOn with
    | tmul z X =>
      change Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (complexPlotSmoothLieAction F G hG hcG
        (z ⊗ₜ[ℝ] (mfderiv 𝓘(ℝ, smoothModel F c) 𝓘(ℝ, smoothModel F d)
          (V.affinePointsTarget (iV ≫ q) A∞) 1 X)) u') = 0
      rw [complexPlotSmoothLieAction_tmul, LinearMap.smul_apply, map_smul,
        pointPullback_differential_radical hiV hG hV u' hu' X, smul_zero]
    | add a b ha hb =>
      rw [map_add, map_add, LinearMap.add_apply, map_add, ha, hb, add_zero]
  | zero => rw [map_zero, LinearMap.zero_apply, map_zero]
  | add x y _ _ hx hy => rw [map_add, LinearMap.add_apply, map_add, hx, hy, add_zero]
  | smul t x _ hx => rw [map_smul, LinearMap.smul_apply, map_smul, hx, smul_zero]

/-- The identity-translate case: from the two tangent statements, a finite map of centres
intertwines Levi pullback on radical-invariant functions. -/
theorem exists_leviCenterProjection
    (hT1 :
      Langlands.Algebra.ParabolicCenterProjection.ParabolicCenterProjectionFiniteStatement.{u, u})
    (hT2 : ParabolicLeviTangentGradingStatement.{u})
    (hGr : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hiV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl : IsRationalLeviSubgroup l)
    (hiso : IsIso (subgroupMultiplication l iV))
    (hG : SmoothOfRelativeDimension d G.X.hom) (hM : SmoothOfRelativeDimension e M.X.hom)
    (hV : SmoothOfRelativeDimension c V.X.hom)
    (hcG : AdelicDifferentialCommutator F G hG) (hcM : AdelicDifferentialCommutator F M hM) :
    ∃ p : AdelicEnvelopingCenter F G hG →ₐ[ℂ] AdelicEnvelopingCenter F M hM,
      p.Finite ∧ ∀ u : InfinitePlotSmoothFunctions F G, IsRadicalLeftInvariant q iV u →
        ∀ z, Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (plotSmoothCenterAction F G hG hcG z u) =
          plotSmoothCenterAction F M hM hcM (p z) (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) u) := by
  let := fun v : NumberField.InfinitePlace F => InfinitePlaceGroupPoints.completionRCLike F v
  let := smoothChartedSpace F G hG
  let := smoothLieGroup F G hG
  let : LieGroup 𝓘(ℝ, smoothModel F d) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F G) := LieGroup.of_le (n := ∞) (by simp)
  let := smoothChartedSpace F M hM
  let := smoothLieGroup F M hM
  let : LieGroup 𝓘(ℝ, smoothModel F e) (minSmoothness ℝ 3)
    (InfiniteAdelicGroupPoints F M) := LieGroup.of_le (n := ∞) (by simp)
  obtain ⟨hred, H, hspan, hinj, hlevi, hrad⟩ :=
    hT2 F G Q M V q iV l hGr hq hiV hl hiso hG hM hV
  let j := complexPointLieDifferential hM hG (l ≫ q)
  have hj : Function.Injective j := hinj
  have hrange : ∀ X, X ∈ Set.range j ↔ ⁅H, X⁆ = 0 := fun X => hlevi X
  obtain ⟨p, hp⟩ := Langlands.Algebra.ParabolicCenterProjection.exists_centerProjection
    j H hspan hj hrange
  refine ⟨p, hT1 _ _ j H hred hspan hj hrange p hp, fun u hu z => ?_⟩
  let J := UniversalEnvelopingAlgebra.lift ℂ ((UniversalEnvelopingAlgebra.ι ℂ).comp j)
  have hdec : (z : AdelicEnvelopingAlgebra F G hG) =
      J (p z : AdelicEnvelopingAlgebra F M hM) + ((z : AdelicEnvelopingAlgebra F G hG) -
        J (p z : AdelicEnvelopingAlgebra F M hM)) := by abel
  change Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (plotSmoothEnvelopingAction F G hG hcG z.val u) =
    plotSmoothEnvelopingAction F M hM hcM (p z).val (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) u)
  rw [hdec, map_add, LinearMap.add_apply, map_add, pointPullback_envelopingAction,
    pointPullback_positiveRightIdeal hiV hG hV hcG H hrad _ (hp z) u hu, add_zero]

/-- The adjoint action of an infinite point, as an algebra endomorphism of the centre. -/
def centerConjugationAlgHom (hG : SmoothOfRelativeDimension d G.X.hom)
    (a : InfiniteAdelicGroupPoints F G) :
    AdelicEnvelopingCenter F G hG →ₐ[ℂ] AdelicEnvelopingCenter F G hG where
  toFun := adelicCenterConjugation F G hG a
  map_one' := Subtype.ext (map_one (adelicEnvelopingConjugation F G hG a))
  map_mul' x y := Subtype.ext (map_mul (adelicEnvelopingConjugation F G hG a) x.val y.val)
  map_zero' := Subtype.ext (map_zero (adelicEnvelopingConjugation F G hG a))
  map_add' x y := Subtype.ext (map_add (adelicEnvelopingConjugation F G hG a) x.val y.val)
  commutes' t := Subtype.ext ((adelicEnvelopingConjugation F G hG a).commutes t)

theorem centerConjugationAlgHom_surjective (hG : SmoothOfRelativeDimension d G.X.hom)
    (a : InfiniteAdelicGroupPoints F G) :
    Function.Surjective (centerConjugationAlgHom hG a) := fun z =>
  ⟨adelicCenterConjugation F G hG a⁻¹ z,
    Subtype.ext (adelicEnvelopingConjugation_apply_inv F G hG a z.val)⟩

omit [IsAffine G.X.left] [IsAffine M.X.left] [IsAffine V.X.left] in
/-- **Finite Levi restriction of the archimedean enveloping centres**, from the algebraic
finiteness of Harish-Chandra's projection and the archimedean tangent grading of a parabolic. -/
theorem parabolicLeviCenterRestriction_of_tangent
    (hT1 :
      Langlands.Algebra.ParabolicCenterProjection.ParabolicCenterProjectionFiniteStatement.{u, u})
    (hT2 : ParabolicLeviTangentGradingStatement.{u}) :
    ParabolicLeviCenterRestrictionStatement.{u} := by
  intro F _ _ G Q M V _ _ q iV l hGr hq hiV hl hiso d e hG hM hcG hcM a
  have hcl : IsClosedImmersion (iV ≫ q).hom.hom.left := by
    have h1 : IsClosedImmersion iV.hom.hom.left := hiV.1.isClosedSubgroup
    have h2 : IsClosedImmersion q.hom.hom.left := hq.isClosedSubgroup
    change IsClosedImmersion (iV.hom.hom.left ≫ q.hom.hom.left)
    infer_instance
  have : IsAffine V.X.left := isAffine_of_isAffineHom (iV ≫ q).hom.hom.left
  obtain ⟨c, hV⟩ := Langlands.AlgebraicGeometry.smoothConnectedRelativeDimension V.X.left _
    V.X.hom hiV.1.smooth hiV.1.connectedSpace
  obtain ⟨p, hpfin, hp⟩ :=
    exists_leviCenterProjection hT1 hT2 hGr hq hiV hl hiso hG hM hV hcG hcM
  refine ⟨p.comp (centerConjugationAlgHom hG a),
    hpfin.comp (AlgHom.Finite.of_surjective _ (centerConjugationAlgHom_surjective hG a)),
    fun f hf z => ?_⟩
  let ρ := G.plotSmoothRightAction (CommAlgCat.of F (InfiniteAdeleRing F))
    (B := mixedEmbedding.mixedSpace F) (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom a
  have hres (g : InfinitePlotSmoothFunctions F G) :
      infiniteLeviRestriction (q := q) l a g = Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (ρ g) := Subtype.ext rfl
  have hρf : IsRadicalLeftInvariant q iV (ρ f) := fun v x => by
    change f.val (V.affinePointsTarget (iV ≫ q) (CommAlgCat.of F (InfiniteAdeleRing F)) v * x * a) =
      f.val (x * a)
    rw [mul_assoc]
    exact hf v (x * a)
  rw [hres, hres]
  change Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (ρ (plotSmoothEnvelopingAction F G hG hcG z.val f)) =
    plotSmoothCenterAction F M hM hcM (p (centerConjugationAlgHom hG a z))
      (Langlands.Global.InfiniteAdelicGroupPoints.plotSmoothPullback (l ≫ q) (ρ f))
  have hcov : ρ (plotSmoothEnvelopingAction F G hG hcG z.val f) =
      plotSmoothEnvelopingAction F G hG hcG (adelicEnvelopingConjugation F G hG a z.val) (ρ f) :=
    adelicPlotSmoothEnvelopingRightCovariance F G hG hcG a z.val f
  rw [hcov, ← hp (ρ f) hρf]
  rfl

/-- The finite Levi restriction of the actual archimedean enveloping centres follows from the
finiteness of Harish-Chandra's projection for reductive complex Lie algebras and from the
archimedean tangent grading of a rational parabolic. -/
def ParabolicLeviCenterRestrictionReductionStatement : Prop :=
  Langlands.Algebra.ParabolicCenterProjection.ParabolicCenterProjectionFiniteStatement.{u, u} →
    ParabolicLeviTangentGradingStatement.{u} → ParabolicLeviCenterRestrictionStatement.{u}

theorem parabolicLeviCenterRestrictionReduction :
    ParabolicLeviCenterRestrictionReductionStatement.{u} :=
  parabolicLeviCenterRestriction_of_tangent

end Langlands.Automorphic.GroupSchemeFunctions

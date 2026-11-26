import Langlands.Global.AdelicComplexParameters
import Langlands.Global.AdelicGroupNormOneFunctorial
import Langlands.Global.AdelicGroupLocalPoints
import Langlands.Automorphic.GroupSchemeFiniteLevelSlices
import Langlands.Global.ArchimedeanCharacterSmoothness

/-! # Plot-smooth restrictions and characters on infinite adelic points

Plot-smoothness of functions on `G(F_∞)` is preserved by composition with the point map of a
morphism of group schemes and by left and right translations, and by products. For a rational
character parameter `λ` of a group scheme `H` and a morphism `j : G → H`, the function
`m ↦ j(m)^λ` on `G(F_∞)` is plot-smooth. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain
open scoped Classical CategoryTheory.MonObj Manifold ContDiff NNReal

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxSize 256

namespace Langlands.Global.InfiniteAdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type u} [Field F] [NumberField F]

local notation "Ainf" => CommAlgCat.of F (InfiniteAdeleRing F)

/-- Plot-smooth functions are closed under pointwise products. -/
theorem mul_mem_infinitePlotSmoothFunctions {G : GroupScheme (Spec (CommRingCat.of F))}
    {f g : InfiniteAdelicGroupPoints F G → ℂ} (hf : f ∈ InfinitePlotSmoothFunctions F G)
    (hg : g ∈ InfinitePlotSmoothFunctions F G) :
    (fun x => f x * g x) ∈ InfinitePlotSmoothFunctions F G := by
  intro E _ _ M _ _ p hp
  have h1 := hf E M p hp
  have h2 := hg E M p hp
  have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_mul
  exact hmul.contMDiff.comp (h1.prodMk_space h2)

/-- Composition with the point map of a morphism of group schemes and two translations preserves
plot-smoothness. -/
theorem comp_affinePointsTarget_mem_infinitePlotSmoothFunctions
    {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] (j : H ⟶ G)
    (a b : InfiniteAdelicGroupPoints F G) {f : InfiniteAdelicGroupPoints F G → ℂ}
    (hf : f ∈ InfinitePlotSmoothFunctions F G) :
    (fun m => f (a * H.affinePointsTarget j Ainf m * b)) ∈ InfinitePlotSmoothFunctions F H := by
  intro E _ _ M _ _ p hp
  have hq := CoordinateSmooth.mul G _ _ _
    (CoordinateSmooth.mul G _ _ _ (coordinateSmooth_const G _ _ 𝓘(ℝ, E) a)
      (hp.postcomp j.hom.hom))
    (coordinateSmooth_const G _ _ 𝓘(ℝ, E) b)
  exact hf E M _ hq


/-- At a point with trivial finite components, the adelic norm of an algebraic character is the
archimedean norm of its value. -/
theorem characterNorm_ofInfinite {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left]
    (χ : AlgebraicCharacter F G) (y : InfiniteAdelicGroupPoints F G) :
    characterNorm F G χ (ofInfinite F G y) =
      IdeleAbsoluteValue.infinite F (characterUnits F G χ Ainf y) := by
  have hfst : Units.map (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toRingHom.toMonoidHom
      (character F G χ (ofInfinite F G y)) = characterUnits F G χ Ainf y := by
    have h := characterUnits_naturality F G χ
      (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
      (ofInfinite F G y)
    have hy : G.affinePointMap (CommAlgCat.ofHom (AlgHom.fst F (InfiniteAdeleRing F)
        (FiniteAdeleRing (𝓞 F) F))) (ofInfinite F G y) = y := infinite_ofInfinite F G y
    rw [hy] at h
    exact h.symm
  have hsnd : Units.map (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)).toRingHom.toMonoidHom
      (character F G χ (ofInfinite F G y)) = 1 := by
    have h := characterUnits_naturality F G χ
      (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F) (FiniteAdeleRing (𝓞 F) F)))
      (ofInfinite F G y)
    have hy : G.affinePointMap (CommAlgCat.ofHom (AlgHom.snd F (InfiniteAdeleRing F)
        (FiniteAdeleRing (𝓞 F) F))) (ofInfinite F G y) = 1 := finite_ofInfinite F G y
    rw [hy, map_one] at h
    exact h.symm
  change IdeleAbsoluteValue.infinite F ((ideleProductEquiv F (character F G χ (ofInfinite F G y))).1) *
      IdeleAbsoluteValue.finite F ((ideleProductEquiv F (character F G χ (ofInfinite F G y))).2) = _
  have h1 : (ideleProductEquiv F (character F G χ (ofInfinite F G y))).1 =
      characterUnits F G χ Ainf y := by
    rw [← hfst]
    rfl
  have h2 : (ideleProductEquiv F (character F G χ (ofInfinite F G y))).2 = 1 := by
    rw [← hsnd]
    rfl
  rw [h1, h2, map_one, mul_one]


variable (F) in
/-- The archimedean norm `u ↦ ∏_v ‖u_v‖^{n_v}` as a continuous character of the units of the
mixed space. -/
def mixedNormCharacter : (mixedEmbedding.mixedSpace F)ˣ →ₜ* ℂˣ :=
  ({ toMonoidHom := Units.map ((Complex.ofRealHom.comp NNReal.toRealHom).toMonoidHom)
     continuous_toFun := (Complex.continuous_ofReal.comp NNReal.continuous_coe).units_map _ } :
      ℝ≥0ˣ →ₜ* ℂˣ).comp
    ((IdeleAbsoluteValue.infinite F).comp
      { toMonoidHom :=
          Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom
        continuous_toFun := (continuous_infiniteAdeleCoordinates_symm F).units_map _ })

theorem mixedNormCharacter_map (u : (InfiniteAdeleRing F)ˣ) :
    ((mixedNormCharacter F
        (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.toMonoidHom u) : ℂˣ) :
        ℂ) = ((IdeleAbsoluteValue.infinite F u : ℝ≥0) : ℝ) := by
  have h : Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom
      (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.toMonoidHom u) = u := by
    apply Units.ext
    exact (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm_apply_apply (u : InfiniteAdeleRing F)
  simp only [mixedNormCharacter, ContinuousMonoidHom.comp_toFun]
  change ((((IdeleAbsoluteValue.infinite F)
    (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).symm.toRingHom.toMonoidHom
      (Units.map (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.toMonoidHom u)) : ℝ≥0) :
        ℝ) : ℂ) = _
  rw [h]

/-- Along a coordinate-smooth family of infinite points, the logarithm of the adelic norm of an
algebraic character is smooth. -/
theorem contMDiff_log_characterNorm_ofInfinite {G : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine G.X.left] (χ : AlgebraicCharacter F G)
    {E : Type u} [NormedAddCommGroup E] [NormedSpace ℝ E] {M : Type u} [TopologicalSpace M]
    [ChartedSpace E M] {p : M → InfiniteAdelicGroupPoints F G}
    (hp : G.CoordinateSmooth Ainf (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom 𝓘(ℝ, E) p) :
    ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x => Real.log ((characterNorm F G χ (ofInfinite F G (p x)) : ℝ≥0) : ℝ)) := by
  let c := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let u : M → (InfiniteAdeleRing F)ˣ := fun x => characterUnits F G χ Ainf (p x)
  let w : M → (mixedEmbedding.mixedSpace F)ˣ := fun x => Units.map c.toRingHom.toMonoidHom (u x)
  have hw : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, mixedEmbedding.mixedSpace F) ∞
      (fun x => ((w x : (mixedEmbedding.mixedSpace F)ˣ) : mixedEmbedding.mixedSpace F)) := by
    have h := (hp.postcomp χ.hom.hom) (GroupScheme.Gm.universalUnit (CommRingCat.of F)).val
    refine h.congr fun x => ?_
    change c ((GroupScheme.Gm.affineUnitsEquiv (CommRingCat.of F) Ainf (p x ≫ χ.hom.hom) :
      (InfiniteAdeleRing F)ˣ) : InfiniteAdeleRing F) = _
    rw [GroupScheme.Gm.affineUnitsEquiv_eq_map]
    rfl
  have hnorm : ∀ x, (unitsCharacterExtension (mixedNormCharacter F)
      ((w x : (mixedEmbedding.mixedSpace F)ˣ) : mixedEmbedding.mixedSpace F)) =
      (((characterNorm F G χ (ofInfinite F G (p x)) : ℝ≥0) : ℝ) : ℂ) := by
    intro x
    rw [unitsCharacterExtension_unit, characterNorm_ofInfinite]
    exact mixedNormCharacter_map (u x)
  have hC : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℂ) ∞
      (fun x => (((characterNorm F G χ (ofInfinite F G (p x)) : ℝ≥0) : ℝ) : ℂ)) := by
    intro x
    have hd := (contDiffAt_unitsCharacterExtension (mixedNormCharacter F) (w x)).contMDiffAt
    have hc := hd.comp x (hw x)
    exact hc.congr_of_eventuallyEq (Filter.Eventually.of_forall fun y => (hnorm y).symm)
  have hR : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞
      (fun x => ((characterNorm F G χ (ofInfinite F G (p x)) : ℝ≥0) : ℝ)) := by
    have := Complex.reCLM.contDiff.contMDiff.comp hC
    refine this.congr fun x => ?_
    simp
  intro x
  have hpos : ((characterNorm F G χ (ofInfinite F G (p x)) : ℝ≥0) : ℝ) ≠ 0 := by
    exact_mod_cast (characterNorm F G χ (ofInfinite F G (p x))).ne_zero
  exact (Real.contDiffAt_log.mpr hpos).contMDiffAt.comp x (hR x)

/-- For a morphism `j : G → H` and a complex character parameter `λ` of `H`, the function
`m ↦ j(m)^λ` on `G(F_∞)` is plot-smooth. -/
theorem parameterPower_map_ofInfinite_mem_infinitePlotSmoothFunctions
    {G H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine G.X.left] (j : G ⟶ H)
    (lam : ComplexCharacterParameter F H) :
    (fun m => parameterPower F H lam (map F G H j (ofInfinite F G m))) ∈
      InfinitePlotSmoothFunctions F G := by
  intro E _ _ M _ _ p hp
  induction lam using TensorProduct.inductionOn with
  | tmul s χ =>
    have hlog := contMDiff_log_characterNorm_ofInfinite (j ≫ χ.toMul) hp
    have hexp : ContDiff ℝ ∞ (fun t : ℝ => Complex.exp (s * (t : ℂ))) :=
      Complex.contDiff_exp.comp (contDiff_const.mul Complex.ofRealCLM.contDiff)
    refine (hexp.contMDiff.comp hlog).congr fun x => ?_
    simp only [Function.comp_apply, parameterPower, complexParameterPairing_tmul,
      characterLog_apply]
    rw [characterNorm_comp]
  | add a b ha hb =>
    have hmul : ContDiff ℝ ∞ (fun z : ℂ × ℂ => z.1 * z.2) := contDiff_mul
    refine (hmul.contMDiff.comp (ha.prodMk_space hb)).congr fun x => ?_
    simp only [Function.comp_apply, parameterPower, map_add, LinearMap.add_apply,
      Complex.exp_add]

end Langlands.Global.InfiniteAdelicGroupPoints

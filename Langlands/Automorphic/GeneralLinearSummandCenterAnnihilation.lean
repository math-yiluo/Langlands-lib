import Langlands.Automorphic.GeneralLinearHilbertCenterFinite
import Langlands.Automorphic.GeneralLinearSummandSmoothing
import Langlands.Automorphic.GroupSchemeFullAEL2Integrated

/-! # A common centre annihilator for smoothed classes in an irreducible cuspidal summand -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory Filter
open scoped Classical CategoryTheory.MonObj Topology InnerProductSpace Manifold ContDiff Matrix.Norms.Operator

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 100000
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Automorphic.GroupSchemeFunctions

open Langlands.Global Langlands.Global.AdelicGroupPoints Langlands.Global.PositiveRealTorus
open Langlands.GroupScheme Langlands.Archimedean

private local instance (F : Type u) [Field F] (n : ℕ) :
    IsAffine (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme (Fin n) (CommRingCat.of F)

private local instance (F : Type u) [Field F] (n : ℕ) :
    Smooth (GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)).X.hom :=
  GroupScheme.GeneralLinear.smoothStatement (Fin n) (CommRingCat.of F)

section Summand

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)

local notation "n" => r + 1
local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
local notation "S" => fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)

/-- The archimedean units inclusion into the group-scheme adelic points. -/
def archimedeanUnitsPoint :
    (ArchimedeanMatrix F (r + 1))ˣ →* AdelicGroupPoints F GLs :=
  ((m).symm.toMulEquiv.toMonoidHom).comp ((AdelicGL.ofInfinite F (r + 1)).toMonoidHom.comp
    (archimedeanGLCoordinates F (r + 1)).symm.toMulEquiv.toMonoidHom)

theorem archimedeanUnitsPoint_apply (b : (ArchimedeanMatrix F (r + 1))ˣ) :
    archimedeanUnitsPoint F r b =
      (m).symm (AdelicGL.ofInfinite F (r + 1) ((archimedeanGLCoordinates F (r + 1)).symm b)) :=
  rfl

theorem continuous_archimedeanUnitsPoint : Continuous (archimedeanUnitsPoint F r) :=
  (m).symm.continuous.comp ((AdelicGL.ofInfinite F (r + 1)).continuous.comp
    (archimedeanGLCoordinates F (r + 1)).symm.continuous)

theorem archimedeanUnitsPoint_coordinates (z : InfiniteAdelicGL F (r + 1)) :
    archimedeanUnitsPoint F r (archimedeanGLCoordinates F (r + 1) z) =
      archimedeanAdelicPoint F r z := by
  rw [archimedeanUnitsPoint_apply, ContinuousMulEquiv.symm_apply_apply]
  rfl

theorem adelicGL_mul_ofInfinite (x : AdelicGL F (r + 1)) (a : InfiniteAdelicGL F (r + 1)) :
    x * AdelicGL.ofInfinite F (r + 1) a =
      AdelicGL.ofInfinite F (r + 1) (AdelicGL.infinite F (r + 1) x * a *
        (AdelicGL.infinite F (r + 1) x)⁻¹) * x := by
  apply (AdelicGL.split F (r + 1)).injective
  change (AdelicGL.infinite F (r + 1) _, AdelicGL.finite F (r + 1) _) =
    (AdelicGL.infinite F (r + 1) _, AdelicGL.finite F (r + 1) _)
  simp only [map_mul, AdelicGL.ofInfinite_eq_pair, AdelicGL.infinite_pair, AdelicGL.finite_pair,
    one_mul, mul_one, inv_mul_cancel_right]

/-- Every adelic point normalizes the archimedean subgroup through its archimedean
coordinate. -/
theorem mul_archimedeanUnitsPoint (g : AdelicGroupPoints F GLs)
    (a : (ArchimedeanMatrix F (r + 1))ˣ) :
    g * archimedeanUnitsPoint F r a =
      archimedeanUnitsPoint F r
        (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) (m g)) * a *
          (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) (m g)))⁻¹) * g := by
  apply (m).injective
  rw [map_mul, map_mul, archimedeanUnitsPoint_apply, archimedeanUnitsPoint_apply,
    ContinuousMulEquiv.apply_symm_apply, ContinuousMulEquiv.apply_symm_apply]
  have hcoord : (archimedeanGLCoordinates F (r + 1)).symm
      (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) (m g)) * a *
        (archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) (m g)))⁻¹) =
      AdelicGL.infinite F (r + 1) (m g) * (archimedeanGLCoordinates F (r + 1)).symm a *
        (AdelicGL.infinite F (r + 1) (m g))⁻¹ := by
    rw [map_mul, map_mul, map_inv, ContinuousMulEquiv.symm_apply_apply]
  rw [hcoord]
  exact adelicGL_mul_ofInfinite F r (m g) _

variable [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]

variable (P : Submodule ℂ (fullAEL2CuspidalSubmodule F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) hPD
    (GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))) T i hi I e hc))
  (hPinv : ∀ a, ∀ x ∈ P, fullAEL2CuspidalBoundedRightAction F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)) hPD
    (GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))) T i hi I e hc a x ∈ P)

/-- The subspace `P` of the cuspidal space, viewed in quotient `L²`. -/
abbrev summandSubmodule : Submodule ℂ (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)) :=
  P.map (S).subtype

theorem isClosed_summandSubmodule (hPc : IsClosed (P : Set S)) :
    IsClosed ((summandSubmodule F r hPD T i hi I e hc P : Submodule ℂ
      (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i))) :
        Set (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i))) := by
  rw [Submodule.map_coe]
  exact (fullAEL2CuspidalClosedSubmodule F GLs hPD hG T i hi I e hc).isClosed
    |>.isClosedEmbedding_subtypeVal.isClosedMap _ hPc

include hPinv in
theorem summandSubmodule_invariant (a : AdelicGroupPoints F GLs) (φ) (hφ : φ ∈ summandSubmodule F r hPD T i hi I e hc P) :
    haarQuotientL2BoundedRightAction F GLs T i hi I e hc a φ ∈
      summandSubmodule F r hPD T i hi I e hc P := by
  obtain ⟨x, hx, rfl⟩ := hφ
  exact ⟨πc a x, hPinv a x hx, rfl⟩

/-- The quotient right action preserves the inner product. -/
theorem inner_haarQuotientL2BoundedRightAction (a : AdelicGroupPoints F GLs)
    (x y : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)) :
    inner ℂ (haarQuotientL2BoundedRightAction F GLs T i hi I e hc a x)
      (haarQuotientL2BoundedRightAction F GLs T i hi I e hc a y) = inner ℂ x y := by
  let L : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i) →ₗᵢ[ℂ]
      Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i) :=
    ⟨(haarQuotientL2BoundedRightAction F GLs T i hi I e hc a).toLinearMap,
      norm_haarQuotientL2BoundedRightAction F GLs T i hi I e hc a⟩
  exact L.inner_map_map x y

theorem haarQuotientL2BoundedRightAction_archimedean_isContinuous :
    IsContinuousRepresentation ((haarQuotientL2BoundedRightAction F GLs T i hi I e hc).comp
      (archimedeanUnitsPoint F r)) := by
  unfold IsContinuousRepresentation
  refine ((haarQuotientL2JointRightAction F GLs T i hi I e hc).continuous.comp
    (((continuous_archimedeanUnitsPoint F r).comp continuous_fst).prodMk
      continuous_snd)).congr fun p => ?_
  simp only [Function.comp_apply, MonoidHom.coe_comp, haarQuotientL2JointRightAction_apply,
    haarQuotientL2BoundedRightAction_apply]

theorem haarQuotientL2BoundedRightAction_normalizes (g : AdelicGroupPoints F GLs) :
    ∃ b : (ArchimedeanMatrix F (r + 1))ˣ, ∀ a,
      haarQuotientL2BoundedRightAction F GLs T i hi I e hc g *
          haarQuotientL2BoundedRightAction F GLs T i hi I e hc (archimedeanUnitsPoint F r a) =
        haarQuotientL2BoundedRightAction F GLs T i hi I e hc
            (archimedeanUnitsPoint F r (b * a * b⁻¹)) *
          haarQuotientL2BoundedRightAction F GLs T i hi I e hc g := by
  refine ⟨archimedeanGLCoordinates F (r + 1) (AdelicGL.infinite F (r + 1) (m g)), fun a => ?_⟩
  rw [← map_mul, ← map_mul, mul_archimedeanUnitsPoint]

/-- Minimality of `P` among closed invariant subspaces of the cuspidal space gives minimality
of its image among closed invariant subspaces of quotient `L²`. -/
theorem summandSubmodule_minimal
    (hPmin : ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
      (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P)
    (W : Submodule ℂ (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)))
    (hWle : W ≤ summandSubmodule F r hPD T i hi I e hc P)
    (hWc : IsClosed (W : Set (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i))))
    (hWinv : ∀ g, ∀ x ∈ W, haarQuotientL2BoundedRightAction F GLs T i hi I e hc g x ∈ W) :
    W = ⊥ ∨ W = summandSubmodule F r hPD T i hi I e hc P := by
  let W' : Submodule ℂ S := W.comap (S).subtype
  have hW'le : W' ≤ P := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hWle hx
    rw [← Subtype.ext hyx]
    exact hy
  have hW'c : IsClosed (W' : Set S) := hWc.preimage continuous_subtype_val
  have hW'inv : ∀ a, ∀ x ∈ W', πc a x ∈ W' := fun a x hx => hWinv a x hx
  rcases hPmin W' hW'le hW'c hW'inv with h | h
  · left
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨y, -, rfl⟩ := hWle hw
    have hy : y ∈ W' := hw
    rw [h, Submodule.mem_bot] at hy
    rw [hy, Submodule.mem_bot]
    rfl
  · right
    apply le_antisymm hWle
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ W' := by rw [h]; exact hy
    exact hy'

variable [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  (ν : Measure (InfiniteAdelicGL F (r + 1))) [ν.IsHaarMeasure]

/-- The kernel transported to the archimedean units. -/
def unitsKernel (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1)) :
    (ArchimedeanMatrix F (r + 1))ˣ → ℂ :=
  fun b => κ.val.val ((archimedeanGLCoordinates F (r + 1)).symm b)

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))] in
theorem contMDiff_unitsKernel (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1)) :
    ContMDiff 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) 𝓘(ℝ, ℂ) ∞ (unitsKernel F r κ) :=
  κ.val.property

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))] in
theorem hasCompactSupport_unitsKernel (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1)) :
    HasCompactSupport (unitsKernel F r κ) :=
  κ.property.comp_homeomorph (archimedeanGLCoordinates F (r + 1)).symm.toHomeomorph

omit [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))] in
/-- The smoothing weight at `z` is the transported kernel at the inverse coordinate. -/
theorem smoothingWeight_one_eq (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (z : InfiniteAdelicGL F (r + 1)) :
    smoothingWeight F r 1 κ z = unitsKernel F r κ (archimedeanGLCoordinates F (r + 1) z)⁻¹ := by
  change (ArchimedeanGL.envelopingAction F (r + 1) 1 κ.val).val z⁻¹ =
    κ.val.val ((archimedeanGLCoordinates F (r + 1)).symm (archimedeanGLCoordinates F (r + 1) z)⁻¹)
  rw [map_inv, ContinuousMulEquiv.symm_apply_apply, map_one, Module.End.one_apply]

section Units

variable [MeasurableSpace (ArchimedeanMatrix F (r + 1))ˣ] [BorelSpace (ArchimedeanMatrix F (r + 1))ˣ]

/-- The archimedean Haar measure transported to the units by the coordinate isomorphism. -/
def unitsHaar : Measure (ArchimedeanMatrix F (r + 1))ˣ :=
  ν.map (archimedeanGLCoordinates F (r + 1)).toHomeomorph.toMeasurableEquiv

instance unitsHaar_isHaarMeasure : (unitsHaar F r ν).IsHaarMeasure :=
  ContinuousMulEquiv.isHaarMeasure_map ν (archimedeanGLCoordinates F (r + 1))

omit [ν.IsHaarMeasure] in
/-- The smoothing with the identity element, written as an integral over the units. -/
theorem smoothedClass_one_eq_integral_units (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (u : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)) :
    smoothedClass F r T i ν hi I e hc 1 κ u =
      ∫ g, unitsKernel F r κ g⁻¹ •
        haarQuotientL2BoundedRightAction F GLs T i hi I e hc (archimedeanUnitsPoint F r g) u
          ∂(unitsHaar F r ν) := by
  rw [unitsHaar, integral_map_equiv, smoothedClass]
  congr 1
  funext z
  change smoothingWeight F r 1 κ z • _ = unitsKernel F r κ (archimedeanGLCoordinates F (r + 1) z)⁻¹ •
    haarQuotientL2BoundedRightAction F GLs T i hi I e hc
      (archimedeanUnitsPoint F r (archimedeanGLCoordinates F (r + 1) z)) u
  rw [smoothingWeight_one_eq, archimedeanUnitsPoint_coordinates]

end Units

variable [SecondCountableTopology (InfiniteAdelicGL F (r + 1))]

/-- The derivative of the smoothed classes along real exponential curves, in units coordinates. -/
theorem hasDerivAt_smoothedClass_units (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (u : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i))
    (h : C(PositiveRationalQuotient F GLs T i, ℂ))
    (hrep : (u : PositiveRationalQuotient F GLs T i → ℂ) =ᵐ[positiveRationalQuotientHaarMeasure F GLs T i] h)
    (L : OpenSubgroup (FiniteAdelicGL F (r + 1)))
    (hL : ∀ l : L.toSubgroup, ∀ q, h (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F GLs T i)
      ((m).symm (AdelicGL.ofFinite F (r + 1) l)) q) = h q)
    (X : ArchimedeanGL.RealLieAlgebra F (r + 1)) (a : ArchimedeanGL.EnvelopingAlgebra F (r + 1)) :
    HasDerivAt (fun t : ℝ => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
        (archimedeanUnitsPoint F r (archimedeanGLCoordinates F (r + 1)
          (ArchimedeanGL.realLieExponentialCurve F (r + 1) X t)))
        (smoothedClass F r T i ν hi I e hc a κ u))
      (smoothedClass F r T i ν hi I e hc (ArchimedeanGL.envelopingGenerator F (r + 1)
          (ArchimedeanGL.complexify F (r + 1) X) * a) κ u) 0 := by
  have hfun : (fun t : ℝ => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
        (archimedeanUnitsPoint F r (archimedeanGLCoordinates F (r + 1)
          (ArchimedeanGL.realLieExponentialCurve F (r + 1) X t)))
        (smoothedClass F r T i ν hi I e hc a κ u)) =
      fun t : ℝ => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
        (GeneralLinearFormClassDerivative.exponentialAdelicPoint F r X t)
        (smoothedClass F r T i ν hi I e hc a κ u) := by
    funext t
    rw [archimedeanUnitsPoint_coordinates]
    rfl
  rw [hfun]
  exact hasDerivAt_smoothedClass F r T i ν hi I e hc κ u h hrep L hL X a

end Summand

section Annihilation

variable (F : Type u) [Field F] [NumberField F] (r : ℕ)
  (hPD : ParabolicDynamicStatement.{u})
  (T : CommGroupScheme (Spec (CommRingCat.of F)))
  (i : T.toGrp ⟶ GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F))
  (hi : Function.Injective (characterRestrict i)) [(characterRestrict i).range.FiniteIndex]
  (I : Type u) [Fintype I]
  (e : T.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) (hc : IsCentral i)
  [(Measure.haar : Measure (normOneSubgroup F
    (GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)))).IsMulRightInvariant]
  [MeasurableSpace (InfiniteAdelicGL F (r + 1))] [BorelSpace (InfiniteAdelicGL F (r + 1))]
  (ν : Measure (InfiniteAdelicGL F (r + 1))) [ν.IsHaarMeasure]
  [SecondCountableTopology (InfiniteAdelicGL F (r + 1))]

local notation "GLs" => GroupScheme.GeneralLinear.groupScheme (Fin (r + 1)) (CommRingCat.of F)
local notation "hG" => GroupScheme.isConnectedReductive_generalLinear F (Fin (r + 1))
local notation "S" => fullAEL2CuspidalSubmodule F GLs hPD hG T i hi I e hc
local notation "πc" => fullAEL2CuspidalBoundedRightAction F GLs hPD hG T i hi I e hc
local notation "m" => GeneralLinearGroupPoints.adelicHomeomorph F (r + 1)

/-- The family of smoothed classes of one vector satisfies the hypotheses of the abstract
annihilation theorem. -/
theorem smoothedClass_family_eq_zero
    (A : Submodule ℂ (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)))
    (hAc : IsClosed (A : Set (Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i))))
    (hAinv : ∀ a, ∀ φ ∈ A, haarQuotientL2BoundedRightAction F GLs T i hi I e hc a φ ∈ A)
    [MeasurableSpace (ArchimedeanMatrix F (r + 1))ˣ] [BorelSpace (ArchimedeanMatrix F (r + 1))ˣ]
    (J : Ideal (ArchimedeanGL.EnvelopingCenter F (r + 1)))
    (hJy : ∀ u ∈ A, ∀ κ' : (ArchimedeanMatrix F (r + 1))ˣ → ℂ,
        ContMDiff 𝓘(ℝ, ArchimedeanMatrix F (r + 1)) 𝓘(ℝ, ℂ) ∞ κ' → HasCompactSupport κ' →
        ∀ y : ArchimedeanGL.EnvelopingAlgebra F (r + 1) →
            Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i), (∀ a, y a ∈ A) →
          y 1 = (∫ g, κ' g⁻¹ • haarQuotientL2BoundedRightAction F GLs T i hi I e hc
            (archimedeanUnitsPoint F r g) u ∂(unitsHaar F r ν)) →
          (∀ a b, y (a + b) = y a + y b) → (∀ (c : ℂ) a, y (c • a) = c • y a) →
          (∀ X a, HasDerivAt
            (fun t : ℝ => haarQuotientL2BoundedRightAction F GLs T i hi I e hc
              (archimedeanUnitsPoint F r (archimedeanGLCoordinates F (r + 1)
                (ArchimedeanGL.realLieExponentialCurve F (r + 1) X t))) (y a))
            (y (ArchimedeanGL.envelopingGenerator F (r + 1)
              (ArchimedeanGL.complexify F (r + 1) X) * a)) 0) →
          ∀ z ∈ J, y (ArchimedeanGL.centerInclusion F (r + 1) z) = 0)
    (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
    (u : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)) (hu : u ∈ A)
    (h : C(PositiveRationalQuotient F GLs T i, ℂ))
    (hrep : (u : PositiveRationalQuotient F GLs T i → ℂ) =ᵐ[positiveRationalQuotientHaarMeasure F GLs T i] h)
    (L : OpenSubgroup (FiniteAdelicGL F (r + 1)))
    (hL : ∀ l : L.toSubgroup, ∀ q, h (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F GLs T i)
      ((m).symm (AdelicGL.ofFinite F (r + 1) l)) q) = h q)
    (z : ArchimedeanGL.EnvelopingCenter F (r + 1)) (hz : z ∈ J) :
    smoothedClass F r T i ν hi I e hc (ArchimedeanGL.centerInclusion F (r + 1) z) κ u = 0 :=
  hJy u hu (unitsKernel F r κ) (contMDiff_unitsKernel F r κ) (hasCompactSupport_unitsKernel F r κ)
    (fun a => smoothedClass F r T i ν hi I e hc a κ u)
    (fun a => smoothedClass_mem F r T i ν hi I e hc A hAc hAinv a κ hu
      (integrable_smoothingOrbit F r T i ν hi I e hc a κ u h hrep))
    (smoothedClass_one_eq_integral_units F r T i hi I e hc ν κ u)
    (fun a b => smoothedClass_add F r T i ν hi I e hc a b κ u h hrep)
    (fun c a => smoothedClass_smul F r T i ν hi I e hc c a κ u)
    (fun X a => hasDerivAt_smoothedClass_units F r T i hi I e hc ν κ u h hrep L hL X a) z hz

/-- **A common centre annihilator.** For a nonzero closed invariant subspace `P` of the full
almost-everywhere cuspidal space, minimal among such subspaces, there is an ideal of finite
codimension of the enveloping centre that kills every archimedean smoothing of every vector of
`P` with a continuous representative invariant under an open subgroup of the finite adelic
points. -/
theorem exists_ideal_smoothedClass_eq_zero (P : Submodule ℂ S)
    (hPinv : ∀ a, ∀ x ∈ P, πc a x ∈ P) (hPne : P ≠ ⊥) (hPc : IsClosed (P : Set S))
    (hPmin : ∀ P' : Submodule ℂ S, P' ≤ P → IsClosed (P' : Set S) →
      (∀ a, ∀ x ∈ P', πc a x ∈ P') → P' = ⊥ ∨ P' = P) :
    ∃ J : Ideal (ArchimedeanGL.EnvelopingCenter F (r + 1)),
      Module.Finite ℂ (ArchimedeanGL.EnvelopingCenter F (r + 1) ⧸ J.restrictScalars ℂ) ∧
      ∀ (κ : ArchimedeanGL.SmoothCompactKernel F (r + 1))
        (u : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)),
        u ∈ summandSubmodule F r hPD T i hi I e hc P →
        ∀ (h : C(PositiveRationalQuotient F GLs T i, ℂ)),
          (u : PositiveRationalQuotient F GLs T i → ℂ) =ᵐ[positiveRationalQuotientHaarMeasure F GLs T i] h →
        ∀ L : OpenSubgroup (FiniteAdelicGL F (r + 1)),
          (∀ l : L.toSubgroup, ∀ q, h (LeftCosetSpace.rightTranslate (positiveRationalSubgroup F GLs T i)
            ((m).symm (AdelicGL.ofFinite F (r + 1) l)) q) = h q) →
        ∀ z ∈ J, smoothedClass F r T i ν hi I e hc
          (ArchimedeanGL.centerInclusion F (r + 1) z) κ u = 0 := by
  let : MeasurableSpace (ArchimedeanMatrix F (r + 1))ˣ := borel _
  have : BorelSpace (ArchimedeanMatrix F (r + 1))ˣ := ⟨rfl⟩
  have hAne : summandSubmodule F r hPD T i hi I e hc P ≠ ⊥ := by
    intro hA
    apply hPne
    rw [eq_bot_iff]
    intro x hx
    have hxA : ((x : S) : Lp ℂ 2 (positiveRationalQuotientHaarMeasure F GLs T i)) ∈
        summandSubmodule F r hPD T i hi I e hc P := ⟨x, hx, rfl⟩
    rw [hA, Submodule.mem_bot] at hxA
    rw [Submodule.mem_bot]
    exact Subtype.ext hxA
  obtain ⟨J, hJ, hJy⟩ := ArchimedeanGL.exists_ideal_smoothingFamily_eq_zero F (r + 1)
    (haarQuotientL2BoundedRightAction F GLs T i hi I e hc)
    (archimedeanUnitsPoint F r) (unitsHaar F r ν)
    (haarQuotientL2BoundedRightAction_archimedean_isContinuous F r T i hi I e hc)
    (haarQuotientL2BoundedRightAction_normalizes F r T i hi I e hc)
    (inner_haarQuotientL2BoundedRightAction F r T i hi I e hc)
    (summandSubmodule F r hPD T i hi I e hc P)
    (isClosed_summandSubmodule F r hPD T i hi I e hc P hPc)
    (summandSubmodule_invariant F r hPD T i hi I e hc P hPinv) hAne
    (summandSubmodule_minimal F r hPD T i hi I e hc P hPmin)
  exact ⟨J, hJ, fun κ u hu h hrep L hL z hz =>
    smoothedClass_family_eq_zero F r T i hi I e hc ν _
      (isClosed_summandSubmodule F r hPD T i hi I e hc P hPc)
      (summandSubmodule_invariant F r hPD T i hi I e hc P hPinv) J hJy κ u hu h hrep L hL z hz⟩

end Annihilation

end Langlands.Automorphic.GroupSchemeFunctions

import Langlands.TraceFormula.GeneralLinearRadicalIntegralVanishingStatement
import Langlands.Automorphic.GeneralLinearParabolicCuspidalComparisonProof
import Langlands.Global.AdelicGLInverseTranspose
import Langlands.Analysis.Local.QuotientMeasureExistence

/-! # Adelic radical integral vanishing for `GL_n` -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry NumberField MeasureTheory MeasureTheory.Measure Topology
open scoped CategoryTheory.MonObj

namespace Langlands.TraceFormula

open Langlands.Global Langlands.GroupScheme Langlands.GeneralLinear
open Langlands.Automorphic.GroupSchemeFunctions Langlands.Global.AdelicSubgroupPoints
open Langlands.QuotientIntegration

set_option autoImplicit false

/-- Use the Weil formula along the closed image of an additive group. -/
private theorem integral_eq_zero_of_additive_averages
    {G A : Type u} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [MeasurableSpace G] [BorelSpace G]
    [AddCommGroup A] [TopologicalSpace A] [IsTopologicalAddGroup A] [MeasurableSpace A] [BorelSpace A]
    (incl : Multiplicative A →* G) (hincl : IsClosedEmbedding incl)
    (ambientHaar : Measure G) [ambientHaar.IsHaarMeasure] [ambientHaar.IsMulRightInvariant]
    (φ : G → ℂ) (hφ : Continuous φ) (hφc : HasCompactSupport φ)
    (hzero : ∀ (ν : Measure A), ν.IsAddHaarMeasure → ∀ g : G,
      (∫ a, φ (incl (Multiplicative.ofAdd a) * g) ∂ν) = 0) :
    (∫ g, φ g ∂ambientHaar) = 0 := by
  let H := incl.range
  have hH : IsClosed (H : Set G) := hincl.isClosed_range
  let : LocallyCompactSpace H := hH.locallyCompactSpace
  let : MeasurableSpace H := borel H
  let : BorelSpace H := ⟨rfl⟩
  let : MeasurableSpace (Multiplicative A) := ‹MeasurableSpace A›
  let : BorelSpace (Multiplicative A) := ‹BorelSpace A›
  let e₀ : Multiplicative A ≃* H := MonoidHom.ofInjective hincl.injective
  let eTop := e₀.toEquiv.toHomeomorphOfIsInducing
    (hincl.isEmbedding.codRestrict (H : Set G) fun a => ⟨a, rfl⟩).isInducing
  let e : Multiplicative A ≃ₜ* H :=
    { toMulEquiv := e₀
      continuous_toFun := eTop.continuous
      continuous_invFun := eTop.symm.continuous }
  let subgroupHaar : Measure H := Measure.haar
  let : subgroupHaar.IsMulRightInvariant := ⟨fun h => by
    have hcomm : (· * h) = (h * ·) := by
      funext k
      apply e.symm.injective
      simp only [map_mul, mul_comm]
    rw [hcomm, map_mul_left_eq_self]⟩
  let νmul : Measure (Multiplicative A) := Measure.map e.symm subgroupHaar
  let : νmul.IsHaarMeasure := e.symm.toMulEquiv.isHaarMeasure_map subgroupHaar
    e.symm.continuous e.continuous
  let ν : Measure A := νmul
  have hν : ν.IsAddHaarMeasure :=
    { toIsFiniteMeasureOnCompacts := (inferInstance : IsFiniteMeasureOnCompacts νmul)
      toIsOpenPosMeasure := (inferInstance : νmul.IsOpenPosMeasure)
      map_add_left_eq_self := fun a => map_mul_left_eq_self νmul (Multiplicative.ofAdd a) }
  let : MeasurableSpace (LeftQuotient H) := borel _
  let : BorelSpace (LeftQuotient H) := ⟨rfl⟩
  obtain ⟨quotientMeasure, hQuotient⟩ := compatibleMeasureExists H hH ambientHaar subgroupHaar
  have hq (q : LeftQuotient H) : quotientAverage H subgroupHaar φ q = 0 := by
    induction q using Quotient.inductionOn with
    | h g =>
      rw [quotientAverage_mk]
      have hchange := integral_map_equiv («μ» := subgroupHaar)
        e.symm.toHomeomorph.toMeasurableEquiv (fun a : Multiplicative A => φ (incl a * g))
      change (∫ a : Multiplicative A, φ (incl a * g) ∂νmul) =
        ∫ z : H, φ (incl ((MonoidHom.ofInjective hincl.injective).symm z) * g) ∂subgroupHaar at hchange
      simp only [MonoidHom.apply_ofInjective_symm] at hchange
      exact hchange.symm.trans (hzero ν hν g)
  simpa only [hq, integral_zero] using (hQuotient.integral_formula φ hφ hφc).symm

section LocalBlock

variable (F : Type u) [Field F] [NumberField F] {a b n : ℕ}
  (v : Langlands.Global.FinitePlace F) (h : a + b = n)

local notation "RF" => CommRingCat.of F
local notation "GLG" => GroupScheme.GeneralLinear.groupScheme (Fin n) RF
local notation "A" => CommAlgCat.of F (AdeleRing (𝓞 F) F)
local notation "M" => Matrix (Fin a) (Fin b) (FiniteCompletion F v)

local instance localBlockIsAffine : IsAffine (GLG).X.left :=
  GroupScheme.GeneralLinear.isAffine_groupScheme _ _

private def localBlock : Multiplicative M →ₜ* AdelicGL F n where
  toFun Z := AdelicGL.ofFinite F n
    (FiniteAdelicGL.localInclusion F n v (blockUnipotent h Z.toAdd))
  map_one' := by
    change AdelicGL.ofFinite F n
      (FiniteAdelicGL.localInclusion F n v (blockUnipotent h (0 : M))) = 1
    rw [blockUnipotent_zero, map_one, map_one]
  map_mul' Z W := by
    change AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v
      (blockUnipotent h (Z.toAdd + W.toAdd))) = _
    simp only [blockUnipotent_add, map_mul]
  continuous_toFun := (AdelicGL.ofFinite F n).continuous.comp
    ((FiniteAdelicGL.localInclusion F n v).continuous.comp
      ((continuous_blockUnipotent h).comp continuous_toAdd))

private theorem isClosedEmbedding_localBlock : IsClosedEmbedding (localBlock F v h) := by
  let r : AdelicGL F n → Multiplicative M := fun g => Multiplicative.ofAdd
    (blockUnipotentCoordinates h (FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n g)))
  have hr : Continuous r := continuous_ofAdd.comp
    ((continuous_blockUnipotentCoordinates h).comp
      ((FiniteAdelicGL.localProjection F n v).continuous.comp (AdelicGL.finite F n).continuous))
  have hleft : Function.LeftInverse r (localBlock F v h) := by
    intro Z
    change Multiplicative.ofAdd (blockUnipotentCoordinates h
      (FiniteAdelicGL.localProjection F n v (AdelicGL.finite F n (AdelicGL.ofFinite F n
        (FiniteAdelicGL.localInclusion F n v (blockUnipotent h Z.toAdd)))))) = Z
    rw [AdelicGL.finite_ofFinite, FiniteAdelicGL.localProjection_localInclusion,
      blockUnipotentCoordinates_blockUnipotent]
    rfl
  let : T2Space (AdelicGL F n) :=
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm.toHomeomorph.isEmbedding.t2Space
  exact hleft.isClosedEmbedding hr (localBlock F v h).continuous

private theorem localBlock_mem (Z : Multiplicative M) :
    (GeneralLinearGroupPoints.adelicHomeomorph F n).symm (localBlock F v h Z) ∈
      adelicPoints F GLG (GroupScheme.GeneralLinear.blockUnipotent (Fin n) RF
        (twoBlockWeight h)) := by
  apply (GroupScheme.GeneralLinear.mem_blockUnipotent_affinePoints_iff RF A _ _).2
  have hmatrix : GroupScheme.GeneralLinear.affinePointsEquiv (Fin n) RF A
      ((GeneralLinearGroupPoints.adelicHomeomorph F n).symm (localBlock F v h Z)) =
      localBlock F v h Z :=
    (GeneralLinearGroupPoints.adelicHomeomorph F n).apply_symm_apply _
  rw [hmatrix]
  intro i j hij
  change localBlock F v h Z i j = (1 : AdelicGL F n) i j
  apply Prod.ext
  · change AdelicGL.infinite F n (AdelicGL.ofFinite F n
        (FiniteAdelicGL.localInclusion F n v (blockUnipotent h Z.toAdd))) i j =
      AdelicGL.infinite F n 1 i j
    rw [AdelicGL.infinite_ofFinite, map_one]
  · apply IsDedekindDomain.FiniteAdeleRing.ext
    intro w
    change FiniteAdelicGL.localProjection F n w (AdelicGL.finite F n
        (AdelicGL.ofFinite F n (FiniteAdelicGL.localInclusion F n v
          (blockUnipotent h Z.toAdd)))) i j =
      FiniteAdelicGL.localProjection F n w (AdelicGL.finite F n 1) i j
    rw [AdelicGL.finite_ofFinite, map_one, map_one]
    by_cases hw : w = v
    · subst w
      rw [FiniteAdelicGL.localProjection_localInclusion]
      exact blockUnipotent_mem h Z.toAdd i j hij
    · rw [FiniteAdelicGL.localProjection_localInclusion_of_ne F n v w hw]

end LocalBlock

section Radical

private theorem conj_inv_mem_adelicPoints_comap
    {F : Type u} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))}
    (g : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    {U : SubgroupFunctor G} {z : AdelicGroupPoints F G}
    (hz : z ∈ adelicPoints F G U) :
    MulAut.conj (innerAdelicPoint F G g)⁻¹ z ∈ adelicPoints F G (U.comap (G.innerIso g).hom) := by
  change G.affinePointsTarget (G.innerIso g).hom (CommAlgCat.of F (AdeleRing (𝓞 F) F)) _ ∈
    adelicPoints F G U
  rw [affinePointsTarget_innerIso_hom, MulAut.conj_apply, inv_inv]
  simpa only [mul_assoc, mul_inv_cancel, mul_one, mul_inv_cancel_left] using hz

set_option maxHeartbeats 1200000 in
/-- Local two-block vanishing implies adelic vanishing along every proper parabolic radical. -/
theorem generalLinearRadicalIntegralVanishing :
    GeneralLinearRadicalIntegralVanishingStatement.{u} := by
  classical
  intro F _ _ n hPD hG v f hf hfc hlocal P x y
  let GLG := GroupScheme.GeneralLinear.groupScheme (Fin n) (CommRingCat.of F)
  let : IsAffine GLG.X.left := GroupScheme.GeneralLinear.isAffine_groupScheme _ _
  let : Smooth GLG.X.hom := GroupScheme.GeneralLinear.smoothStatement _ _
  let U := properRationalParabolicRadicals hPD hG P
  let N := adelicPoints F GLG U
  have hN : IsClosed (N : Set (AdelicGroupPoints F GLG)) :=
    isClosed_properRationalParabolicRadicalAdelicPoints F GLG hPD hG P
  let : LocallyCompactSpace N := hN.locallyCompactSpace
  let : (Measure.haar : Measure N).IsMulRightInvariant :=
    haar_isMulRightInvariant_of_compactRationalQuotient F GLG U
  obtain ⟨g, e, ⟨i, j, hij⟩, hU⟩ := exists_properRationalParabolicRadicals_eq_comap hPD hG P
  obtain ⟨a, b, h, τ, ha, hb, hτ⟩ :=
    GroupScheme.GeneralLinear.exists_perm_thresholdWeight_eq_twoBlockWeight e (e i)
  let p := innerAdelicPoint F GLG (GroupScheme.GeneralLinear.permPoint (CommRingCat.of F) τ.symm)
  let q := innerAdelicPoint F GLG g
  let k := p * q
  let E := GeneralLinearGroupPoints.adelicHomeomorph F n
  let M := Matrix (Fin a) (Fin b) (FiniteCompletion F v)
  let embedding : Multiplicative M →* AdelicGroupPoints F GLG :=
    (E.symm.toMonoidHom).comp (localBlock F v h).toMonoidHom
  let ambient := (MulAut.conj k⁻¹).toMonoidHom.comp embedding
  have hmem (Z : Multiplicative M) : ambient Z ∈ N := by
    have hthr := GroupScheme.GeneralLinear.blockUnipotent_eq_comap_innerIso_permPoint
      (R := CommRingCat.of F) hτ
    have hw : ∀ s t, e s ≤ e t →
        GroupScheme.GeneralLinear.thresholdWeight e (e i) s ≤
          GroupScheme.GeneralLinear.thresholdWeight e (e i) t :=
      fun _ _ hst => GroupScheme.GeneralLinear.thresholdWeight_le_of_le e (e i) hst
    have ht : MulAut.conj p⁻¹ (embedding Z) ∈ adelicPoints F GLG
        (GroupScheme.GeneralLinear.blockUnipotent (Fin n) (CommRingCat.of F)
          (GroupScheme.GeneralLinear.thresholdWeight e (e i))) := by
      rw [hthr]
      exact conj_inv_mem_adelicPoints_comap _ (localBlock_mem F v h Z)
    have he := GroupScheme.GeneralLinear.blockUnipotent_le_of_le (CommRingCat.of F) hw _ ht
    change MulAut.conj (p * q)⁻¹ (embedding Z) ∈ adelicPoints F GLG U
    rw [mul_inv_rev, map_mul, MulAut.mul_apply, show U = _ from hU]
    exact conj_inv_mem_adelicPoints_comap g he
  let incl := ambient.codRestrict N hmem
  have hincl : IsClosedEmbedding incl := by
    let c := (Homeomorph.mulLeft k⁻¹).trans (Homeomorph.mulRight (k⁻¹)⁻¹)
    have hc : IsClosedEmbedding (c ∘ E.symm ∘ localBlock F v h) :=
      c.isClosedEmbedding.comp
        (E.symm.toHomeomorph.isClosedEmbedding.comp (isClosedEmbedding_localBlock F v h))
    exact IsClosedEmbedding.of_comp IsEmbedding.subtypeVal hc
  let φ : N → ℂ := fun m => f (E (x * m.val * y))
  let T := (Homeomorph.mulLeft x).trans (Homeomorph.mulRight y)
  have htrans : IsClosedEmbedding (E ∘ T ∘ (Subtype.val : N → AdelicGroupPoints F GLG)) :=
    E.toHomeomorph.isClosedEmbedding.comp
      (T.isClosedEmbedding.comp hN.isClosedEmbedding_subtypeVal)
  let : MeasurableSpace M := borel M
  let : BorelSpace M := ⟨rfl⟩
  have hzero : (∫ m, φ m ∂(Measure.haar : Measure N)) = 0 := by
    apply integral_eq_zero_of_additive_averages incl hincl Measure.haar φ
      (hf.comp htrans.continuous) (hfc.comp_isClosedEmbedding htrans)
    intro ν hν t
    refine (integral_congr_ae (Filter.Eventually.of_forall fun Z => ?_)).trans
      (hlocal a b h (ha.mpr ⟨j, hij⟩) (hb.mpr ⟨i, le_rfl⟩) ν hν
        (E x * (E k)⁻¹) (E k * E t.val * E y))
    change f (E (x * (MulAut.conj k⁻¹ (E.symm (localBlock F v h (Multiplicative.ofAdd Z))) *
      t.val) * y)) = _
    rw [MulAut.conj_apply, inv_inv]
    simp only [map_mul, map_inv, E.apply_symm_apply, mul_assoc]
    rfl
  change (∫ m, φ m ∂properParabolicHaarMeasure F GLG hPD hG P) = 0
  rw [properParabolicHaarMeasure, normalizedHaarMeasure, integral_smul_measure, hzero, smul_zero]

end Radical

end Langlands.TraceFormula

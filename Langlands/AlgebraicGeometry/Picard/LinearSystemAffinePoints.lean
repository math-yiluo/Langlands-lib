import Langlands.AlgebraicGeometry.Picard.LinearSystemAffineDivisor
import Langlands.AlgebraicGeometry.Picard.RelativeEffectiveDivisorBaseChangeProof
import Langlands.AlgebraicGeometry.Picard.PicardHilbertPiecesRepresentabilityReductionDivisors

/-! # The universal divisor at the points given by line quotients

For `v : Q → B` whose values generate the unit ideal, the pullback of the universal divisor along
the corresponding `B`-point of the Grassmannian is the zero locus of the section `σ_v`.
Conversely, if the zero locus of `σ_v` is a relative effective Cartier divisor, then the values
of `v` generate the unit ideal (the fibres are nonempty). -/

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false

noncomputable section

namespace Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

open scoped TensorProduct
open Scheme.TwoAffineOpenCover SectionZeroIdeal
open Langlands.RingTheory.Grassmannian.LineQuotientCoordinates
open Module.Grassmannian.ProjectiveEmbedding (Rep InChart)

section Empty

/-- **The zero ideal sheaf is effective Cartier only on the empty scheme.** -/
lemma isEmpty_of_isEffectiveCartierIdeal_bot {X : Scheme.{u}}
    (h : IsEffectiveCartierIdeal (⊥ : X.IdealSheafData)) : IsEmpty X := by
  refine ⟨fun x => ?_⟩
  let L : LineBundle X :=
    ⟨StructureKernelModule.kernelModule (⊥ : X.IdealSheafData).subschemeι, h⟩
  obtain ⟨U, hxU, t, ht⟩ := exists_affine_frame L x
  have h0 : ∀ y ∈ RingHom.ker ((⊥ : X.IdealSheafData).subschemeι.app U.1).hom, y = 0 := by
    intro y hy
    rw [Scheme.IdealSheafData.ker_subschemeι_app, Scheme.IdealSheafData.ideal_bot, Pi.bot_apply,
      Ideal.mem_bot] at hy
    exact hy
  have hsub : ∀ a : Γ(L.obj, U.1), a = 0 := fun a => Subtype.ext (h0 a.val a.property)
  have : Nonempty U.1 := ⟨⟨x, hxU⟩⟩
  have h1 : (frameEquiv ht).symm 1 = (frameEquiv ht).symm 0 := by
    rw [hsub ((frameEquiv ht).symm 1), hsub ((frameEquiv ht).symm 0)]
  exact one_ne_zero ((frameEquiv ht).symm.injective h1)

end Empty

section Points

variable {R : Type u} [CommRing R] {X : Scheme.{u}} {π : X ⟶ Spec (.of R)} {L : LineBundle X}
  {𝒰 : X.OrderedAffineCover} (e : ∀ i, Γ(L.obj, 𝒰.U i))
  (he : ∀ i, Scheme.Modules.IsFrameOn (e i) (𝒰.U i)) (C : CechRep π L.obj 𝒰)
  (D : Rep R C.Q 1)

lemma span_range_comp {B B' : Type u} [CommRing B] [Algebra R B] [CommRing B'] [Algebra R B']
    (φ : B →ₐ[R] B') (v : C.Q →ₗ[R] B) (hv : Ideal.span (Set.range v) = ⊤) :
    Ideal.span (Set.range (φ.toLinearMap ∘ₗ v)) = ⊤ := by
  have h := congrArg (Ideal.map φ) hv
  rw [Ideal.map_span, Ideal.map_top, ← Set.range_comp] at h
  exact h

lemma ptOf_pt {B : Type u} [CommRing B] [Algebra R B]
    (N : Module.Grassmannian B (B ⊗[R] C.Q) 1) :
    LinSys.ptOf D (D.pt B N).1 (D.pt B N).2 = N :=
  (D.pt B).symm_apply_apply N

/-- The chart coordinates of the point given by a line quotient are a unit multiple of `v`. -/
lemma vOf_linePt {B : Type u} [CommRing B] [Algebra R B] (v : C.Q →ₗ[R] B)
    (hv : Ideal.span (Set.range v) = ⊤)
    (hP : LinSys.InSomeChart D (D.pt B (linePt v hv)).1) :
    ∃ c : B, IsUnit c ∧ LinSys.vOf D _ (D.pt B (linePt v hv)).2 hP = c • v := by
  have hpo := ptOf_pt C D (linePt v hv)
  have h₁ := LinSys.inChart_ptOf D _ (D.pt B (linePt v hv)).2 hP.choose hP.choose_spec
  have h₂ : InChart (fun _ => hP.choose) (linePt v hv) := by
    have h₃ := h₁
    rw [hpo] at h₃
    exact h₃
  have hu := isUnit_of_inChart_linePt v hv hP.choose h₂
  exact ⟨_, (Units.isUnit _), (LinSys.coord_congr hP.choose hpo h₁ h₂).trans
    (coord_linePt v hv hP.choose hu h₂)⟩

set_option maxHeartbeats 1000000 in
include he in
/-- **The universal divisor at the point given by a line quotient.** -/
theorem comap_ptMap_linePt {W : (pullback π D.p).IdealSheafData}
    (hW : ∀ {B : Type u} [CommRing B] [Algebra R B] (k : Spec (.of B) ⟶ D.Gr)
      (hk : k ≫ D.p = specMap R B) (hP : LinSys.InSomeChart D k),
      W.comap (ptMap π D.p k hk) = LinSys.FOf L D k hk hP)
    {B : Type u} [CommRing B] [Algebra R B] (v : C.Q →ₗ[R] B)
    (hv : Ideal.span (Set.range v) = ⊤) :
    W.comap (ptMap π D.p (D.pt B (linePt v hv)).1 (D.pt B (linePt v hv)).2) =
      zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v) := by
  let loc : ∀ x : C.Q, B →ₐ[R] Localization.Away (v x) :=
    fun x => IsScalarTower.toAlgHom R B (Localization.Away (v x))
  have hopen : ∀ x : C.Q, IsOpenImmersion (bcMap (π := π) _ (loc x)) := by
    intro x
    unfold bcMap
    have : IsOpenImmersion (Spec.map (CommRingCat.ofHom (loc x).toRingHom)) :=
      inferInstanceAs (IsOpenImmersion
        (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (v x))))))
    infer_instance
  refine Langlands.AlgebraicGeometry.IdealSheafGluing.eq_of_comap_eq'
    (fun x : C.Q => bcMap (π := π) _ (loc x)) ?_ fun x => ?_
  · intro y
    let P := (pullback.snd π (specMap R B)).base y
    obtain ⟨x, hx⟩ : ∃ x : C.Q, v x ∉ P.asIdeal := by
      by_contra hcon
      push Not at hcon
      have hle : Ideal.span (Set.range v) ≤ P.asIdeal := by
        rw [Ideal.span_le]
        rintro _ ⟨q, rfl⟩
        exact hcon q
      rw [hv] at hle
      exact P.isPrime.ne_top (top_le_iff.mp hle)
    refine ⟨x, ?_⟩
    rw [bcMap, Scheme.Pullback.range_map]
    refine ⟨by simp, ?_⟩
    change P ∈ Set.range (Spec.map (CommRingCat.ofHom (algebraMap B (Localization.Away (v x)))))
    rw [← Scheme.Hom.coe_opensRange]
    erw [Scheme.Hom.opensRange_localizationAway (R := CommRingCat.of B) (v x)]
    exact hx
  · have hv' := span_range_comp (C := C) (loc x) v hv
    have hunit : IsUnit (((loc x).toLinearMap ∘ₗ v) x) :=
      IsLocalization.Away.algebraMap_isUnit (v x)
    have hpt : Spec.map (CommRingCat.ofHom (loc x).toRingHom) ≫ (D.pt B (linePt v hv)).1 =
        (D.pt _ (linePt _ hv')).1 := by
      rw [← D.hpt, map_linePt]
    have hN := linePt_inChart _ hv' x hunit
    have hP : LinSys.InSomeChart D
        (D.pt (Localization.Away (v x)) (linePt ((loc x).toLinearMap ∘ₗ v) hv')).1 :=
      ⟨x, (D.hVchart (fun _ => x) _ _).2 hN⟩
    obtain ⟨c, hcu, hc⟩ := vOf_linePt C D ((loc x).toLinearMap ∘ₗ v) hv' hP
    have h1 : W.comap (ptMap π D.p
        (D.pt (Localization.Away (v x)) (linePt ((loc x).toLinearMap ∘ₗ v) hv')).1
        (D.pt (Localization.Away (v x)) (linePt ((loc x).toLinearMap ∘ₗ v) hv')).2) =
        zeroIdeal (pbLB (pullback.fst π (specMap R (Localization.Away (v x)))) L)
          (C.homEquivSections (Localization.Away (v x)) (c • ((loc x).toLinearMap ∘ₗ v))) := by
      rw [← hc]
      exact hW _ _ hP
    rw [← Scheme.IdealSheafData.comap_comp, bcMap_ptMap,
      ptMap_congr π D.p hpt _ (D.pt _ (linePt _ hv')).2, h1,
      zeroIdeal_homEquivSections_smul e he C _ hcu,
      zeroIdeal_comap_homEquivSections e he C _ (loc x) (bcMap_fst _ _) (bcMap_snd _ _) v]

variable {B : Type u} [CommRing B] [Algebra R B]

include he in
/-- A relative effective zero locus of `σ_v` cannot contain a whole fibre: `v` does not vanish
at any field point. -/
lemma false_of_isRelativeEffective_of_comp_eq_zero [GeometricallyIntegral π] (v : C.Q →ₗ[R] B)
    (hE : IsRelativeEffectiveCartierIdeal (pullback.snd π (specMap R B))
      (zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v)))
    (K : Type u) [Field K] [Algebra R K] (φ : B →ₐ[R] K) (hφv : φ.toLinearMap ∘ₗ v = 0) :
    False := by
  have hcomap := zeroIdeal_comap_homEquivSections e he C (bcMap (π := π) K φ) φ
    (bcMap_fst _ _) (bcMap_snd _ _) v
  rw [hφv, homEquivSections_zero, zeroIdeal_zero] at hcomap
  obtain ⟨hJ, -⟩ := PicardHilbertPiecesReduction.divBC π
    RelativeEffectiveDivisorBaseChangeProof.relativeEffectiveDivisorBaseChange
    (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_comp φ) _ hE
  have hbot : (zeroIdeal (pbLB (pullback.fst π (specMap R B)) L)
      (C.homEquivSections B v)).comap (PicardHilbertPiecesReduction.mapX π
        (Spec.map (CommRingCat.ofHom φ.toRingHom)) (specMap_comp φ)) = ⊥ := hcomap
  rw [hbot] at hJ
  have hint : IsIntegral (pullback π (specMap R K)) :=
    GeometricallyIntegral.geometrically_isIntegral (f := π) (specMap R K) (pullback.fst _ _)
      (pullback.snd _ _) (IsPullback.of_hasPullback _ _)
  have hE := isEmpty_of_isEffectiveCartierIdeal_bot hJ.1
  exact hE.false (Classical.arbitrary _)

include he in
/-- **If the zero locus of `σ_v` is relative effective Cartier, the values of `v` generate the unit
ideal**, the fibres of a geometrically integral morphism being nonempty. -/
theorem span_range_of_isRelativeEffective [GeometricallyIntegral π] (v : C.Q →ₗ[R] B)
    (hE : IsRelativeEffectiveCartierIdeal (pullback.snd π (specMap R B))
      (zeroIdeal (pbLB (pullback.fst π (specMap R B)) L) (C.homEquivSections B v))) :
    Ideal.span (Set.range v) = ⊤ := by
  by_contra hne
  obtain ⟨m, hm, hle⟩ := Ideal.exists_le_maximal _ hne
  refine false_of_isRelativeEffective_of_comp_eq_zero e he C v hE m.ResidueField
    (IsScalarTower.toAlgHom R B m.ResidueField) (LinearMap.ext fun q => ?_)
  change algebraMap B m.ResidueField (v q) = 0
  rw [Ideal.algebraMap_residueField_eq_zero]
  exact hle (Ideal.subset_span ⟨q, rfl⟩)

end Points

end Langlands.AlgebraicGeometry.Picard.LinearSystemCechModule

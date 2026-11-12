import Langlands.Global.AdelicSpreadNonseparatedPullbackStatement
import Langlands.Global.AdelicSpreadAffineTopologyProof
import Langlands.Global.AdelicFixedModelFunctorialityProof
import Langlands.Global.AdelicPunctureEmbeddingProof
import Langlands.AlgebraicGeometry.AlgebraicSpace.HenselianIntegralPointsNotClosedFiniteTypeProof

/-! # The doubled-origin counterexample to adelic fibre products over a nonseparated base -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits Topology Polynomial
open _root_.AlgebraicGeometry

set_option maxHeartbeats 800000
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global

open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.AlgebraicSpace

/-- If natural point homeomorphisms carry a pullback comparison to a homeomorphism for the image
cone, the original comparison is a homeomorphism. -/
private theorem isHomeomorph_of_imagePullbackPointComparison
    (C B A : Type u) [CommRing C] [CommRing B] [CommRing A]
    [Algebra C A] [Algebra B A]
    (G : Over (Spec (CommRingCat.of C)) ⥤ Over (Spec (CommRingCat.of B)))
    (τ : ∀ W : Over (Spec (CommRingCat.of C)), TopologicalSpace (RingPoint C W A))
    (σ : ∀ W : Over (Spec (CommRingCat.of C)),
      TopologicalSpace (RingPoint B (G.obj W) A))
    (e : ∀ W, @Homeomorph (RingPoint C W A) (RingPoint B (G.obj W) A) (τ W) (σ W))
    (he : ∀ {V W} (h : V ⟶ W) (p : RingPoint C V A), e W (p ≫ h) = e V p ≫ G.map h)
    {X Y Z : Over (Spec (CommRingCat.of C))}
    {f : X ⟶ Z} {g : Y ⟶ Z} (c : PullbackCone f g)
    (hl : letI := σ X
      letI := σ Y
      @IsHomeomorph (RingPoint B (G.obj c.pt) A)
        {q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A //
          q.1 ≫ G.map f = q.2 ≫ G.map g}
        (σ c.pt) inferInstance (affineSchemePullbackPointComparison B A (c.map G))) :
    letI := τ X
    letI := τ Y
    @IsHomeomorph (RingPoint C c.pt A)
      {q : RingPoint C X A × RingPoint C Y A // q.1 ≫ f = q.2 ≫ g}
      (τ c.pt) inferInstance (affineSchemePullbackPointComparison C A c) := by
  let := τ X
  let := τ Y
  let := τ c.pt
  let := σ X
  let := σ Y
  let := σ c.pt
  let E := ((e X).prodCongr (e Y)).subtype
    (p := fun q : RingPoint C X A × RingPoint C Y A => q.1 ≫ f = q.2 ≫ g)
    (q := fun q : RingPoint B (G.obj X) A × RingPoint B (G.obj Y) A =>
      q.1 ≫ G.map f = q.2 ≫ G.map g)
    (fun q => by
      change q.1 ≫ f = q.2 ≫ g ↔ e X q.1 ≫ G.map f = e Y q.2 ≫ G.map g
      rw [← he, ← he]
      exact (e Z).injective.eq_iff.symm)
  let H := IsHomeomorph.homeomorph _ hl
  have hfun : (⇑(((e c.pt).trans H).trans E.symm)) =
      affineSchemePullbackPointComparison C A c := by
    funext p
    apply E.injective
    rw [Homeomorph.trans_apply, Homeomorph.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · change e c.pt p ≫ G.map c.fst = e X (p ≫ c.fst)
      rw [he]
    · change e c.pt p ≫ G.map c.snd = e Y (p ≫ c.snd)
      rw [he]
  rw [← hfun]
  exact (((e c.pt).trans H).trans E.symm).isHomeomorph

section Core

variable (R A : Type u) [CommRing R] [CommRing A] [Algebra R A]
  [TopologicalSpace A] [IsTopologicalRing A]

/-- The point of the affine line with coordinate `a`. -/
abbrev linePoint (a : A) : RingPoint R (ringTest R R[X]) A :=
  HenselianIntegralPointsNotClosed.linePoint R a

/-- The coordinate of a point of the affine line. -/
def lineCoord (q : RingPoint R (ringTest R R[X]) A) : A :=
  affineRingPointEquiv R R[X] A q X

omit [IsTopologicalRing A] in
private theorem spectrumAlgebraPointHomeomorph_linePoint (a : A) (P : R[X]) :
    spectrumAlgebraPointHomeomorph R A R[X] (linePoint R A a) P = aeval a P := by
  rw [spectrumAlgebraPointHomeomorph_apply]
  change affineRingPointEquiv R R[X] A (ringTestMap R (aeval a)) P = aeval a P
  rw [HenselianIntegralPointsNotClosed.affineRingPointEquiv_ringTestMap]

theorem continuous_linePoint : Continuous (linePoint R A) := by
  rw [← (spectrumAlgebraPointHomeomorph R A R[X]).comp_continuous_iff, AlgPoint.continuous_iff]
  intro P
  simp only [Function.comp_apply, spectrumAlgebraPointHomeomorph_linePoint]
  exact P.continuous_aeval

omit [IsTopologicalRing A] in
theorem continuous_lineCoord : Continuous (lineCoord R A) :=
  (AlgPoint.continuous_eval X).comp (spectrumAlgebraPointHomeomorph R A R[X]).continuous

/-- The core counterexample: for any functorial topologies on points that are the affine
topology on the affine line, the comparison for a cone over the two charts of the doubled-origin
line is not a homeomorphism, as soon as `Aˣ → A` is not a topological embedding. -/
theorem doubledOrigin_pullbackComparison_not_isHomeomorph
    (hA : ¬ IsEmbedding (Units.val : Aˣ → A))
    (τ : ∀ W : Over (Spec (CommRingCat.of R)), TopologicalSpace (RingPoint R W A))
    (hτ : ∀ {V W : Over (Spec (CommRingCat.of R))} (h : V ⟶ W),
      Continuous[τ V, τ W] (fun p : RingPoint R V A => p ≫ h))
    (hlp : Continuous[_, τ (ringTest R R[X])] (linePoint R A))
    (hlc : Continuous[τ (ringTest R R[X]), _] (lineCoord R A))
    (c : PullbackCone (doubledOriginChart R true) (doubledOriginChart R false)) :
    letI := τ (ringTest R R[X])
    ¬ @IsHomeomorph (RingPoint R c.pt A)
      {q : RingPoint R (ringTest R R[X]) A × RingPoint R (ringTest R R[X]) A //
        q.1 ≫ doubledOriginChart R true = q.2 ≫ doubledOriginChart R false}
      (τ c.pt) inferInstance (affineSchemePullbackPointComparison R A c) := by
  let tL : TopologicalSpace (RingPoint R (ringTest R R[X]) A) := τ (ringTest R R[X])
  intro hΦ
  apply hA
  suffices hcont : Continuous[TopologicalSpace.induced Units.val inferInstance, _]
      (fun u : Aˣ => ((u⁻¹ : Aˣ) : A)) by
    refine ⟨⟨?_⟩, Units.val_injective⟩
    rw [Units.topology_eq_inf, inf_eq_left, ← continuous_iff_le_induced]
    exact hcont
  -- The first leg factors through the common open of the two charts.
  have hcond : c.fst.left ≫ DoubledPointLine.ι R 1 ⟨true⟩ =
      c.snd.left ≫ DoubledPointLine.ι R 1 ⟨false⟩ :=
    congrArg (fun φ => φ.left) c.condition
  obtain ⟨w₀, hw₀, -⟩ := Langlands.AlgebraicGeometry.CommonOpenGluing.exists_of_comp_eq _ _ (DoubledPointLine.g R 1)
    (i := ⟨true⟩) (j := ⟨false⟩) (by simp) _ _ hcond
  have hw₀' : w₀ ≫ DoubledPointLine.g₁ R 1 = c.fst.left := hw₀
  -- On the common open, the coordinate `t = s - 1` of the first chart is a unit.
  have hunit : IsUnit (DoubledPointLine.α R 1 X) := by
    have h := IsLocalization.Away.algebraMap_isUnit (S := DoubledPointLine.B₂ R 1)
      (DoubledPointLine.f₂ R 1)
    rw [DoubledPointLine.algebraMap_f₂] at h
    have h2 := isUnit_of_mul_isUnit_right h
    simpa [DoubledPointLine.α] using h2
  let v : DoubledPointLine.B₂ R 1 := ↑hunit.unit⁻¹
  let φ : R[X] →ₐ[R] DoubledPointLine.B₂ R 1 := aeval v
  -- The morphism to the affine line with coordinate `1 / t`.
  let mL : c.pt.left ⟶ Spec (CommRingCat.of R[X]) :=
    w₀ ≫ Spec.map (CommRingCat.ofHom φ.toRingHom)
  have h1 : Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ (ringTest R R[X]).hom =
      DoubledPointLine.g₁ R 1 ≫ (ringTest R R[X]).hom := by
    change Spec.map (CommRingCat.ofHom φ.toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R[X])) =
      Spec.map (CommRingCat.ofHom (DoubledPointLine.α R 1)) ≫
        Spec.map (CommRingCat.ofHom (algebraMap R R[X]))
    rw [← Spec.map_comp, ← Spec.map_comp, ← CommRingCat.ofHom_comp, ← CommRingCat.ofHom_comp,
      DoubledPointLine.α_comp_algebraMap]
    congr 2
    exact φ.comp_algebraMap
  have hmL : mL ≫ (ringTest R R[X]).hom = c.pt.hom := by
    rw [← Over.w c.fst, ← hw₀']
    change (w₀ ≫ _) ≫ _ = (w₀ ≫ _) ≫ _
    rw [Category.assoc, Category.assoc, h1]
  let m : c.pt ⟶ ringTest R R[X] := Over.homMk mL hmL
  -- Compatible pairs of points of the two lines.
  have hcompat : ∀ u : Aˣ, linePoint R A (u : A) ≫ doubledOriginChart R true =
      linePoint R A ((u : A) + 1) ≫ doubledOriginChart R false := by
    intro u
    have hs : IsUnit (aeval ((u : A) + 1) (DoubledPointLine.f₂ R 1)) := by
      simp [DoubledPointLine.f₂]
    have h := DoubledPointLine.ringTestMap_aeval_chart_eq ((u : A) + 1) hs
    have hc : aeval ((u : A) + 1) (C (1 : R) * X - 1) = (u : A) := by simp
    rw [hc] at h
    exact h
  let pair : Aˣ → {q : RingPoint R (ringTest R R[X]) A × RingPoint R (ringTest R R[X]) A //
      q.1 ≫ doubledOriginChart R true = q.2 ≫ doubledOriginChart R false} :=
    fun u => ⟨(linePoint R A (u : A), linePoint R A ((u : A) + 1)), hcompat u⟩
  let tU : TopologicalSpace Aˣ := TopologicalSpace.induced Units.val inferInstance
  have hpair : Continuous[tU, _] pair := by
    apply Continuous.subtype_mk
    exact Continuous.prodMk (hlp.comp continuous_induced_dom)
      (hlp.comp ((continuous_add_const 1).comp continuous_induced_dom))
  let H := IsHomeomorph.homeomorph _ hΦ
  let inv' : Aˣ → A := fun u => lineCoord R A (H.symm (pair u) ≫ m)
  have hinv' : Continuous[tU, _] inv' :=
    (hlc.comp (hτ m)).comp (H.symm.continuous.comp hpair)
  -- The value of `inv'` is the inverse.
  have hval : ∀ u : Aˣ, inv' u = ((u⁻¹ : Aˣ) : A) := by
    intro u
    let w : ringTest R A ⟶ c.pt := H.symm (pair u)
    have hw : affineSchemePullbackPointComparison R A c w = pair u := H.apply_symm_apply (pair u)
    have hfst : w ≫ c.fst = linePoint R A (u : A) := congrArg (fun q => q.1.1) hw
    let ω := Spec.preimage (w.left ≫ w₀)
    have hω : Spec.map ω = w.left ≫ w₀ := Spec.map_preimage _
    have hα : CommRingCat.ofHom (DoubledPointLine.α R 1) ≫ ω =
        CommRingCat.ofHom (aeval (u : A)).toRingHom := by
      apply Spec.map_injective
      rw [Spec.map_comp, hω, Category.assoc]
      change w.left ≫ w₀ ≫ DoubledPointLine.g₁ R 1 = _
      rw [hw₀']
      exact congrArg (fun φ => φ.left) hfst
    have hωα : ω.hom (DoubledPointLine.α R 1 X) = (u : A) := by
      have h := congrArg (fun f => f.hom X) hα
      simpa using h
    have hq : w ≫ m = ringTestMap R (affineRingPointEquiv R R[X] A (w ≫ m)) :=
      (affineRingPointEquiv R R[X] A).injective (HenselianIntegralPointsNotClosed.affineRingPointEquiv_ringTestMap _).symm
    have hleft : Spec.map (CommRingCat.ofHom φ.toRingHom ≫ ω) =
        Spec.map (CommRingCat.ofHom (affineRingPointEquiv R R[X] A (w ≫ m)).toRingHom) := by
      rw [Spec.map_comp, hω]
      have h := congrArg (fun φ => φ.left) hq
      rw [ringTestMap_left] at h
      rw [← h]
      change (w.left ≫ w₀) ≫ _ = w.left ≫ (w₀ ≫ _)
      rw [Category.assoc]
    have hψ := congrArg (fun f => f.hom X) (Spec.map_injective hleft)
    change lineCoord R A (w ≫ m) = _
    change _ = affineRingPointEquiv R R[X] A (w ≫ m) X at hψ
    simp only [CommRingCat.hom_comp, CommRingCat.hom_ofHom, RingHom.comp_apply,
      AlgHom.toRingHom_eq_coe, RingHom.coe_coe, φ, aeval_X] at hψ
    change affineRingPointEquiv R R[X] A (w ≫ m) X = _
    rw [← hψ]
    have hv : v * DoubledPointLine.α R 1 X = 1 := hunit.val_inv_mul
    have hmul : ω.hom v * (u : A) = 1 := by
      rw [← hωα, ← map_mul, hv, map_one]
    calc ω.hom v = ω.hom v * ((u : A) * ((u⁻¹ : Aˣ) : A)) := by rw [Units.mul_inv, mul_one]
      _ = ((u⁻¹ : Aˣ) : A) := by rw [← mul_assoc, hmul, one_mul]
  have h : (fun u : Aˣ => ((u⁻¹ : Aˣ) : A)) = inv' := funext fun u => (hval u).symm
  rw [h]
  exact hinv'

end Core

/-- The affine line over a ring is of finite presentation. -/
private instance ringTest_polynomial_locallyOfFinitePresentation (R : Type u) [CommRing R] :
    LocallyOfFinitePresentation (ringTest R R[X]).hom := by
  change LocallyOfFinitePresentation (Spec.map (CommRingCat.ofHom (algebraMap R R[X])))
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFinitePresentation)]
  exact RingHom.finitePresentation_algebraMap.mpr inferInstance

/-- **The doubled-origin counterexample.** Over a nonseparated base, the adelic points of a
fibre product of generic fibres need not carry the fibre-product topology. -/
theorem adelicSpreadNonseparatedPullback : AdelicSpreadNonseparatedPullbackStatement.{u} := by
  constructor
  · intro k F _ _ _ _ _ _ _ S
    refine ⟨DoubledPointLine.locallyOfFiniteType_hom _ 1,
      DoubledPointLine.quasiCompact_hom _ 1, ?_⟩
    intro c _hc G L hhomeo
    let : Algebra F (curvePlaceAdeleOver k F S) :=
      inferInstanceAs (Algebra F (CurvePlaceAdeleRing k F))
    have hfixed := isHomeomorph_of_imagePullbackPointComparison
      (curvePlaceSIntegers k F S) F (curvePlaceAdeleOver k F S) G
      (curvePlaceFixedModelAdelePointTopology k F S)
      (fun W => curvePlaceSpreadAdelePointTopology k F S W (G.obj W) (Iso.refl _))
      (fun W => curvePlaceSpreadAdelePointHomeomorph k F S W (G.obj W) (Iso.refl _))
      (fun h p => by
        change curvePlaceGenericFiberAdelePointEquiv k F S _ (p ≫ h) ≫ 𝟙 _ =
          (curvePlaceGenericFiberAdelePointEquiv k F S _ p ≫ 𝟙 _) ≫ G.map h
        simpa only [Category.comp_id] using
          curvePlaceGenericFiberAdelePointEquiv_natural k F S h p)
      c hhomeo
    have hA : ¬ IsEmbedding (Units.val : (curvePlaceAdeleOver k F S)ˣ →
        curvePlaceAdeleOver k F S) :=
      (adelicPunctureEmbedding.2 k F).2.1
    exact doubledOrigin_pullbackComparison_not_isHomeomorph
      (curvePlaceSIntegers k F S) (curvePlaceAdeleOver k F S) hA
      (curvePlaceFixedModelAdelePointTopology k F S)
      (fun h => adelicFixedModelFunctoriality.1 k F S _ _ h)
      (by rw [curvePlaceFixedModelAdelePointTopology_eq_affine k F S _]
          exact continuous_linePoint _ _)
      (by rw [curvePlaceFixedModelAdelePointTopology_eq_affine k F S _]
          exact continuous_lineCoord _ _) c hfixed
  · intro K _ _ S
    refine ⟨DoubledPointLine.locallyOfFiniteType_hom _ 1,
      DoubledPointLine.quasiCompact_hom _ 1, ?_⟩
    intro c _hc G L hhomeo
    let : Algebra ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) :=
      (numberFieldAdeleOver K S).algebra
    let : Algebra K (numberFieldAdeleOver K S) :=
      inferInstanceAs (Algebra K (Adeles K))
    have hfixed := isHomeomorph_of_imagePullbackPointComparison
      ((S : Set (FinitePlace K)).integer K) K (numberFieldAdeleOver K S) G
      (numberFieldFixedModelAdelePointTopology K S)
      (fun W => numberFieldSpreadAdelePointTopology K S W (G.obj W) (Iso.refl _))
      (fun W => numberFieldSpreadAdelePointHomeomorph K S W (G.obj W) (Iso.refl _))
      (fun h p => by
        change numberFieldGenericFiberAdelePointEquiv K S _ (p ≫ h) ≫ 𝟙 _ =
          (numberFieldGenericFiberAdelePointEquiv K S _ p ≫ 𝟙 _) ≫ G.map h
        simpa only [Category.comp_id] using
          numberFieldGenericFiberAdelePointEquiv_natural K S h p)
      c hhomeo
    have hA : ¬ IsEmbedding (Units.val : (numberFieldAdeleOver K S)ˣ →
        numberFieldAdeleOver K S) :=
      (adelicPunctureEmbedding.1 K).2.1
    exact doubledOrigin_pullbackComparison_not_isHomeomorph
      ((S : Set (FinitePlace K)).integer K) (numberFieldAdeleOver K S) hA
      (numberFieldFixedModelAdelePointTopology K S)
      (fun h => adelicFixedModelFunctoriality.2 K S _ _ h)
      (by rw [numberFieldFixedModelAdelePointTopology_eq_affine K S _]
          exact continuous_linePoint _ _)
      (by rw [numberFieldFixedModelAdelePointTopology_eq_affine K S _]
          exact continuous_lineCoord _ _) c hfixed

end Langlands.Global

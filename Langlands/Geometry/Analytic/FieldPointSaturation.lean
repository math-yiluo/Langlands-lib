import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.AtlasSaturationComparison
import Langlands.Geometry.Analytic.GeneralizedAffinoid.Relations
import Langlands.Geometry.Analytic.GeneralizedTateAlgebra.Evaluation

/-! # Base-field points and saturation of an affinoid atlas -/

noncomputable section

universe u v w

namespace Langlands.Analytic.FieldPointSaturationComparison

open Set Topology PresentedAffinoidAlgebra AffinoidAtlasPresentation

/-! ## Characters with values in the base field -/

section Characters

variable {K : Type u} [NormedField K]

/-- A `K`-algebra map to `K` is determined by the absolute values of its values. -/
theorem algHom_eq_of_norm_eq {B : Type v} [Ring B] [Algebra K B] {χ χ' : B →ₐ[K] K}
    (h : ∀ b, ‖χ b‖ = ‖χ' b‖) : χ = χ' := by
  ext b
  have h0 : χ (b - algebraMap K B (χ b)) = 0 := by
    rw [map_sub, AlgHom.commutes]
    exact sub_self _
  have h1 : χ' (b - algebraMap K B (χ b)) = 0 := by
    rw [← norm_eq_zero, ← h, h0, norm_zero]
  rw [map_sub, AlgHom.commutes] at h1
  exact (sub_eq_zero.1 h1).symm

variable (K) in
/-- A spectrum point `s` with `c s = x` is the absolute value of a `K`-valued character:
the point `x` is `K`-rational in the chart `c`. -/
def IsRationalFor {R : Type v} [NormedCommRing R] [Algebra K R] {X : Type w}
    (c : BanachSpectrum R → X) (x : X) : Prop :=
  ∃ χ : R →ₐ[K] K, ∃ s : BanachSpectrum R, c s = x ∧ ∀ b, ‖χ b‖ = s b

/-- Rationality pulls back along a bounded map compatible with the charts. -/
theorem IsRationalFor.comap {R₁ : Type v} {R₂ : Type w} [NormedCommRing R₁] [NormedCommRing R₂]
    [Algebra K R₁] [Algebra K R₂] {X : Type*} {c₁ : BanachSpectrum R₁ → X}
    {c₂ : BanachSpectrum R₂ → X} (ψ : BoundedAlgHom K R₂ R₁)
    (hc : ∀ y, c₂ (BanachSpectrum.comap ψ.toBoundedRingHom y) = c₁ y) {x : X}
    (h : IsRationalFor K c₁ x) : IsRationalFor K c₂ x := by
  obtain ⟨χ, s, hs, hn⟩ := h
  exact ⟨χ.comp ψ.toAlgHom, BanachSpectrum.comap ψ.toBoundedRingHom s, (hc s).trans hs,
    fun b => hn (ψ b)⟩

/-- A character whose absolute value is a spectrum point is bounded. -/
def boundedCharacter {R : Type v} [NormedCommRing R] [Algebra K R] (χ : R →ₐ[K] K)
    (s : BanachSpectrum R) (hn : ∀ b, ‖χ b‖ = s b) : BoundedAlgHom K R K where
  toAlgHom := χ
  bounded := ⟨1, one_pos, fun b => by
    rw [one_mul]
    change ‖χ b‖ ≤ ‖b‖
    rw [hn b]
    exact s.le_norm b⟩

end Characters

/-! ## The base field as an affinoid algebra -/

section PointAlgebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]

/-- The base field, presented as the affinoid algebra in no variables. -/
def pointAlgebra : PresentedAffinoidAlgebra K :=
  PresentedAffinoidAlgebra.ofRelations K 0 (PositivePolyradius.unit (Fin 0)) ∅

/-- The scalar map into the point algebra. -/
def pointInclusion : BoundedAlgHom K K (pointAlgebra K) where
  toAlgHom := Algebra.ofId K (pointAlgebra K)
  bounded := (BoundedRingHom.scalarHom K (pointAlgebra K)).bounded

omit [IsUltrametricDist K] in
theorem hasBoundedMonomials_elim0 :
    GeneralizedTateAlgebra.HasBoundedMonomials (PositivePolyradius.unit (Fin 0)) K
      (Fin.elim0 : Fin 0 → K) := by
  refine ⟨1, one_pos, fun d => ?_⟩
  rw [one_mul]
  unfold StrictTateAlgebra.monomialValue PositivePolyradius.weight
  rw [Finsupp.prod, Finsupp.prod, norm_prod]
  exact Finset.prod_le_prod₀ (fun i _ => Fin.elim0 i) (fun i _ => Fin.elim0 i)

variable [CompleteSpace K]

/-- Evaluation of the point algebra at the empty point. -/
def pointEvaluation : BoundedAlgHom K (pointAlgebra K) K :=
  PresentedAffinoidAlgebra.descendRelations K 0 (PositivePolyradius.unit (Fin 0)) ∅ K
    (GeneralizedTateAlgebra.evaluateHom (PositivePolyradius.unit (Fin 0)) K K Fin.elim0
      (hasBoundedMonomials_elim0 K))
    (fun _ hf => absurd hf (Set.notMem_empty _))

theorem pointEvaluation_algebraMap (c : K) :
    pointEvaluation K (algebraMap K (pointAlgebra K) c) = c :=
  (pointEvaluation K).toAlgHom.commutes c

end PointAlgebra

/-! ## Rational points of affinoid atlases -/

section Atlas

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Rationality descends from a chart to every chart whose range lies in its range,
by the universal property of the restriction map applied to the base field. -/
theorem isRationalFor_restriction {X : Type v} [TopologicalSpace X]
    (b : IndexedAffinoidAtlas.{u, v, w} K X) (S T : b.Index)
    (h : range (b.chart S) ⊆ range (b.chart T)) {x : X} (hx : x ∈ range (b.chart S))
    (hT : IsRationalFor K (b.chart T) x) : IsRationalFor K (b.chart S) x := by
  obtain ⟨χ, s, hs, hn⟩ := hT
  let χb : BoundedAlgHom K (b.algebra T) (pointAlgebra K) :=
    (pointInclusion K).comp (boundedCharacter χ s hn)
  have hcomap : ∀ y : BanachSpectrum (pointAlgebra K),
      BanachSpectrum.comap χb.toBoundedRingHom y = s := by
    intro y
    ext a
    rw [← hn a]
    exact BanachSpectrum.field_apply
      (BanachSpectrum.comap (pointInclusion K).toBoundedRingHom y) (χ a)
  obtain ⟨ψ, hψ, -⟩ := b.restriction_universal S T h (pointAlgebra K) χb (fun y => by
    rw [hcomap y, hs]
    exact hx)
  let ψK : BoundedAlgHom K (b.algebra S) K := (pointEvaluation K).comp ψ
  refine ⟨ψK.toAlgHom, BanachSpectrum.comap ψK.toBoundedRingHom (BanachSpectrum.fieldPoint K),
    ?_, fun _ => rfl⟩
  have key : BanachSpectrum.comap (b.restriction S T h).toBoundedRingHom
      (BanachSpectrum.comap ψK.toBoundedRingHom (BanachSpectrum.fieldPoint K)) = s := by
    ext a
    have hψa : ψ (b.restriction S T h a) = χb a :=
      congrArg (fun g : BoundedAlgHom K (b.algebra T) (pointAlgebra K) => g a) hψ
    change ‖pointEvaluation K (ψ (b.restriction S T h a))‖ = s a
    rw [hψa, ← hn a]
    change ‖pointEvaluation K (algebraMap K (pointAlgebra K) (χ a))‖ = ‖χ a‖
    rw [pointEvaluation_algebraMap]
  rw [← b.restriction_chart S T h, key, hs]

variable {A : AffinoidAtlasPresentation.{u, v, w} K}

/-- A `K`-valued point is rational in every chart containing it. -/
theorem isRationalFor_of_fieldPoint (p : FieldPoint K A) (i : A.atlas.Index)
    (hi : p.point ∈ range (A.atlas.chart i)) : IsRationalFor K (A.atlas.chart i) p.point :=
  ⟨p.eval i hi, p.isChartPoint i hi⟩

/-- `K`-valued points are determined by their underlying points. -/
theorem fieldPoint_ext {p q : FieldPoint K A} (h : p.point = q.point) : p = q := by
  refine FieldPoint.ext' h fun i hp hq => ?_
  obtain ⟨r, hr, hn⟩ := p.isChartPoint i hp
  obtain ⟨r', hr', hn'⟩ := q.isChartPoint i hq
  have hrr : r = r' := (A.atlas.isEmbedding_chart i).injective (hr.trans (h.trans hr'.symm))
  subst hrr
  exact algHom_eq_of_norm_eq fun b => (hn b).trans (hn' b).symm

/-- A point rational in every chart containing it is a `K`-valued point; the compatibility
with restrictions is automatic because the characters are determined by their absolute
values. -/
def ofRational (x : A.space)
    (h : ∀ i, x ∈ range (A.atlas.chart i) → IsRationalFor K (A.atlas.chart i) x) :
    FieldPoint K A where
  point := x
  eval i hi := (h i hi).choose
  isChartPoint i hi := (h i hi).choose_spec
  eval_restriction i j hij hi := by
    obtain ⟨si, hsi, hni⟩ := (h i hi).choose_spec
    obtain ⟨sj, hsj, hnj⟩ := (h j (hij hi)).choose_spec
    have hs : BanachSpectrum.comap (A.atlas.restriction i j hij).toBoundedRingHom si = sj :=
      (A.atlas.isEmbedding_chart j).injective
        ((A.atlas.restriction_chart i j hij si).trans (hsi.trans hsj.symm))
    apply algHom_eq_of_norm_eq
    intro b
    rw [hnj b, ← hs]
    exact hni _

@[simp]
theorem ofRational_point (x : A.space)
    (h : ∀ i, x ∈ range (A.atlas.chart i) → IsRationalFor K (A.atlas.chart i) x) :
    (ofRational x h).point = x :=
  rfl

variable (A)

/-- Rationality in all original charts gives rationality in all saturated charts. -/
theorem isRationalFor_saturated {x : A.space}
    (h : ∀ i, x ∈ range (A.atlas.chart i) → IsRationalFor K (A.atlas.chart i) x)
    (S : A.atlas.localDomainFamily) (hS : x ∈ range (A.atlas.saturatedAtlas.chart S)) :
    IsRationalFor K (A.atlas.saturatedAtlas.chart S) x := by
  set i := (A.atlas.saturatedRepresentative S).index
  have hSi : range (A.atlas.saturatedAtlas.chart S) ⊆ range (A.atlas.chart i) := by
    change range (A.atlas.saturatedChart S) ⊆ _
    rw [A.atlas.range_saturatedChart, ← A.atlas.saturatedRepresentative_locus S]
    exact image_subset_range _ _
  set T := A.atlas.originalSaturatedIndex i
  have hTi : range (A.atlas.saturatedAtlas.chart T) = range (A.atlas.chart i) :=
    A.atlas.saturatedAtlas_original_range i
  have hT : IsRationalFor K (A.atlas.saturatedAtlas.chart T) x := by
    refine IsRationalFor.comap (A.atlas.originalToSaturatedInclusion i T hTi.ge).restriction
      (fun y => ?_) (h i (hSi hS))
    exact ((A.atlas.originalToSaturatedInclusion i T hTi.ge).ambientMap_naturality y).trans
      (A.atlas.originalLocalDomain_ambientMap i y)
  exact isRationalFor_restriction A.atlas.saturatedAtlas S T (hSi.trans hTi.ge) hS hT

/-- Rationality in all saturated charts gives rationality in all original charts. -/
theorem isRationalFor_original {x : A.space}
    (h : ∀ S, x ∈ range (A.atlas.saturatedAtlas.chart S) →
      IsRationalFor K (A.atlas.saturatedAtlas.chart S) x)
    (i : A.atlas.Index) (hi : x ∈ range (A.atlas.chart i)) :
    IsRationalFor K (A.atlas.chart i) x := by
  set T := A.atlas.originalSaturatedIndex i
  have hTi : range (A.atlas.saturatedAtlas.chart T) = range (A.atlas.chart i) :=
    A.atlas.saturatedAtlas_original_range i
  refine IsRationalFor.comap (A.atlas.saturatedToOriginalInclusion T i hTi.le).restriction
    (fun y => ?_) (h T (hTi.ge hi))
  exact (A.atlas.originalLocalDomain_ambientMap i _).symm.trans
    ((A.atlas.saturatedToOriginalInclusion T i hTi.le).ambientMap_naturality y)

/-- The `K`-valued point of the saturated atlas with the same underlying point. -/
def toSaturated (p : FieldPoint K A) : FieldPoint K A.saturatedPresentation :=
  ofRational (A := A.saturatedPresentation) p.point
    (isRationalFor_saturated A fun i hi => isRationalFor_of_fieldPoint p i hi)

/-- The `K`-valued point of the original atlas with the same underlying point. -/
def ofSaturated (q : FieldPoint K A.saturatedPresentation) : FieldPoint K A :=
  ofRational (A := A) q.point
    (isRationalFor_original A fun S hS => isRationalFor_of_fieldPoint q S hS)

end Atlas


section Equivalence

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- Saturating an affinoid atlas preserves its base-field-valued points. -/
def saturationEquiv : FieldPoint K A ≃ FieldPoint K A.saturatedPresentation where
  toFun := toSaturated A
  invFun := ofSaturated A
  left_inv _ := fieldPoint_ext rfl
  right_inv _ := fieldPoint_ext rfl

@[simp]
theorem saturationEquiv_point (p : FieldPoint K A) :
    (saturationEquiv A p).point = p.point := rfl

@[simp]
theorem saturationEquiv_symm_point (q : FieldPoint K A.saturatedPresentation) :
    ((saturationEquiv A).symm q).point = q.point := rfl

end Equivalence

end Langlands.Analytic.FieldPointSaturationComparison

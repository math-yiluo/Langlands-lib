import Langlands.Geometry.Analytic.AffineAnalytificationRationalPointsProof
import Langlands.Geometry.Analytic.AffineAnalytificationLocalizedMap

/-! # Algebraic coordinates of extension-field-valued affine analytic points -/

noncomputable section

universe u v w uL

namespace Langlands.Analytic

open CategoryTheory Set PresentedAffinoidAlgebra

namespace AffinoidAtlasPresentation.FieldPoint

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {X : AffinoidAtlasPresentation.{u, v, w} K}

/-- Restrict an extension-field-valued point of the constructed saturation
to the original charts, retaining its actual characters. -/
def restrictSaturation (q : FieldPoint L X.saturatedPresentation) : FieldPoint L X where
  point := q.point
  eval i hi :=
    (q.eval (X.atlas.originalSaturatedIndex i)
      ((X.atlas.saturatedAtlas_original_range i).ge hi)).comp
        (X.atlas.saturatedToOriginalInclusion (X.atlas.originalSaturatedIndex i) i
          (X.atlas.saturatedAtlas_original_range i).le).restriction.toAlgHom
  isChartPoint i hi := by
    let I := X.atlas.originalSaturatedIndex i
    let c := X.atlas.saturatedToOriginalInclusion I i
      (X.atlas.saturatedAtlas_original_range i).le
    obtain ⟨s, hs, hn⟩ := q.isChartPoint I
      ((X.atlas.saturatedAtlas_original_range i).ge hi)
    refine ⟨BanachSpectrum.comap c.restriction.toBoundedRingHom s, ?_, ?_⟩
    · exact (X.atlas.originalLocalDomain_ambientMap i _).symm.trans
        ((c.ambientMap_naturality s).trans hs)
    · intro a
      exact hn (c.restriction a)
  eval_restriction i j hij hi := by
    let I := X.atlas.originalSaturatedIndex i
    let J := X.atlas.originalSaturatedIndex j
    have hIJ : range (X.atlas.saturatedAtlas.chart I) ⊆
        range (X.atlas.saturatedAtlas.chart J) := by
      rw [X.atlas.saturatedAtlas_original_range i, X.atlas.saturatedAtlas_original_range j]
      exact hij
    let c := X.atlas.saturatedToOriginalInclusion I i
      (X.atlas.saturatedAtlas_original_range i).le
    let d := X.atlas.saturatedToOriginalInclusion J j
      (X.atlas.saturatedAtlas_original_range j).le
    let r : X.atlas.originalLocalDomain i ⟶ X.atlas.originalLocalDomain j :=
      IndexedAffinoidAtlas.LocalDomain.Inclusion.ofSubset _ _ (by
        rw [X.atlas.originalLocalDomain_locus i, X.atlas.originalLocalDomain_locus j]
        exact hij)
    have heq := congrArg IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction
      (@Subsingleton.elim (IndexedAffinoidAtlas.LocalDomain.Inclusion
        (X.atlas.saturatedRepresentative I) (X.atlas.originalLocalDomain j))
        inferInstance (c ≫ r) (X.atlas.saturatedInclusion I J hIJ ≫ d))
    rw [IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction_comp,
      IndexedAffinoidAtlas.LocalDomain.Inclusion.restriction_comp,
      X.atlas.originalLocalDomain_restriction i j hij r] at heq
    change ((q.eval I _).comp c.restriction.toAlgHom).comp
      (X.atlas.restriction i j hij).toAlgHom = (q.eval J _).comp d.restriction.toAlgHom
    change (q.eval I _).comp
      (c.restriction.comp (X.atlas.restriction i j hij)).toAlgHom = _
    exact (congrArg (fun f : BoundedAlgHom K (X.atlas.algebra j)
        (X.atlas.saturatedRepresentative I).algebra =>
          (q.eval I _).comp f.toAlgHom) heq).trans
      (congrArg (fun e => e.comp d.restriction.toAlgHom)
        (q.eval_restriction I J hIJ _))

@[simp]
theorem restrictSaturation_point (q : FieldPoint L X.saturatedPresentation) :
    q.restrictSaturation.point = q.point := rfl

end AffinoidAtlasPresentation.FieldPoint

namespace AffineAnalytification

open AffinoidAtlasPresentation AnalyticAffineSpace

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {L : Type uL} [NormedField L] [NormedAlgebra K L]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)

/-- Recover algebraic coordinates from a point of the original affine atlas
with values in an arbitrary normed extension of the base field. -/
def originalExtensionAlgHom (p : FieldPoint L (presentation K P)) : A →ₐ[K] L :=
  let h := (presentation K P).atlas.exists_mem_range_chart p.point
  (p.eval h.choose h.choose_spec).comp (chartAlgebraMap K P h.choose)

/-- The recovered algebra map is computed in every original chart through
the point. -/
theorem originalExtensionAlgHom_apply_eq (p : FieldPoint L (presentation K P))
    (i : (presentation K P).atlas.Index)
    (hi : p.point ∈ range ((presentation K P).atlas.chart i)) (a : A) :
    originalExtensionAlgHom K P p a = p.eval i hi (chartAlgebraMap K P i a) := by
  have key : ∀ j (hj : p.point ∈ range ((presentation K P).atlas.chart j))
      (k : (presentation K P).atlas.Index)
      (hkj : range ((presentation K P).atlas.chart k) ⊆
        range ((presentation K P).atlas.chart j))
      (hk : p.point ∈ range ((presentation K P).atlas.chart k)),
      p.eval j hj (chartAlgebraMap K P j a) =
        p.eval k hk (chartAlgebraMap K P k a) := by
    intro j hj k hkj hk
    rw [← p.eval_restriction k j hkj hk]
    change p.eval k hk (PolynomialLocus.restriction P _ _ _
      (PolynomialLocus.algebraMap P (polyradius K P.arity j.val) a)) = _
    rw [PolynomialLocus.restriction_algebraMap]
    rfl
  let h := (presentation K P).atlas.exists_mem_range_chart p.point
  let j := h.choose
  have hj : p.point ∈ range ((presentation K P).atlas.chart j) := h.choose_spec
  let k := representative K P (min i.val j.val)
  have hk_range : range ((presentation K P).atlas.chart k) =
      range (chart K P (min i.val j.val)) :=
    range_representative K P (min i.val j.val)
  have hki : range ((presentation K P).atlas.chart k) ⊆
      range ((presentation K P).atlas.chart i) := by
    rw [hk_range]
    exact range_chart_mono K P (min_le_left _ _)
  have hkj : range ((presentation K P).atlas.chart k) ⊆
      range ((presentation K P).atlas.chart j) := by
    rw [hk_range]
    exact range_chart_mono K P (min_le_right _ _)
  have hk : p.point ∈ range ((presentation K P).atlas.chart k) := by
    rw [hk_range]
    rcases le_total i.val j.val with h' | h'
    · rw [min_eq_left h']
      exact hi
    · rw [min_eq_right h']
      exact hj
  change p.eval j hj (chartAlgebraMap K P j a) = _
  rw [key j hj k hkj hk, key i hi k hki hk]

/-- Recover the actual algebraic coordinates of a full extension-valued
point of the saturated affine analytification. -/
def extensionAlgHom (p : FieldPoint L (saturated K P).presentation) : A →ₐ[K] L :=
  originalExtensionAlgHom K P p.restrictSaturation

/-- The absolute values of the recovered coordinates are exactly the
algebraic point seminorm of the original analytic point. -/
theorem norm_extensionAlgHom (p : FieldPoint L (saturated K P).presentation) (a : A) :
    ‖extensionAlgHom K P p a‖ = pointSeminorm K P p.point a := by
  let q := p.restrictSaturation
  obtain ⟨i, hi⟩ := (presentation K P).atlas.exists_mem_range_chart q.point
  obtain ⟨s, hs, hn⟩ := q.isChartPoint i hi
  change ‖originalExtensionAlgHom K P q a‖ = _
  rw [originalExtensionAlgHom_apply_eq K P q i hi, hn]
  change s (PolynomialLocus.algebraMap P (polyradius K P.arity i.val) a) =
    pointSeminorm K P q.point a
  exact (congrArg (fun ν : MulRingSeminorm A => ν a)
      (pointSeminorm_chart K P i.val s)).symm.trans
    (congrArg (fun z : Space K P => pointSeminorm K P z a) hs)

end AffineAnalytification

end Langlands.Analytic

import Langlands.Geometry.Analytic.GroundFieldRationalLocusStatement

/-! # Proof of the closed rational locus under ground field extension

This file proves `GroundFieldRationalLocusStatement`. On each affinoid chart
`B` over `K`, an `L`-rational point of the scalar extension `B_L` projects to a
`K`-rational point of `B` exactly when its character takes values in `K` on the
image of `B`; this locus is closed, and over each `K`-rational point of `B`
there is exactly one `L`-rational point of `B_L`. The extended atlas glues these
chartwise facts. No hypothesis on the degree of `L` over `K` or on the
nontriviality of the absolute values is used. -/

noncomputable section

universe u v w u'

namespace Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

open Set Topology
open PresentedAffinoidAlgebra
open PresentedAffinoidAlgebra.GroundFieldExtension hiding algebra
open BanachSpectrum (rationalCharacter)

local notation "extendedAlgebra" => PresentedAffinoidAlgebra.GroundFieldExtension.algebra

variable (K : Type u) [NormedField K] [IsUltrametricDist K]
  (L : Type u') [NormedField L] [IsUltrametricDist L] [NormedAlgebra K L]
  (B : PresentedAffinoidAlgebra K)

/-- Over a `K`-rational point, the character of an `L`-rational point of the
extended chart restricts on `B` to the `K`-valued character. -/
private theorem rationalCharacter_iota
    (s : BanachSpectrum.rationalLocus K B)
    (t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B))
    (h : spectrumProjection K L B t.val = s.val) (b : B) :
    rationalCharacter t (iota K L B b) = algebraMap K L (rationalCharacter s b) := by
  let c := b - algebraMap K B (rationalCharacter s b)
  have hc : s.val c = 0 := by
    rw [← BanachSpectrum.norm_rationalCharacter s c]
    simp only [c, map_sub, AlgHom.commutes, Algebra.algebraMap_self_apply, sub_self, norm_zero]
  have ht : ‖rationalCharacter t (iota K L B c)‖ = 0 := by
    rw [BanachSpectrum.norm_rationalCharacter]
    exact (congrArg (fun p : BanachSpectrum B => p c) h).trans hc
  have ht' := norm_eq_zero.mp ht
  change ((rationalCharacter t).toAlgHom.restrictScalars K).comp (iota K L B).toAlgHom c = 0 at ht'
  rw [show c = b - algebraMap K B (rationalCharacter s b) by rfl, map_sub, AlgHom.commutes,
    sub_eq_zero] at ht'
  exact ht'

/-- The projection of an `L`-rational point is `K`-rational exactly when its
character takes values in `K` on the image of `B`. -/
private theorem spectrumProjection_mem_rationalLocus_iff
    (t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B)) :
    spectrumProjection K L B t.val ∈ BanachSpectrum.rationalLocus K B ↔
      ∀ b, rationalCharacter t (iota K L B b) ∈ range (algebraMap K L) := by
  constructor
  · intro ht b
    let s : BanachSpectrum.rationalLocus K B := ⟨_, ht⟩
    exact ⟨_, (rationalCharacter_iota K L B s t rfl b).symm⟩
  · intro ht
    let φ := (overBase K L (rationalCharacter t)).comp (iota K L B)
    let ι := Algebra.ofId K L
    let e := AlgEquiv.ofInjectiveField ι
    let ψ : B →ₐ[K] K := e.symm.toAlgHom.comp (φ.toAlgHom.codRestrict ι.range ht)
    have hψ (b : B) : algebraMap K L (ψ b) = φ b := by
      exact congrArg Subtype.val (e.apply_symm_apply (φ.toAlgHom.codRestrict ι.range ht b))
    have hn (b : B) : ‖ψ b‖ = spectrumProjection K L B t.val b := by
      rw [← norm_algebraMap' L (ψ b), hψ]
      exact BanachSpectrum.norm_rationalCharacter t (iota K L B b)
    refine ⟨⟨ψ, ⟨1, zero_lt_one, fun b => ?_⟩⟩, hn⟩
    change ‖ψ b‖ ≤ 1 * ‖b‖
    rw [hn, one_mul]
    exact (spectrumProjection K L B t.val).le_norm b

variable [CompleteSpace K] in
/-- Chartwise closedness: for complete `K`, the `L`-rational points of `B_L`
over `K`-rational points of `B` form a closed subset of the `L`-rational locus. -/
private theorem isClosed_spectrumProjection_rationalLocus :
    IsClosed {t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B) |
      spectrumProjection K L B t.val ∈ BanachSpectrum.rationalLocus K B} := by
  have hi := AddMonoidHomClass.isometry_of_norm (algebraMap K L) (norm_algebraMap' L)
  have h : IsClosed (range (algebraMap K L)) := hi.isClosedEmbedding.isClosed_range
  have heq : {t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B) |
      spectrumProjection K L B t.val ∈ BanachSpectrum.rationalLocus K B} =
        ⋂ b : B, (fun t => rationalCharacter t (iota K L B b)) ⁻¹' range (algebraMap K L) := by
    ext t
    simpa only [mem_ofPred_eq, mem_iInter, mem_preimage] using
      spectrumProjection_mem_rationalLocus_iff K L B t
  rw [heq]
  exact isClosed_iInter fun b =>
    h.preimage (BanachSpectrum.continuous_rationalCharacter_apply (iota K L B b))

variable [CompleteSpace L] in
/-- Chartwise unique lifting: for complete `L`, each `K`-rational point of `B`
has exactly one `L`-rational point of `B_L` over it, given by the scalar extension
of its character. -/
private theorem spectrumProjection_existsUnique_rationalLift
    (s : BanachSpectrum.rationalLocus K B) :
    ∃! t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B),
      spectrumProjection K L B t.val = s.val := by
  let ψ := lift K L B L ((coefficientMap K L).comp (rationalCharacter s))
  let p := BanachSpectrum.comap ψ.toBoundedRingHom (BanachSpectrum.fieldPoint L)
  let t : BanachSpectrum.rationalLocus L (extendedAlgebra K L B) := ⟨p, ψ, fun _ => rfl⟩
  have ht : spectrumProjection K L B t.val = s.val := by
    apply BanachSpectrum.ext
    intro b
    change ‖ψ (iota K L B b)‖ = s.val b
    rw [lift_iota, BoundedAlgHom.comp_apply, norm_coefficientMap,
      BanachSpectrum.norm_rationalCharacter]
  refine ⟨t, ht, fun q hq => ?_⟩
  have hq' : rationalCharacter q = ψ := by
    apply lift_unique K L B L
    apply BoundedAlgHom.ext
    exact rationalCharacter_iota K L B s q hq
  apply Subtype.ext
  apply BanachSpectrum.ext
  intro b
  rw [← BanachSpectrum.norm_rationalCharacter q b, hq']
  rfl

variable [CompleteSpace K] [CompleteSpace L] (A : AffinoidAtlasPresentation.{u, v, w} K)

/-- The closedness clause of the statement, tested on the quasinet of extended
chart images in the `L`-rational locus. -/
private theorem isClosed_projection_rationalLocus :
    IsClosed (Subtype.val ⁻¹' (projection K L A.atlas ⁻¹' A.rationalLocus K) :
      Set ((presentation K L A.atlas).rationalLocus L)) := by
  let T := presentation K L A.atlas
  let R := T.rationalLocus L
  let S := A.rationalLocus K
  let π := projection K L A.atlas
  have hnet := T.atlas.isNet_chartFamily.1.preimage_image
    (continuous_subtype_val : Continuous (Subtype.val : R → T.space))
  apply (hnet.isClosed_iff (Subtype.val ⁻¹' (π ⁻¹' S) : Set R)).2
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  let W : Set R := Subtype.val ⁻¹' range (T.atlas.chart i)
  let C := BanachSpectrum.rationalLocus L (T.atlas.algebra i)
  let f : C → W := fun z =>
    ⟨⟨T.atlas.chart i z.val, (T.chart_mem_rationalLocus_iff i z.val).2 z.property⟩,
      ⟨z.val, rfl⟩⟩
  have hf : IsEmbedding f :=
    (IsEmbedding.subtypeVal.comp IsEmbedding.subtypeVal).of_comp_iff.mp
      ((T.atlas.isEmbedding_chart i).comp IsEmbedding.subtypeVal)
  have hsurj : Function.Surjective f := by
    rintro ⟨y, z, hz⟩
    refine ⟨⟨z, (T.chart_mem_rationalLocus_iff i z).1 (hz.symm ▸ y.property)⟩, ?_⟩
    exact Subtype.ext (Subtype.ext hz)
  have he := isHomeomorph_iff_isEmbedding_surjective.2 ⟨hf, hsurj⟩
  apply he.isQuotientMap.isCoinducing.isClosed_preimage.1
  have heq : f ⁻¹' (Subtype.val ⁻¹' (Subtype.val ⁻¹' (π ⁻¹' S)) : Set W) =
      {t : C | spectrumProjection K L (A.atlas.algebra i) t.val ∈
          BanachSpectrum.rationalLocus K (A.atlas.algebra i)} := by
    ext t
    exact (congrArg (fun z => z ∈ S) (projection_chart K L A.atlas i t.val)).to_iff.trans
      (A.chart_mem_rationalLocus_iff _ _)
  rw [heq]
  exact isClosed_spectrumProjection_rationalLocus K L (A.atlas.algebra i)

/-- Every `K`-rational point of the original atlas has exactly one `L`-rational
point of the extended atlas over it. -/
private theorem projection_existsUnique_rationalLift (x : A.rationalLocus K) :
    ∃! y : (presentation K L A.atlas).rationalLocus L, projection K L A.atlas y.val = x.val := by
  obtain ⟨i, s, hs⟩ := A.atlas.exists_mem_range_chart x.val
  let r : BanachSpectrum.rationalLocus K (A.atlas.algebra i) :=
    ⟨s, (A.chart_mem_rationalLocus_iff i s).1 (hs.symm ▸ x.property)⟩
  obtain ⟨t, ht, ht_unique⟩ := spectrumProjection_existsUnique_rationalLift K L _ r
  let T := presentation K L A.atlas
  let z : T.rationalLocus L :=
    ⟨T.atlas.chart i t.val, (T.chart_mem_rationalLocus_iff i t.val).2 t.property⟩
  have hz : projection K L A.atlas z.val = x.val := by
    change projection K L A.atlas ((chartSystem K L A.atlas).chart i t.val) = x.val
    rw [projection_chart, ht]
    exact hs
  refine ⟨z, hz, fun y hy => ?_⟩
  have hiy : y.val ∈ range (T.atlas.chart i) :=
    (range_chart K L A.atlas i).symm ▸
      (show projection K L A.atlas y.val ∈ range (A.atlas.chart i) by exact ⟨s, hs.trans hy.symm⟩)
  obtain ⟨u, hu⟩ := hiy
  let u' : BanachSpectrum.rationalLocus L (T.atlas.algebra i) :=
    ⟨u, (T.chart_mem_rationalLocus_iff i u).1 (hu.symm ▸ y.property)⟩
  have hu' : spectrumProjection K L (A.atlas.algebra i) u'.val = r.val := by
    apply (A.atlas.isEmbedding_chart i).injective
    exact (projection_chart K L A.atlas i u).symm.trans
      ((congrArg (projection K L A.atlas) hu).trans (hy.trans hs.symm))
  have htu := ht_unique u' hu'
  apply Subtype.ext
  exact hu.symm.trans (congrArg (fun p => T.atlas.chart i p.val) htu)

/-- Rational points of the original atlas are exactly the unique projections
from the closed sublocus of rational points defined by descent to the base field. -/
theorem groundFieldRationalLocus : GroundFieldRationalLocusStatement.{u, v, w, u'} := by
  intro K _ _ _ L _ _ _ _ A
  refine ⟨isClosed_projection_rationalLocus K L A, ?_, ?_⟩
  · intro y hy z hz h
    obtain ⟨q, _, hq⟩ := projection_existsUnique_rationalLift K L A ⟨_, hy.2⟩
    exact congrArg Subtype.val ((hq ⟨y, hy.1⟩ rfl).trans (hq ⟨z, hz.1⟩ h.symm).symm)
  · intro x hx
    obtain ⟨y, hy, _⟩ := projection_existsUnique_rationalLift K L A ⟨x, hx⟩
    exact ⟨y.val, y.property, hy⟩

end Langlands.Analytic.IndexedAffinoidAtlas.GroundFieldExtension

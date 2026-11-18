import Langlands.Geometry.Analytic.FullRecognitionPointedFinitePairs
import Langlands.Geometry.Analytic.FieldValuedPoints
import Langlands.Geometry.Analytic.Spectrum.ResidueField.CharacterTransport

/-! # Finite completed residues over base-field-valued points -/

noncomputable section

universe u v w

namespace Langlands.Analytic

namespace BanachSpectrum

variable (K : Type u) [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [NormedCommRing A] [NormedAlgebra K A]
  (x : BanachSpectrum A) (g : A →ₐ[K] K) (hg : ∀ a, ‖g a‖ = x a)

/-- A base-field character realizing a spectrum point identifies its completed
residue field with the base field, using the canonical completed residue lift. -/
def completedResidueBaseFieldEquiv :
    BoundedAlgEquiv K (CompletedResidueField K x) K := by
  let ρ := completedResidueLift K x g hg
  have hs : Function.Surjective ρ := fun c =>
    ⟨algebraMap K (CompletedResidueField K x) c, by
      exact ρ.toAlgHom.commutes c⟩
  let e := AlgEquiv.ofBijective ρ.toAlgHom
    ⟨(isometry_completedResidueLift K x g hg).injective, hs⟩
  refine ⟨e, ρ.bounded, 1, zero_lt_one, ?_⟩
  intro c
  rw [one_mul]
  have hc := (isometry_completedResidueLift K x g hg).norm_map_of_map_zero
    (map_zero _) (e.symm c)
  change ‖e.symm c‖ ≤ ‖c‖
  exact (hc.symm.trans (congrArg norm (e.apply_symm_apply c))).le

@[simp]
theorem completedResidueBaseFieldEquiv_map (a : A) :
    completedResidueBaseFieldEquiv K x g hg (completedResidueMap K x a) = g a :=
  completedResidueLift_map K x g hg a

include g hg in
/-- A point realized over the base field has a finite-dimensional completed
residue field over that base field. -/
theorem finite_completedResidue_of_baseFieldCharacter :
    Module.Finite K (CompletedResidueField K x) :=
  Module.Finite.of_surjective
    (completedResidueBaseFieldEquiv K x g hg).toAlgEquiv.symm.toLinearMap
    (completedResidueBaseFieldEquiv K x g hg).toAlgEquiv.symm.surjective

variable {B : Type w} [NormedCommRing B] [NormedAlgebra K B]

/-- Above a base-field-realized point, a finite bounded map has a
finite-dimensional completed residue field over the base field. -/
theorem finite_completedResidue_of_finite_over_baseFieldCharacter
    (f : BoundedAlgHom K A B) (hf : f.toAlgHom.toRingHom.Finite)
    (y : BanachSpectrum B) (g : A →ₐ[K] K)
    (hg : ∀ a, ‖g a‖ = (comap f.toBoundedRingHom y) a) :
    Module.Finite K (CompletedResidueField K y) := by
  let E := CompletedResidueField K (comap f.toBoundedRingHom y)
  let F := CompletedResidueField K y
  let ρ := completedResidueComap K f y
  let : Algebra E F := ρ.toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower K E F :=
    IsScalarTower.of_algebraMap_eq fun c => (ρ.toAlgHom.commutes c).symm
  have : Module.Finite K E :=
    finite_completedResidue_of_baseFieldCharacter K _ g hg
  have : Module.Finite E F := finite_completedResidueComap K f hf y
  exact Module.Finite.trans E F

end BanachSpectrum

namespace AffinoidAtlasPresentation.StrongHom

open Set

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : AffinoidAtlasPresentation.{u, v, w} K}
  {g : StrongHom A.saturatedPresentation B.saturatedPresentation}

/-- A finite local chart pair above a full base-field point has a finite
completed residue field at its selected source spectrum point. -/
theorem IsFiniteAt.exists_finiteResidue_pair_over_baseFieldPoint
    {y : A.space} (hg : g.IsFiniteAt y)
    (p : FieldPoint K B.fullRecognitionPresentation) (hp : p.point = g.baseMap y) :
    ∃ (V : A.atlas.saturatedAtlas.RecognizedSubset)
      (W : B.atlas.saturatedAtlas.RecognizedSubset)
      (h : g.baseMap '' range V.chart ⊆ range W.chart)
      (s : BanachSpectrum V.algebra),
      V.chart s = y ∧
        (g.fullRecognitionPairs.pullback V W h).IsFiniteBanach ∧
        Module.Finite K (BanachSpectrum.CompletedResidueField K s) := by
  obtain ⟨V, W, h, s, hs, hf⟩ := hg.hasFiniteFullRecognitionPairAt
  have hw : p.point ∈ range W.chart := hp.symm ▸ h ⟨y, ⟨s, hs⟩, rfl⟩
  obtain ⟨t, ht, hn⟩ := p.isChartPoint W hw
  have hc : W.chart
      (BanachSpectrum.comap (g.fullRecognitionPairs.pullback V W h).toBoundedRingHom s) =
      p.point :=
    (g.fullRecognitionPairs.chart_comm V W h s).trans
      ((congrArg g.baseMap hs).trans hp.symm)
  have ht' : t =
      BanachSpectrum.comap (g.fullRecognitionPairs.pullback V W h).toBoundedRingHom s :=
    (B.fullRecognitionPresentation.atlas.isEmbedding_chart W).injective
      (ht.trans hc.symm)
  refine ⟨V, W, h, s, hs, hf, ?_⟩
  exact BanachSpectrum.finite_completedResidue_of_finite_over_baseFieldCharacter K
    (g.fullRecognitionPairs.pullback V W h) hf.finite s (p.eval W hw)
    (fun a => (hn a).trans (congrArg (fun z : BanachSpectrum W.algebra => z a) ht'))

end AffinoidAtlasPresentation.StrongHom

end Langlands.Analytic

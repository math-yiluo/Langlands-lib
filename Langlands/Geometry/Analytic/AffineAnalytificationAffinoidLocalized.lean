import Langlands.Geometry.Analytic.AffineAnalytificationChartAssembly
import Langlands.Geometry.Analytic.AffineAnalytificationSaturatedChartAssembly
import Langlands.Geometry.Analytic.AtlasTopology.DirectedCompact
import Langlands.Geometry.Analytic.LocalizedAffinoidChartFactorization
import Langlands.Geometry.Analytic.SmallAffinoidPullbacks

/-! # Localized affinoid tests of affine analytifications -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffineAnalytification

open CategoryTheory Set AffinoidAtlasPresentation PresentedAffinoidAlgebra
open SaturatedAtlasPresentation ChartFamilyComparison

variable (K : Type u) [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A : Type v} [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
  (R : PresentedAffinoidAlgebra K)

private abbrev spectrum (R : PresentedAffinoidAlgebra K) :=
  SmallAffinoidSpectrum.saturated.{u, u} R

private def spectrumAlgebraFamily (φ : A →ₐ[K] R) : AlgebraFamily (spectrum K R).presentation A where
  map i := (((spectrum K R).presentation.atlas.restriction i (SmallAffinoidSpectrum.topIndex R)
      (SmallAffinoidSpectrum.top_contains R i)).comp
        (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm)).toAlgHom.comp φ
  naturality i j hij := by
    apply AlgHom.ext
    intro a
    exact congrArg (fun q => q (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm (φ a)))
      ((spectrum K R).presentation.atlas.restriction_comp i j
        (SmallAffinoidSpectrum.topIndex R) hij (SmallAffinoidSpectrum.top_contains R j)
        (SmallAffinoidSpectrum.top_contains R i)).symm

/-- The strong map of saturated presentations induced by an algebra map
from the affine coordinate algebra to the affinoid algebra. -/
def saturatedAffinoidHom (φ : A →ₐ[K] R) : SmallAffinoidSpectrum.saturated.{u, u} R ⟶ saturated K P :=
  saturatedChartHom P (algebraFamilyData P (spectrumAlgebraFamily K R φ))

/-- The corresponding actual localized analytic morphism. -/
def localizedAffinoidHom (φ : A →ₐ[K] R) :
    localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} R) ⟶ localized K P :=
  localizationFunctor.map (saturatedAffinoidHom K P R φ)

/-- Read the coordinate-algebra map from the greatest source chart. -/
def affinoidStrongAlgHom (F : SmallAffinoidSpectrum.saturated.{u, u} R ⟶ saturated K P) : A →ₐ[K] R :=
  (algebraCast (SmallAffinoidSpectrum.top_algebra R)).toAlgHom.comp
    ((toAlgebraFamily P F).map (SmallAffinoidSpectrum.topIndex R))

@[simp]
theorem affinoidStrongAlgHom_saturatedAffinoidHom (φ : A →ₐ[K] R) :
    affinoidStrongAlgHom K P R (saturatedAffinoidHom K P R φ) = φ := by
  have h := (toAlgebraFamily_saturatedChartHom P
    (algebraFamilyData P (spectrumAlgebraFamily K R φ)) (SmallAffinoidSpectrum.topIndex R)).trans
    (algebraFamilyData_coordinate P (spectrumAlgebraFamily K R φ) (SmallAffinoidSpectrum.topIndex R))
  unfold affinoidStrongAlgHom
  rw [saturatedAffinoidHom, h]
  apply AlgHom.ext
  intro a
  change algebraCast (SmallAffinoidSpectrum.top_algebra R)
    ((spectrum K R).presentation.atlas.restriction (SmallAffinoidSpectrum.topIndex R)
      (SmallAffinoidSpectrum.topIndex R) _ (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm (φ a))) = φ a
  rw [(spectrum K R).presentation.atlas.restriction_id]
  change ((algebraCast (SmallAffinoidSpectrum.top_algebra R)).comp
    (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm)) (φ a) = φ a
  rw [algebraCast_comp_symm]
  rfl

/-- The greatest-chart coefficient map determines the complete strong morphism. -/
theorem affinoidStrongAlgHom_injective :
    Function.Injective (affinoidStrongAlgHom K P R) := by
  intro F G h
  have hcancel (a : A →ₐ[K] (spectrum K R).presentation.atlas.algebra
      (SmallAffinoidSpectrum.topIndex R)) :
      (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm).toAlgHom.comp
        ((algebraCast (SmallAffinoidSpectrum.top_algebra R)).toAlgHom.comp a) = a := by
    apply AlgHom.ext
    intro x
    change ((algebraCast (SmallAffinoidSpectrum.top_algebra R).symm).comp
      (algebraCast (SmallAffinoidSpectrum.top_algebra R))) (a x) = a x
    rw [algebraCast_comp_symm (SmallAffinoidSpectrum.top_algebra R).symm]
    rfl
  have ht : (toAlgebraFamily P F).map (SmallAffinoidSpectrum.topIndex R) =
      (toAlgebraFamily P G).map (SmallAffinoidSpectrum.topIndex R) :=
    (hcancel _).symm.trans ((congrArg
      (fun a : A →ₐ[K] R => (algebraCast (SmallAffinoidSpectrum.top_algebra R).symm).toAlgHom.comp a)
      h).trans (hcancel _))
  apply toAlgebraFamily_ext P F G
  intro i
  rw [← (toAlgebraFamily P F).naturality i (SmallAffinoidSpectrum.topIndex R)
    (SmallAffinoidSpectrum.top_contains R i), ht]
  exact (toAlgebraFamily P G).naturality i _ (SmallAffinoidSpectrum.top_contains R i)

/-- All localized morphisms from the affinoid spectrum to the affine
analytification are exactly the algebra maps into the affinoid algebra. -/
def localizedAffinoidHomEquiv : (A →ₐ[K] R) ≃
    (localizationFunctor.obj (SmallAffinoidSpectrum.saturated.{u, u} R) ⟶ localized K P) := by
  refine Equiv.ofBijective (localizedAffinoidHom K P R) ⟨?_, ?_⟩
  · intro φ ψ h
    have hFG := localizationFunctor_map_injective h
    exact (affinoidStrongAlgHom_saturatedAffinoidHom K P R φ).symm.trans
      ((congrArg (affinoidStrongAlgHom K P R) hFG).trans
        (affinoidStrongAlgHom_saturatedAffinoidHom K P R ψ))
  · intro f
    let b := (saturated K P).presentation.atlas
    let : Nonempty b.Index := ⟨originalIndex P (representative K P 0)⟩
    have hCompact := isCompact_range (SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R).continuous
    rw [(SmallAffinoidSpectrum.spectrumHomeomorph.{u, u} R).surjective.range_eq] at hCompact
    let : CompactSpace (localizedSpaceFunctor.obj (localizationFunctor.obj (spectrum K R))) :=
      ⟨hCompact⟩
    have hc : IsCompact (range (localizedSpaceFunctor.map f)) :=
      isCompact_range (localizedSpaceFunctor.map f).hom.continuous
    obtain ⟨j, hj⟩ := b.isNet_chartFamily.1.exists_subset_of_isCompact
      (saturated_hasDirectedCharts P) hc
    obtain ⟨β, hβ, -⟩ := SmallAffinoidSpectrum.localizedAffinoidChartFactorization
      (saturated K P) R j f (fun x => hj (mem_range_self x))
    let F := SmallAffinoidSpectrum.chartMap R j β
    have hF : saturatedAffinoidHom K P R (affinoidStrongAlgHom K P R F) = F :=
      affinoidStrongAlgHom_injective K P R (affinoidStrongAlgHom_saturatedAffinoidHom K P R _)
    exact ⟨affinoidStrongAlgHom K P R F, (congrArg localizationFunctor.map hF).trans hβ⟩

@[simp]
theorem localizedAffinoidHomEquiv_apply (φ : A →ₐ[K] R) :
    localizedAffinoidHomEquiv K P R φ = localizedAffinoidHom K P R φ := rfl

end Langlands.Analytic.AffineAnalytification

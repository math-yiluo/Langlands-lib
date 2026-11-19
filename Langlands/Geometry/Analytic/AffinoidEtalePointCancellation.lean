import Langlands.Geometry.Analytic.AffinoidPointwiseEtale
import Langlands.Geometry.Analytic.FinitePiecesEtaleAllPiecesProof
import Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationReduction
import Langlands.Geometry.Analytic.LocalizedEtaleComposition
import Mathlib.RingTheory.Unramified.LocalRing

/-! # Pointwise étale cancellation for bounded affinoid morphisms -/

noncomputable section

universe u v w z

namespace Langlands.Analytic.BoundedAlgHom

variable {K : Type u} {R : Type v} {S : Type w} {T : Type z}
  [NormedField K] [NormedCommRing R] [NormedCommRing S] [NormedCommRing T]
  [Algebra K R] [Algebra K S] [Algebra K T]

/-- For finite-type maps, a composite étale at the given spectrum point
and an unramified first map at its image give an étale second map. -/
theorem IsEtaleAtPoint.of_comp_of_isUnramifiedAtPoint
    {f : BoundedAlgHom K R S} {g : BoundedAlgHom K S T}
    (hf : f.toAlgHom.toRingHom.FiniteType) (hg : g.toAlgHom.toRingHom.FiniteType)
    {x : BanachSpectrum T}
    (hu : f.IsUnramifiedAtPoint (BanachSpectrum.comap g.toBoundedRingHom x))
    (he : (g.comp f).IsEtaleAtPoint x) : g.IsEtaleAtPoint x := by
  let y := BanachSpectrum.comap g.toBoundedRingHom x
  let z := BanachSpectrum.comap (g.comp f).toBoundedRingHom x
  let : Algebra R S := f.toAlgHom.toRingHom.toAlgebra
  let : Algebra S T := g.toAlgHom.toRingHom.toAlgebra
  let : Algebra R T := (g.comp f).toAlgHom.toRingHom.toAlgebra
  let : IsScalarTower R S T := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra.FiniteType R S := hf
  let : Algebra.IsUnramifiedAt R y.kernel :=
    (f.isUnramifiedAtPoint_iff_isUnramifiedAt hf y).mp hu
  have hcomp : Algebra.IsUnramifiedAt R x.kernel :=
    ((g.comp f).isUnramifiedAtPoint_iff_isUnramifiedAt (hg.comp hf) x).mp he.2
  refine ⟨?_, (g.isUnramifiedAtPoint_iff_isUnramifiedAt hg x).mpr
    (Algebra.IsUnramifiedAt.of_restrictScalars R x.kernel)⟩
  let : y.kernel.LiesOver z.kernel := ⟨f.kernel_comap y⟩
  let : x.kernel.LiesOver y.kernel := ⟨g.kernel_comap x⟩
  let : x.kernel.LiesOver z.kernel := ⟨(g.comp f).kernel_comap x⟩
  let : Algebra (Localization.AtPrime z.kernel) (Localization.AtPrime y.kernel) :=
    Localization.AtPrime.algebraOfLiesOver z.kernel y.kernel
  let : Algebra (Localization.AtPrime y.kernel) (Localization.AtPrime x.kernel) :=
    Localization.AtPrime.algebraOfLiesOver y.kernel x.kernel
  let : Algebra (Localization.AtPrime z.kernel) (Localization.AtPrime x.kernel) :=
    Localization.AtPrime.algebraOfLiesOver z.kernel x.kernel
  have : Algebra.EssFiniteType (Localization.AtPrime z.kernel) (Localization.AtPrime y.kernel) :=
    .of_comp R _ _
  have : Module.Flat (Localization.AtPrime z.kernel) (Localization.AtPrime x.kernel) :=
    RingHom.flat_algebraMap_iff.mp (show
      (algebraMap (Localization.AtPrime z.kernel) (Localization.AtPrime x.kernel)).Flat from he.1)
  have hflat : Module.Flat (Localization.AtPrime y.kernel) (Localization.AtPrime x.kernel) :=
    Algebra.FormallyUnramified.flat_of_restrictScalars (Localization.AtPrime z.kernel) _ _
  exact RingHom.flat_algebraMap_iff.mpr hflat

end Langlands.Analytic.BoundedAlgHom

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Finite right cancellation is sufficient for étale right cancellation
over all recognized pieces. -/
theorem etaleRightCancellation_of_finiteOver
    (hfinite : FiniteOverRightCancellationStatement.{u, v, w} K) :
    EtaleRightCancellationStatement.{u, v, w} K :=
  etaleRightCancellationReduction hfinite finitePiecesEtaleAllPieces
    (fun _ _ _ _ _ _ hf hcomp hu he => he.of_comp_of_isUnramifiedAtPoint hf
      (RingHom.FiniteType.of_comp_finiteType hcomp) hu)

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

namespace Langlands.Analytic.SaturatedAtlasPresentation

open CategoryTheory AffinoidAtlasPresentation

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

set_option linter.defProp false in
/-- The canonical strong étale property has right cancellation once
finite right cancellation over a common open base is supplied. -/
@[instance_reducible]
def strongEtaleRightCancellation_of_finiteOver
    (hfinite : StrongHom.FiniteOverRightCancellationStatement.{u, v, w} K) :
    (strongEtale (K := K) :
      MorphismProperty (SaturatedAtlasPresentation.{u, v, w} K)).HasOfPostcompProperty
        (strongEtale (K := K)) where
  of_postcomp f g hg hfg := by
    unfold strongEtale at hg hfg ⊢
    rw [Functor.map_comp] at hfg
    exact StrongHom.etaleRightCancellation_of_finiteOver hfinite _ _ _ _ _ hg hfg

/-- The same finite-over input gives right cancellation for the existing
localized étale predicate. -/
theorem etaleRightCancellation_of_finiteOver
    (hfinite : StrongHom.FiniteOverRightCancellationStatement.{u, v, v} K) :
    (etale (K := K) : MorphismProperty
      (LocalizedCategory.{u, v, v} (K := K))).HasOfPostcompProperty (etale (K := K)) :=
  etale_hasOfPostcompProperty_of_strong (strongEtaleRightCancellation_of_finiteOver hfinite)

end Langlands.Analytic.SaturatedAtlasPresentation

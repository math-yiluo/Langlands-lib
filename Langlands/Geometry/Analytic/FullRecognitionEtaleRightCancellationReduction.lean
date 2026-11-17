import Langlands.Geometry.Analytic.FullRecognitionFinitePiecesCancellation
import Langlands.Geometry.Analytic.FullRecognitionEtaleRightCancellationStatement

/-! # Reduction of strong all-pieces etale right cancellation -/

noncomputable section

universe u v w

namespace Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

open CategoryTheory Set Filter PresentedAffinoidAlgebra IndexedAffinoidAtlas
open scoped Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]

/-- Strong all-pieces etale cancellation follows from common-base finite
cancellation, finite-to-all pointwise etale recognition, and pointwise
cancellation in finite-type bounded algebra triangles. These premises remain
explicit: this is a reduction, not the unconditional target. -/
def EtaleRightCancellationReductionStatement (K : Type u)
    [NormedField K] [IsUltrametricDist K] [CompleteSpace K] : Prop :=
  FiniteOverRightCancellationStatement.{u, v, w} K →
    (∀ (A B : AffinoidAtlasPresentation.{u, v, w} K)
      (g : StrongHom A.saturatedPresentation B.saturatedPresentation) (y : A.space),
      g.HasFinitePiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y →
        g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y) →
    (∀ (R S T : PresentedAffinoidAlgebra K)
      (f : BoundedAlgHom K R S) (h : BoundedAlgHom K S T) (s : BanachSpectrum T),
      f.toAlgHom.toRingHom.FiniteType →
        (h.comp f).toAlgHom.toRingHom.FiniteType →
        f.IsUnramifiedAtPoint (BanachSpectrum.comap h.toBoundedRingHom s) →
        (h.comp f).IsEtaleAtPoint s → h.IsEtaleAtPoint s) →
    EtaleRightCancellationStatement.{u, v, w} K

/-- The geometric assembly of the three explicit prerequisites. -/
theorem etaleRightCancellationReduction :
    EtaleRightCancellationReductionStatement.{u, v, w} K := by
  intro hfinite hpieces hpointwise A B C g g' hg' hgg'
  let c := g.saturatedComp g' A.atlas.saturatedAtlas_hasAllLocalDomains
    B.atlas.saturatedAtlas_hasAllLocalDomains
  have hlocal : ∀ y : A.space,
      g.HasAllPiecesAt (fun _ _ f s => f.IsEtaleAtPoint s) y := by
    intro y
    obtain ⟨U, hU, hxU, hUprop⟩ := hg' (g.baseMap y)
    obtain ⟨V, hV, hyV, hVprop⟩ := hgg' y
    have hu := (hUprop (g.baseMap y) hxU).1
    have he := hasAllPiecesAt_isEtaleAtPoint_iff.mpr (hVprop y hyV)
    have hf : g.IsFiniteAt y := isFiniteAt_of_finiteOverRightCancellation hfinite
      hu.hasFinitePiecesAt.isFiniteAt he.hasFinitePiecesAt.isFiniteAt
    apply hpieces A B g y
    apply hasFinitePiecesAt_of_comp_of_isFiniteAt (Q' := fun _ _ f s => f.IsUnramifiedAtPoint s)
      (Q := fun _ _ f s => f.IsEtaleAtPoint s) (g' := g') (y := y) _ _ _ hf hu he
    · intro R S T r f z hr hrs hft hf
      exact ⟨(r.isFlatAtPoint_of_flat hr z).comp hf.1,
        BoundedAlgHom.IsUnramifiedAtPoint.comp
          (RingHom.Finite.of_surjective _ hrs).finiteType hft
          (r.isUnramifiedAtPoint_of_formallyUnramified
            (RingHom.FormallyUnramified.of_surjective hrs) z) hf.2⟩
    · intro R S T r f z _ hrs hft hf
      exact BoundedAlgHom.IsUnramifiedAtPoint.comp
        (RingHom.Finite.of_surjective _ hrs).finiteType hft
        (r.isUnramifiedAtPoint_of_formallyUnramified
          (RingHom.FormallyUnramified.of_surjective hrs) z) hf
    · intro R S T f f' z hft hf't hf' hcomp
      exact hpointwise R S T f' f z hf't (hft.comp hf't) hf' hcomp
  intro y
  exact ⟨Set.univ, isOpen_univ, Set.mem_univ y,
    fun z _ => hasAllPiecesAt_isEtaleAtPoint_iff.mp (hlocal z)⟩

end Langlands.Analytic.AffinoidAtlasPresentation.StrongHom

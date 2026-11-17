import Langlands.Geometry.Analytic.SpaceAnalytification
import Langlands.Geometry.Analytic.EtaleOpenMap.Proof

/-! # Hausdorffness from closed relations between affine étale charts -/

noncomputable section

universe u

namespace Langlands.Analytic.SpaceAnalytification

open CategoryTheory SaturatedAtlasPresentation Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry Langlands.AlgebraicGeometry.AlgebraicSpace

variable {K : Type u} [NontriviallyNormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : AlgebraicSpace (Spec (CommRingCat.of K))}
  {Y : LocalizedCategory.{u, u, u} (K := K)}

/-- The equality relation between every two affine étale charts is closed in the
product of the charts' underlying analytic spaces. -/
def AffineEtaleChartRelationsClosed (p : PointFamily K X Y) : Prop :=
  ∀ (A : Type u) [CommRing A] [Algebra K A] (P : FinitePolynomialPresentation K A)
    (x : RingPoints K X A), AlgebraicSpace.IsEtale (pointHom K x) →
    ∀ (B : Type u) [CommRing B] [Algebra K B] (Q : FinitePolynomialPresentation K B)
      (y : RingPoints K X B), AlgebraicSpace.IsEtale (pointHom K y) →
      IsClosed {z : localizedSpaceFunctor.obj (AffineAnalytification.localized K P) ×
        localizedSpaceFunctor.obj (AffineAnalytification.localized K Q) |
        localizedSpaceFunctor.map (p A P x) z.1 =
          localizedSpaceFunctor.map (p B Q y) z.2}

/-- Étale openness and joint surjectivity reduce Hausdorffness to closedness of
relations between affine étale charts. -/
theorem IsAnalytification.t2Space_iff_affineEtaleChartRelationsClosed
    {p : PointFamily K X Y} (hp : IsAnalytification K X Y p) :
    T2Space (localizedSpaceFunctor.obj Y) ↔ AffineEtaleChartRelationsClosed p := by
  constructor
  · intro h
    let := h
    intro A _ _ P x _ B _ _ Q y _
    exact isClosed_eq ((localizedSpaceFunctor.map (p A P x)).hom.continuous.comp continuous_fst)
      ((localizedSpaceFunctor.map (p B Q y)).hom.continuous.comp continuous_snd)
  · intro hrel
    constructor
    intro y₁ y₂ hy
    obtain ⟨A, _, _, P, x, hx, a, ha⟩ := hp.jointly_surjective y₁
    obtain ⟨B, _, _, Q, z, hz, b, hb⟩ := hp.jointly_surjective y₂
    have hn : (a, b) ∈ {w :
        localizedSpaceFunctor.obj (AffineAnalytification.localized K P) ×
        localizedSpaceFunctor.obj (AffineAnalytification.localized K Q) |
        localizedSpaceFunctor.map (p A P x) w.1 =
          localizedSpaceFunctor.map (p B Q z) w.2}ᶜ := by
      change localizedSpaceFunctor.map (p A P x) a ≠
        localizedSpaceFunctor.map (p B Q z) b
      rwa [ha, hb]
    obtain ⟨U, V, hU, hV, haU, hbV, hUV⟩ :=
      isOpen_prod_iff.mp (hrel A P x hx B Q z hz).isOpen_compl a b hn
    refine ⟨localizedSpaceFunctor.map (p A P x) '' U,
      localizedSpaceFunctor.map (p B Q z) '' V,
      etaleOpenMap K _ (hp.etale_map P x hx) U hU,
      etaleOpenMap K _ (hp.etale_map Q z hz) V hV,
      ⟨a, haU, ha⟩, ⟨b, hbV, hb⟩, ?_⟩
    apply Set.disjoint_left.mpr
    rintro t ⟨a', ha', hat⟩ ⟨b', hb', hbt⟩
    have hne := hUV (show (a', b') ∈ U ×ˢ V from ⟨ha', hb'⟩)
    exact hne (hat.trans hbt.symm)

end Langlands.Analytic.SpaceAnalytification

import Langlands.Geometry.Analytic.AtlasIntersectionFiniteRecognition
import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainProduct

/-! # Saturation of product covers from finite intersection comparisons -/

noncomputable section

universe u v w

namespace Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

open CategoryTheory Set PresentedAffinoidAlgebra

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {X : Type v} [TopologicalSpace X] {a : IndexedAffinoidAtlas.{u, v, w} K X}
  {U V : LocalDomain a} {Q : PresentedAffinoidAlgebra K}
  {f : BoundedAlgHom K U.algebra Q} {g : BoundedAlgHom K V.algebra Q}

/-- Finite local comparisons force the two ambient maps to agree everywhere
on the candidate algebra. Saturation and global representation are not inputs. -/
theorem ambient_eq_of_finiteCover
    (c : Domain.FiniteCover (Domain.whole K Q))
    (piece : Fin c.size → LocalDomain a)
    (left : ∀ i, piece i ⟶ U) (right : ∀ i, piece i ⟶ V)
    (e : ∀ i, BoundedAlgEquiv K (c.obj i).algebra (piece i).algebra)
    (hf : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp f) =
      (left i).restriction)
    (hg : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp g) =
      (right i).restriction)
    (x : BanachSpectrum Q) :
    U.ambientMap (BanachSpectrum.comap f.toBoundedRingHom x) =
      V.ambientMap (BanachSpectrum.comap g.toBoundedRingHom x) := by
  obtain ⟨i, hi⟩ := c.covers x (Set.mem_univ x)
  obtain ⟨y, hy⟩ := (c.obj i).represents.2.1.symm ▸ hi
  let z := (e i).spectrumHomeomorph.symm y
  have hz : (e i).spectrumHomeomorph z = y :=
    (e i).spectrumHomeomorph.apply_symm_apply y
  have hleft :
      BanachSpectrum.comap f.toBoundedRingHom x = (left i).spectrumMap z := by
    rw [← hy, ← hz]
    exact BanachSpectrum.ext fun b =>
      congrArg (fun h : BoundedAlgHom K U.algebra (piece i).algebra => z (h b)) (hf i)
  have hright :
      BanachSpectrum.comap g.toBoundedRingHom x = (right i).spectrumMap z := by
    rw [← hy, ← hz]
    exact BanachSpectrum.ext fun b =>
      congrArg (fun h : BoundedAlgHom K V.algebra (piece i).algebra => z (h b)) (hg i)
  rw [hleft, hright, (left i).ambientMap_naturality, (right i).ambientMap_naturality]

/-- On a candidate whose two ambient maps agree, the inverse image of an
actual product domain is the inverse image of the literal local intersection. -/
theorem pullback_product_locus_of_ambient_eq
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (hdiag : ∀ x : BanachSpectrum Q,
      U.ambientMap (BanachSpectrum.comap
        (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra)).toBoundedRingHom x) =
      V.ambientMap (BanachSpectrum.comap
        (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)).toBoundedRingHom x))
    {S T : LocalDomain a} (s : S ⟶ U) (t : T ⟶ V) :
    (Domain.pullback q (s.relativeDomain.product t.relativeDomain)).locus =
      (BanachSpectrum.comap
        (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra)).toBoundedRingHom) ⁻¹'
          (U.ambientMap ⁻¹' (S.locus ∩ T.locus)) := by
  ext x
  change
    (U.ambientMap (BanachSpectrum.comap
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra)).toBoundedRingHom x)
        ∈ S.locus ∧
    V.ambientMap (BanachSpectrum.comap
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)).toBoundedRingHom x)
        ∈ T.locus) ↔
    (U.ambientMap (BanachSpectrum.comap
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra)).toBoundedRingHom x)
        ∈ S.locus ∧
    U.ambientMap (BanachSpectrum.comap
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra)).toBoundedRingHom x)
        ∈ T.locus)
  exact and_congr Iff.rfl (by rw [hdiag x])

namespace FiniteIntersectionData

/-- Actual product preimages and finite local comparison maps supply the
saturation field of the recognition interface. The global domain property
and injectivity are still derived by that interface. -/
def ofProductCover
    (q : BoundedAlgHom K (AffinoidCoproduct.algebra K U.algebra V.algebra) Q)
    (c : Domain.FiniteCover (Domain.whole K Q))
    (S T piece : Fin c.size → LocalDomain a)
    (s : ∀ i, S i ⟶ U) (t : ∀ i, T i ⟶ V)
    (left : ∀ i, piece i ⟶ U) (right : ∀ i, piece i ⟶ V)
    (e : ∀ i, BoundedAlgEquiv K (c.obj i).algebra (piece i).algebra)
    (hf : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))) = (left i).restriction)
    (hg : ∀ i, (e i).toBoundedAlgHom.comp ((c.obj i).baseMap.comp
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra))) = (right i).restriction)
    (hpiece : ∀ i, (piece i).locus = (S i).locus ∩ (T i).locus)
    (hcover : ∀ i, (c.obj i).locus =
      (Domain.pullback q ((s i).relativeDomain.product (t i).relativeDomain)).locus)
    (hunion : (⋃ i, (piece i).locus) = U.locus ∩ V.locus) :
    FiniteIntersectionData U V Q
      (q.comp (AffinoidCoproduct.leftMap K U.algebra V.algebra))
      (q.comp (AffinoidCoproduct.rightMap K U.algebra V.algebra)) where
  cover := c
  piece := piece
  left := left
  right := right
  equiv := e
  left_eq := hf
  right_eq := hg
  locus_eq := hunion
  saturated i := by
    rw [hcover i, hpiece i]
    exact pullback_product_locus_of_ambient_eq q
      (ambient_eq_of_finiteCover c piece left right e hf hg) (s i) (t i)

end FiniteIntersectionData
end Langlands.Analytic.IndexedAffinoidAtlas.LocalDomain

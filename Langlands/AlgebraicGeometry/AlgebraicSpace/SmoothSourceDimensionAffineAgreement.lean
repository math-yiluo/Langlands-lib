import Langlands.AlgebraicGeometry.AlgebraicSpace.SmoothSourceDimensionAffineAgreementStatement
import Mathlib.Geometry.Manifold.ContMDiff.Atlas

/-! # Affine coordinates for the assembled varying-dimension analytic atlas -/

noncomputable section

universe u

open CategoryTheory Set Topology
open _root_.AlgebraicGeometry
open Langlands.AlgebraicGeometry.PointTopology
open Langlands.AlgebraicGeometry.SchemeFiberGeometry
open IsManifold
open scoped ContDiff Manifold

namespace Langlands.AlgebraicGeometry.AlgebraicSpace

open AnalyticPointStructure

variable {K : Type u} [NontriviallyNormedField K]

private theorem pointDimension_of_pure
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : SmoothOverBase X)
    (n : ℕ) (hPure : IsSmoothPureDimensional K n X) (p : Points X.presheaf) :
    SmoothDimensionPieces.pointDimension hX p = n := by
  obtain ⟨U, a, ha, hs, hU⟩ := hPure.2
  obtain ⟨x, rfl⟩ := surjective_chartPointMap a hs p
  let := hU
  let : Smooth U.hom := SmoothOfRelativeDimension.smooth n _
  have hd := (hasPureDimensionFibers_iff_relativeTopologicalKrullDimAt_eq U.hom n).mp
    (Langlands.AlgebraicGeometry.smoothPureDimension.2 _ _ _ n hU) x
  exact_mod_cast (SmoothDimensionPieces.pointDimension_chart hX a ha x).trans hd

private theorem fieldPointDimension_of_pure
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : SmoothOverBase X)
    (n : ℕ) (hPure : IsSmoothPureDimensional K n X) (x : RingPoints K X K) :
    SmoothDimensionPieces.fieldPointDimension hX x = n :=
  pointDimension_of_pure hX n hPure _

private theorem pieceInclusion_bijective_of_pure
    {X : AlgebraicSpace (Spec (CommRingCat.of K))} (hX : SmoothOverBase X)
    (n : ℕ) (hPure : IsSmoothPureDimensional K n X) :
    Function.Bijective (RingPoints.map (A := K) (SmoothDimensionPieces.inclusion hX n)) := by
  refine ⟨SmoothDimensionPieces.fieldPointInclusion_injective hX n, ?_⟩
  intro x
  obtain ⟨m, ⟨y, hy⟩, _⟩ := SmoothDimensionPieces.existsUnique_fieldPointFactor hX x
  have hm : m = n := (SmoothDimensionPieces.fieldPointDimension_eq_of_factor hX y x hy).trans
    (fieldPointDimension_of_pure hX n hPure x)
  subst m
  exact ⟨y, hy⟩

/-- The affine coordinate equivalence remains analytic in both directions after
assembling the pure-dimensional charts on the actual open dimension pieces. -/
theorem smoothSourceDimensionAffineAgreement :
    SmoothSourceDimensionAffineAgreementStatement.{u} := by
  intro K _ hK σ hσ n
  let X := (schemeToSpace _).obj (affineSpaceOver K n)
  let hX := affineSpace_smoothOverBase (K := K) n
  let hqs := affineSpace_isQuasiSeparated (K := K) n
  let hls := affineSpace_isLocallySeparated (K := K) n
  let hPure := isSmoothPureDimensional_affineSpace (K := K) n
  let := etaleChartTopology K X
  let := σ.chartedSpace n X hPure
  let := hσ.1 n X hPure
  obtain ⟨c, hc⟩ := hσ.2.2.2 n hPure
  refine ⟨c.toEquiv, hc, ⟨c.continuous, ?_⟩, ⟨c.symm.continuous, ?_⟩⟩
  · intro m E hE
    obtain ⟨e, he, rfl⟩ := hE
    let P := SmoothDimensionPieces.space hX m
    let hP := SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls m
    let := etaleChartTopology K P
    let := σ.chartedSpace m P hP
    let := hσ.1 m P hP
    have hf := hσ.2.1 m n P X hP hPure (SmoothDimensionPieces.inclusion hX m)
    have hean := contMDiffOn_symm_of_mem_maximalAtlas
      (I := 𝓘(K, Fin m → K)) (subset_maximalAtlas (n := ω) he)
    exact ((c.contMDiff.comp hf).comp_contMDiffOn hean).contDiffOn
  · intro m E hE
    by_cases hmn : m = n
    · subst m
      obtain ⟨e, he, rfl⟩ := hE
      let P := SmoothDimensionPieces.space hX n
      let hP := SmoothDimensionPieces.space_isSmoothPureDimensional hX hqs hls n
      let := etaleChartTopology K P
      let := σ.chartedSpace n P hP
      let := hσ.1 n P hP
      let f := RingPoints.map (A := K) (SmoothDimensionPieces.inclusion hX n)
      have hfEt : IsEtaleMorphism (SmoothDimensionPieces.inclusion hX n) := by
        intro U a ha
        exact ha.comp (PointOpenSubspace.isEtale_of_isOpenImmersion
          (SmoothDimensionPieces.inclusion_isOpenImmersion hX n))
      let d := (hσ.2.2.1 n P X hP hPure _ hfEt).diffeomorphOfBijective
        (pieceInclusion_bijective_of_pure hX n hPure)
      let g := d.symm ∘ c.symm
      have hfg (x : Fin n → K) : f (g x) = c.symm x := d.apply_symm_apply _
      have hmap : MapsTo g
          (c.toEquiv.symm ⁻¹' (liftDimensionChart hK hX hqs n e).source) e.source := by
        intro x hx
        obtain ⟨y, hy, hxy⟩ := hx
        have hy' : y = g x := (SmoothDimensionPieces.fieldPointInclusion_injective hX n)
          (hxy.trans (hfg x).symm)
        exact hy' ▸ hy
      have hean := contMDiffOn_of_mem_maximalAtlas
        (I := 𝓘(K, Fin n → K)) (subset_maximalAtlas (n := ω) he)
      have hcomp := (hean.comp (d.symm.contMDiff.comp c.symm.contMDiff).contMDiffOn hmap).contDiffOn
      apply hcomp.congr
      intro x _
      change (liftDimensionChart hK hX hqs n e) (c.symm x) = e (g x)
      rw [← hfg x]
      exact OpenPartialHomeomorph.lift_openEmbedding_apply e _
    · have hs : E.source = ∅ := by
        apply Set.eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hmn
        exact ((σ.dimensionAtlas hK hX hqs hls).source_dimension m E hE x hx).symm.trans
          (fieldPointDimension_of_pure hX n hPure x)
      rw [hs, Set.preimage_empty]
      exact contDiffOn_empty

end Langlands.AlgebraicGeometry.AlgebraicSpace

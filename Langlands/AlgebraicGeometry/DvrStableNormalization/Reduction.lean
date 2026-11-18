import Langlands.AlgebraicGeometry.DvrStableNormalization.ReducedFibre
import Langlands.AlgebraicGeometry.DvrAffineReducedFibreStatement
import Langlands.GroupScheme.DvrCoverAssembly

/-! # Stable normal models from the affine reduced fibre theorem -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TensorProduct

namespace Langlands.AlgebraicGeometry.DvrStableNormalization

section Model

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The stable normal model of `X`: the relative normalization `source X` of `X` in its generic
fibre with its map `map X` to `X`, packaged as a `DvrStableNormalization.Model` when that map is
finite and `source X` is geometrically reduced over `Spec R`. -/
def model (X : Over (Spec (CommRingCat.of R))) [Flat X.hom]
    [LocallyOfFiniteType X.hom] [Smooth (pullback.snd X.hom (Spec.algebraMap R (FractionRing R)))]
    (hfin : IsFinite (map X).left) (hgr : GeometricallyReduced (source X).hom) :
    DvrStableNormalization.Model X where
  source := source X
  map := map X
  finite := hfin
  surjective := inferInstance
  flat := inferInstance
  geometricallyReduced := hgr
  genericIso := genericIso X
  normal_powers := fun n => ((good_source X hfin hgr).positivePower n).hasNormalStalks
  normal_lift := fun T hT hn => by
    have := hT
    exact normal_lift X T hn

end Model

/-- The affine reduced fibre theorem implies the existence of stable normal models. -/
theorem dvrStableNormalization_of_affineReducedFibre
    (h : DvrAffineReducedFibreStatement.{u}) : DvrStableNormalizationStatement.{u} := by
  intro R _ _ _ X hflat hlft hqc hsep hsmooth
  have : Smooth (pullback.snd X.hom (Spec.algebraMap R (FractionRing R))) := hsmooth
  have : IsAffine (coverOver X).left := isAffine_coverScheme X.left
  let := (globalAlgebraMap (coverOver X)).toAlgebra
  have hA1 : Module.Flat R Γ((coverOver X).left, ⊤) := flat_globalAlgebraMap (coverOver X)
  have hA2 : Algebra.FiniteType R Γ((coverOver X).left, ⊤) :=
    finiteType_globalAlgebraMap (coverOver X)
  have hA3 := smooth_globalAlgebraMap (coverOver X)
  obtain ⟨R', cR', dR', hR', aR', hff, hfin, hred⟩ := h R Γ((coverOver X).left, ⊤) hA1 hA2 hA3
  let b := Spec.map (CommRingCat.ofHom (algebraMap R R'))
  have hb : Flat b ∧ Surjective b := by
    rw [flat_and_surjective_SpecMap_iff]
    exact (RingHom.faithfullyFlat_algebraMap_iff).mpr hff
  have : Flat b := hb.1
  have : Surjective b := hb.2
  refine ⟨R', cR', dR', hR', b, hb.1, hb.2, ?_⟩
  obtain ⟨hfinX, hgrX⟩ := finite_geometricallyReduced_of_cover X R' hfin hred
  have : Flat ((Over.pullback b).obj X).hom := by
    change Flat (pullback.snd X.hom b); infer_instance
  have : LocallyOfFiniteType ((Over.pullback b).obj X).hom := by
    change LocallyOfFiniteType (pullback.snd X.hom b); infer_instance
  have : Smooth (pullback.snd ((Over.pullback b).obj X).hom
      (Spec.algebraMap R' (FractionRing R'))) :=
    Langlands.GroupScheme.DvrCoverAssembly.smooth_generic (K := FractionRing R) b X
  exact ⟨model _ hfinX hgrX⟩

end Langlands.AlgebraicGeometry.DvrStableNormalization

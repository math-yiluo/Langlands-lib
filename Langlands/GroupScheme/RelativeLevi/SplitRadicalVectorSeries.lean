import Langlands.GroupScheme.RelativeLevi.SplitParabolicVectorSeries
import Langlands.GroupScheme.RelativeLevi.DynamicRadicalIdentification
import Langlands.GroupScheme.RelativeLevi.DynamicProof

/-! # Vector-bundle series for supplied radicals in split dynamic charts -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme.RelativeLevi

open RelativeUnipotent LocalSplitCell

variable {R : Type u} [CommRing R]
  {I J : Type u} [Fintype I] [Finite J]
  {G P U : GroupScheme (Spec (CommRingCat.of R))} [IsAffineHom G.X.hom]
  {t : splitTorus (Spec (CommRingCat.of R)) I ⟶ G}
  {D : RootDatum J (I → ℤ) (I → ℤ)}
  {fam : J → (Ga R ⟶ G)} {wt : I → ℤ}
  {i : P ⟶ G} (r : U ⟶ P)

local instance : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

variable (hG : IsReductive G)
  (hmax : IsFibrewiseMaximalTorus
    (T := splitTorus.commGroupScheme (Spec (CommRingCat.of R)) I) t)
  (hD : IsFibrewiseRootDatumOf I G t D)
  (hfam : ∀ a, IsRootParametrization t (D.root a) (fam a))
  (hPar : (Dynamic.parabolic (AffineRegularBorel.cocharacter t wt)).IsRepresentedBy i)
  (hr : IsRelativeUnipotentRadical r)
  (C : SplitParabolicWeightChart t D fam wt)

/-- The actual positive-weight term is isomorphic to every supplied relative
radical of the dynamic parabolic, preserving its prescribed ambient map. -/
def splitDynamicRadicalWeightIso : C.weights.groupScheme 0 ≅ U :=
  (C.dynamicIso hG hmax hD hfam).trans
    (dynamicParabolicRadicalComparison dynamicRelativeLevi hG
      (AffineRegularBorel.cocharacter t wt) hPar
      (Dynamic.Affine.isRepresentedBy_unipotentHom
        (AffineRegularBorel.cocharacter t wt)) r hr).val.symm

/-- The radical comparison identifies the original ambient inclusions. -/
theorem splitDynamicRadicalWeightIso_hom_comp :
    (splitDynamicRadicalWeightIso r hG hmax hD hfam hPar hr C).hom ≫ r ≫ i =
      C.weights.inclusion 0 ≫
        Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t C.cocharacter) := by
  let e := dynamicParabolicRadicalComparison dynamicRelativeLevi hG
    (AffineRegularBorel.cocharacter t wt) hPar
    (Dynamic.Affine.isRepresentedBy_unipotentHom
      (AffineRegularBorel.cocharacter t wt)) r hr
  have he : e.val.inv ≫ r ≫ i =
      Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t wt) := by
    calc
      e.val.inv ≫ r ≫ i =
          e.val.inv ≫ (e.val.hom ≫
            Dynamic.Affine.unipotentHom (AffineRegularBorel.cocharacter t wt)) :=
        congrArg (fun f => e.val.inv ≫ f) e.property.symm
      _ = _ := by simp
  change ((C.dynamicIso hG hmax hD hfam).hom ≫ e.val.inv) ≫ r ≫ i = _
  rw [Category.assoc, he, C.dynamicIso_hom_comp]

include hG hmax hD hfam hPar hr in
/-- Every supplied radical of the split dynamic parabolic has a finite
vector-bundle series, with no replacement of the supplied group scheme. -/
theorem hasFiniteVectorBundleSeries_relativeRadical_of_splitDynamic :
    HasFiniteVectorBundleSeries U := by
  have hu := hasFiniteVectorBundleSeries_splitContractingGroup
    (wt := wt) hG hmax hD hfam
  exact hasFiniteVectorBundleSeries_of_representatives
    (Dynamic.Affine.isRepresentedBy_unipotentHom (AffineRegularBorel.cocharacter t wt))
    (isRepresentedBy_unipotent_of_relativeRadical dynamicRelativeLevi hG
      (AffineRegularBorel.cocharacter t wt) hPar r hr) hu

include hG hmax hD hPar hr in
/-- Over an arbitrary local ring the actual root parametrizations exist,
so a split-torus dynamic presentation suffices for the supplied radical. -/
theorem hasFiniteVectorBundleSeries_relativeRadical_of_local_splitDynamic
    [IsLocalRing R] : HasFiniteVectorBundleSeries U :=
  hasFiniteVectorBundleSeries_relativeRadical_of_splitDynamic r hG hmax hD
    (LocalSplitBigCell.isRootParametrization_rootFamily hG hmax hD) hPar hr

end Langlands.GroupScheme.RelativeLevi

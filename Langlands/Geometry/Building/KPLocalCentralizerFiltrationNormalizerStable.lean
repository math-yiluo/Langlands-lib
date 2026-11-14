import Langlands.Geometry.Building.KPLocalTorusCharacterFiltration
import Langlands.Geometry.Building.KPLocalMoyPrasadGroups
import Langlands.Geometry.Building.MaximalUnramifiedBuildingData
import Langlands.GroupScheme.Rational.BruhatContractionReduction
import Langlands.GroupScheme.RepresentedSubgroupTransport
import Langlands.Geometry.Building.UnramifiedZeroTransport

/-! # `N(K)`-stability of the torus filtration of quasi-split building data over `F^ur`

Clause 3 of KP Lemma 7.2.3 over `K = F^ur`, for the published `localTorusFiltration`
transported to the centralizer `Z = B.centralizer.Z` through an isomorphism
`e : T ≅ Z` from a commutative group scheme `T` that is a torus. The last section restates
the result for D1's filtration `B.centralizerTorusImage hZ r` (binder
`hZ : IsTorus B.centralizer.Z`, Library module `KPLocalMoyPrasadGroups`).
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open scoped CategoryTheory.MonObj NNReal

namespace Langlands.Geometry.Building.MaximalUnramified

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H)

/-- Conjugation by `n ∈ N(K)` restricted to the centralizer `Z = Z_H(S)`. -/
def centralizerConjIso (n : normalizerPoints B.i) : B.centralizer.Z ≅ B.centralizer.Z :=
  SubgroupFunctor.IsRepresentedBy.isoOfComap B.centralizer.isRepresentedBy
    B.centralizer.isRepresentedBy (H.innerIso (n : Over.mk (𝟙 _) ⟶ H.X))
    (torusCentralizer_comap_innerIso_normalizer B.i n)

theorem map_centralizerConjIso (n : normalizerPoints B.i)
    (z : rationalPoints B.centralizer.Z) :
    rationalPoints.map B.centralizer.j (rationalPoints.map (centralizerConjIso B n).hom z) =
      (n : rationalPoints H) * rationalPoints.map B.centralizer.j z *
        (n : rationalPoints H)⁻¹ := by
  rw [← rationalPoints.map_comp_apply, centralizerConjIso,
    SubgroupFunctor.IsRepresentedBy.isoOfComap_hom_comp, rationalPoints.map_comp_apply,
    rationalPoints.map_apply (H.innerIso _).hom, comp_innerIso_hom, constantPoint_self]

variable (T : CommGroupScheme (Spec (CommRingCat.of (UnramifiedClosure F))))
  [IsAffine T.X.left] (hT : IsTorus T.toGrp) (e : T.toGrp ≅ B.centralizer.Z)

/-- `Z(K)_r`: the published torus filtration of `T`, transported to `Z` along `e`. -/
def localCentralizerFiltration (r : ℝ≥0) : Subgroup (rationalPoints B.centralizer.Z) :=
  (localTorusFiltration F T hT r).map (rationalPoints.map e.hom)

/-- `j(Z(K)_r) ⊆ H(K)`. -/
def localCentralizerFiltrationImage (r : ℝ≥0) : Subgroup (rationalPoints H) :=
  (localCentralizerFiltration B T hT e r).map (rationalPoints.map B.centralizer.j)

/-- Conjugation by `n ∈ N(K)` as an endomorphism of the torus `T`. -/
def torusConj (n : normalizerPoints B.i) : T ⟶ T :=
  Additive.ofMul (e.hom ≫ (centralizerConjIso B n).hom ≫ e.inv)

theorem map_localCentralizerFiltration_conj_le (n : normalizerPoints B.i) (r : ℝ≥0) :
    (localCentralizerFiltration B T hT e r).map
        (rationalPoints.map (centralizerConjIso B n).hom) ≤
      localCentralizerFiltration B T hT e r := by
  rintro _ ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  have hmem := map_localTorusFiltration_le F T hT hT (torusConj B T e n) r ⟨t, ht, rfl⟩
  refine ⟨_, hmem, ?_⟩
  change rationalPoints.map e.hom
      (rationalPoints.map (e.hom ≫ (centralizerConjIso B n).hom ≫ e.inv) t) = _
  rw [← rationalPoints.map_comp_apply, Category.assoc, Category.assoc, e.inv_hom_id,
    Category.comp_id, rationalPoints.map_comp_apply]

theorem map_conj_localCentralizerFiltrationImage_le (n : normalizerPoints B.i) (r : ℝ≥0) :
    (localCentralizerFiltrationImage B T hT e r).map
        (MulAut.conj (n : rationalPoints H)).toMonoidHom ≤
      localCentralizerFiltrationImage B T hT e r := by
  rintro _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
  refine ⟨_, map_localCentralizerFiltration_conj_le B T hT e n r ⟨z, hz, rfl⟩, ?_⟩
  rw [map_centralizerConjIso]
  rfl

/-- Clause 3 of KP Lemma 7.2.3 over `K`: conjugation by `n ∈ N(K)` maps `j(Z(K)_r)` onto
itself. -/
theorem localCentralizerFiltration_isNormalizerStable :
    ∀ n ∈ normalizerPoints B.i, ∀ r : ℝ≥0,
      (localCentralizerFiltrationImage B T hT e r).map (MulAut.conj n).toMonoidHom =
        localCentralizerFiltrationImage B T hT e r := by
  intro n hn r
  refine le_antisymm (map_conj_localCentralizerFiltrationImage_le B T hT e ⟨n, hn⟩ r) ?_
  have h := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom)
    (map_conj_localCentralizerFiltrationImage_le B T hT e ⟨n, hn⟩⁻¹ r)
  rw [Subgroup.map_map] at h
  refine le_trans (le_of_eq ?_) h
  conv_lhs => rw [← Subgroup.map_id (localCentralizerFiltrationImage B T hT e r)]
  congr 1
  refine MonoidHom.ext fun g => ?_
  simp [mul_assoc]

end Langlands.Geometry.Building.MaximalUnramified

namespace Langlands.Geometry.Building.MaximalUnramified.BuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {H : GroupScheme (Spec (CommRingCat.of (UnramifiedClosure F)))} [IsAffineHom H.X.hom]
  (B : BuildingData F H) (hZ : IsTorus B.centralizer.Z)

theorem centralizerTorusFiltration_eq_localCentralizerFiltration (r : ℝ≥0) :
    B.centralizerTorusFiltration hZ r =
      localCentralizerFiltration B (B.centralizerTorus hZ) hZ (Iso.refl _) r :=
  B.centralizerTorusFiltration_eq_map_iso hZ (B.centralizerTorus hZ) hZ (Iso.refl _) r

theorem centralizerTorusImage_eq_localCentralizerFiltrationImage (r : ℝ≥0) :
    B.centralizerTorusImage hZ r =
      localCentralizerFiltrationImage B (B.centralizerTorus hZ) hZ (Iso.refl _) r :=
  B.centralizerTorusImage_eq_map_iso hZ (B.centralizerTorus hZ) hZ (Iso.refl _) r

/-- Clause 3 of KP Lemma 7.2.3 over `K` (normalizer stability) in D1's convention. -/
theorem centralizerTorusImage_isNormalizerStable :
    ∀ n ∈ normalizerPoints B.i, ∀ r : ℝ≥0,
      (B.centralizerTorusImage hZ r).map (MulAut.conj n).toMonoidHom =
        B.centralizerTorusImage hZ r := by
  intro n hn r
  rw [B.centralizerTorusImage_eq_localCentralizerFiltrationImage hZ r]
  exact localCentralizerFiltration_isNormalizerStable B _ hZ _ n hn r

end Langlands.Geometry.Building.MaximalUnramified.BuildingData

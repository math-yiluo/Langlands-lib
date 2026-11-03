import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalOpenPullback
import Langlands.Geometry.Analytic.GeneralizedAffinoid.RationalLocallyRingedSpace
import Langlands.Geometry.Analytic.Spectrum.ResidueField.Lift

/-! # Actual sheaf and stalk maps of bounded affinoid morphisms -/

noncomputable section

universe u

namespace Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

open CategoryTheory TopologicalSpace Topology Opposite
open BanachSpectrum

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {A B : PresentedAffinoidAlgebra K}

/-- The actual continuous spectral map of a bounded coefficient map. -/
def openSpectrumMap (φ : BoundedAlgHom K A B) :
    TopCat.of (BanachSpectrum B) ⟶ TopCat.of (BanachSpectrum A) :=
  TopCat.ofHom (BanachSpectrum.comapContinuous φ.toBoundedRingHom)

/-- Pullback of actual compatible-family sections as a presheaf morphism. -/
def openAlgebraPresheafMap (φ : BoundedAlgHom K A B) :
    openAlgebraPresheaf K A ⟶
      (TopCat.Presheaf.pushforward (CommAlgCat K) (openSpectrumMap φ)).obj
        (openAlgebraPresheaf K B) where
  app U := CommAlgCat.ofHom (OpenSections.pullback φ U.unop)
  naturality U V h := by
    apply CommAlgCat.hom_ext
    exact (OpenSections.pullback_restriction φ h.unop.le).symm

/-- The continuous spectral map with its constructed algebra-sheaf map. -/
def algebraSheafedSpaceMap (φ : BoundedAlgHom K A B) :
    algebraSheafedSpace K B ⟶ algebraSheafedSpace K A :=
  InducedCategory.homMk {
    base := openSpectrumMap φ
    c := openAlgebraPresheafMap φ }

/-- The actual map on ordinary-open algebra stalks. -/
def openStalkMap (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    openStalk (comap φ.toBoundedRingHom y) ⟶ openStalk y :=
  (algebraSheafedSpaceMap φ).hom.stalkMap y

@[reassoc]
theorem openGerm_openStalkMap (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A)) (y : BanachSpectrum B)
    (hy : comap φ.toBoundedRingHom y ∈ U) :
    openGerm U (comap φ.toBoundedRingHom y) hy ≫ openStalkMap φ y =
      CommAlgCat.ofHom (OpenSections.pullback φ U) ≫
        openGerm ((Opens.map (openSpectrumMap φ)).obj U) y hy :=
  AlgebraicGeometry.PresheafedSpace.stalkMap_germ
    (algebraSheafedSpaceMap φ).hom U y hy

/-- Actual quotient transport commutes with completed-residue evaluation. -/
theorem completedResidueEvaluation_transport (φ : BoundedAlgHom K A B)
    (d : RationalChart K A) (e : RationalChart K B)
    (g : e ⟶ RationalChart.pullback φ d) (y : BanachSpectrum B)
    (hy : y ∈ e.locus) (hd : comap φ.toBoundedRingHom y ∈ d.locus) :
    ((completedResidueEvaluation e y hy).comp g.restriction).comp
        (pullbackMap φ d) =
      (completedResidueComap K φ y).comp
        (completedResidueEvaluation d (comap φ.toBoundedRingHom y) hd) := by
  apply RationalPresentation.hom_ext_base K A d.radii d.denominator d.numerators
    (CompletedResidueField K y) d.generates
  apply BoundedAlgHom.ext
  intro a
  change completedResidueEvaluation e y hy
    (g.restriction (pullbackMap φ d (d.baseMap a))) =
      completedResidueComap K φ y
        (completedResidueEvaluation d (comap φ.toBoundedRingHom y) hd (d.baseMap a))
  rw [pullbackMap_baseMap]
  have hg := congrArg (fun k : BoundedAlgHom K B e.algebra => k (φ a)) g.comp_baseMap
  change g.restriction ((RationalChart.pullback φ d).baseMap (φ a)) =
    e.baseMap (φ a) at hg
  rw [hg, completedResidueEvaluation_baseMap, completedResidueEvaluation_baseMap,
    completedResidueComap_map]

namespace OpenSections

/-- Pullback of concrete open sections commutes with their actual point
evaluations through the canonical completed-residue embedding. -/
theorem pointEvaluation_pullback (φ : BoundedAlgHom K A B)
    (U : Opens (BanachSpectrum A)) (y : BanachSpectrum B)
    (hy : comap φ.toBoundedRingHom y ∈ U)
    (s : Sections (U : Set (BanachSpectrum A))) :
    pointEvaluation ((Opens.map (openSpectrumMap φ)).obj U) y hy (pullback φ U s) =
      completedResidueComap K φ y
        (pointEvaluation U (comap φ.toBoundedRingHom y) hy s) := by
  let d := pointChart U (comap φ.toBoundedRingHom y) hy
  have hd : comap φ.toBoundedRingHom y ∈ interior d.val.locus :=
    mem_interior_iff_mem_nhds.mpr (pointChart_mem_nhds U _ hy)
  let V := (Opens.map (openSpectrumMap φ)).obj (interiorOpen d.val)
  let e := pointChart V y hd
  have he := mem_pointChart V y hd
  let e' : ChartIn (comap φ.toBoundedRingHom ⁻¹' (U : Set (BanachSpectrum A))) :=
    ⟨e.val, fun x hx => d.property (interior_subset (e.property hx))⟩
  let g : e.val ⟶ RationalChart.pullback φ d.val :=
    restrictionOfSubset _ _ (by
      rw [pullback_locus]
      intro x hx
      change comap φ.toBoundedRingHom x ∈ d.val.locus
      exact interior_subset (show comap φ.toBoundedRingHom x ∈
        interior d.val.locus from e.property hx))
  calc
    _ = completedResidueEvaluation e.val y he ((pullback φ U s).val e') :=
      pointEvaluation_eq_chart ((Opens.map (openSpectrumMap φ)).obj U) y hy
        e' he (pullback φ U s)
    _ = completedResidueEvaluation e.val y he
        (g.restriction (pullbackMap φ d.val (s.val d))) :=
      congrArg (completedResidueEvaluation e.val y he) (pullback_local φ U s e' d g)
    _ = completedResidueComap K φ y
        (completedResidueEvaluation d.val (comap φ.toBoundedRingHom y)
          (interior_subset hd) (s.val d)) :=
      congrArg (fun k : BoundedAlgHom K d.val.algebra
        (CompletedResidueField K y) => k (s.val d))
          (completedResidueEvaluation_transport φ d.val e.val g y he (interior_subset hd))
    _ = _ := rfl

end OpenSections

/-- The actual ordinary-open stalk map commutes with residue evaluation. -/
theorem openStalkMap_residue (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    openStalkMap φ y ≫ openStalkResidue y =
      openStalkResidue (comap φ.toBoundedRingHom y) ≫
        CommAlgCat.ofHom (completedResidueComap K φ y).toAlgHom := by
  apply TopCat.Presheaf.stalk_hom_ext (X := TopCat.of (BanachSpectrum A))
    (openAlgebraPresheaf K A)
  intro U hy
  change openGerm U (comap φ.toBoundedRingHom y) hy ≫
      openStalkMap φ y ≫ openStalkResidue y =
    openGerm U (comap φ.toBoundedRingHom y) hy ≫
      openStalkResidue (comap φ.toBoundedRingHom y) ≫
        CommAlgCat.ofHom (completedResidueComap K φ y).toAlgHom
  calc
    _ = CommAlgCat.ofHom (OpenSections.pullback φ U) ≫
        CommAlgCat.ofHom (OpenSections.pointEvaluation
          ((Opens.map (openSpectrumMap φ)).obj U) y hy) :=
      (openGerm_openStalkMap_assoc φ U y hy (openStalkResidue y)).trans
        ((Category.assoc _ _ _).trans
          (congrArg (fun k => CommAlgCat.ofHom (OpenSections.pullback φ U) ≫ k)
            (openGerm_openStalkResidue _ y hy)))
    _ = CommAlgCat.ofHom (OpenSections.pointEvaluation U
          (comap φ.toBoundedRingHom y) hy) ≫
        CommAlgCat.ofHom (completedResidueComap K φ y).toAlgHom := by
      ext s
      exact OpenSections.pointEvaluation_pullback φ U y hy s
    _ = _ := (openGerm_openStalkResidue_assoc U (comap φ.toBoundedRingHom y) hy
      (CommAlgCat.ofHom (completedResidueComap K φ y).toAlgHom)).symm

/-- A unit after pullback was already a unit in the source stalk. -/
instance openStalkMap_isLocalHom (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    IsLocalHom (openStalkMap φ y).hom where
  map_nonunit t ht := by
    apply (isUnit_iff_openStalkResidue_ne_zero (comap φ.toBoundedRingHom y) t).mpr
    intro hzero
    apply (isUnit_iff_openStalkResidue_ne_zero y (openStalkMap φ y t)).mp ht
    have hn := ConcreteCategory.congr_hom (openStalkMap_residue φ y) t
    change openStalkResidue y (openStalkMap φ y t) =
      completedResidueComap K φ y
        (openStalkResidue (comap φ.toBoundedRingHom y) t) at hn
    rw [hzero, map_zero (completedResidueComap K φ y).toAlgHom] at hn
    exact hn

/-- Forget scalars on the constructed algebra-sheaf morphism. -/
def ringSheafedSpaceMap (φ : BoundedAlgHom K A B) :
    ringSheafedSpace K B ⟶ ringSheafedSpace K A :=
  InducedCategory.homMk
    ((forget₂ (CommAlgCat K) CommRingCat.{u}).mapPresheaf.map
      (algebraSheafedSpaceMap φ).hom)

/-- The genuine ordinary-open ring-stalk map of the scalar-forgotten morphism. -/
def openRingStalkMap (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    TopCat.Presheaf.stalk (openRingPresheaf K A) (comap φ.toBoundedRingHom y) ⟶
      TopCat.Presheaf.stalk (openRingPresheaf K B) y :=
  (ringSheafedSpaceMap φ).hom.stalkMap y

set_option backward.isDefEq.respectTransparency false in
/-- The canonical scalar-forgetting comparisons conjugate the actual algebra
stalk map to the actual ring stalk map. -/
theorem openRingStalkMap_eq (φ : BoundedAlgHom K A B) (y : BanachSpectrum B) :
    openRingStalkMap φ y =
      (openStalkRingIso (comap φ.toBoundedRingHom y)).inv ≫
        (forget₂ (CommAlgCat K) CommRingCat.{u}).map (openStalkMap φ y) ≫
          (openStalkRingIso y).hom := by
  apply TopCat.Presheaf.stalk_hom_ext (X := TopCat.of (BanachSpectrum A))
    (openRingPresheaf K A)
  intro U hy
  have hginv :
      TopCat.Presheaf.germ (openRingPresheaf K A) U (comap φ.toBoundedRingHom y) hy ≫
          (openStalkRingIso (comap φ.toBoundedRingHom y)).inv =
        (forget₂ (CommAlgCat K) CommRingCat.{u}).map
          (openGerm U (comap φ.toBoundedRingHom y) hy) :=
    (Iso.comp_inv_eq _).mpr
      (openGerm_openStalkRingIso U (comap φ.toBoundedRingHom y) hy).symm
  calc
    _ = (forget₂ (CommAlgCat K) CommRingCat.{u}).map
          (CommAlgCat.ofHom (OpenSections.pullback φ U)) ≫
        TopCat.Presheaf.germ (openRingPresheaf K B)
          ((Opens.map (openSpectrumMap φ)).obj U) y hy :=
      AlgebraicGeometry.PresheafedSpace.stalkMap_germ
        (ringSheafedSpaceMap φ).hom U y hy
    _ = (forget₂ (CommAlgCat K) CommRingCat.{u}).map
          (openGerm U (comap φ.toBoundedRingHom y) hy) ≫
        (forget₂ (CommAlgCat K) CommRingCat.{u}).map (openStalkMap φ y) ≫
          (openStalkRingIso y).hom := by
      erw [← openGerm_openStalkRingIso _ y hy, ← Category.assoc,
        ← Functor.map_comp, ← openGerm_openStalkMap, Functor.map_comp, Category.assoc]
    _ = TopCat.Presheaf.germ (openRingPresheaf K A) U (comap φ.toBoundedRingHom y) hy ≫
        (openStalkRingIso (comap φ.toBoundedRingHom y)).inv ≫
          (forget₂ (CommAlgCat K) CommRingCat.{u}).map (openStalkMap φ y) ≫
            (openStalkRingIso y).hom :=
      (congrArg (fun k => k ≫
        (forget₂ (CommAlgCat K) CommRingCat.{u}).map (openStalkMap φ y) ≫
          (openStalkRingIso y).hom) hginv.symm).trans (Category.assoc _ _ _)

/-- Locality survives the canonical comparisons of genuine stalk colimits. -/
instance openRingStalkMap_isLocalHom (φ : BoundedAlgHom K A B)
    (y : BanachSpectrum B) : IsLocalHom (openRingStalkMap φ y).hom where
  map_nonunit t ht := by
    have hn := ConcreteCategory.congr_hom (openRingStalkMap_eq φ y) t
    change openRingStalkMap φ y t =
      (openStalkRingIso y).hom
        (openStalkMap φ y ((openStalkRingIso (comap φ.toBoundedRingHom y)).inv t)) at hn
    have ht' := ht.map (openStalkRingIso y).inv.hom
    rw [hn] at ht'
    simp only [← ConcreteCategory.comp_apply, Iso.hom_inv_id, ConcreteCategory.id_apply] at ht'
    have hu := (openStalkMap_isLocalHom φ y).map_nonunit _ ht'
    have hv := hu.map (openStalkRingIso (comap φ.toBoundedRingHom y)).hom.hom
    simpa only [← ConcreteCategory.comp_apply, Iso.inv_hom_id,
      ConcreteCategory.id_apply] using hv

/-- A bounded map of actual affinoid algebras induces the constructed morphism
of locally ringed spaces, with locality proved on the genuine stalks. -/
def locallyRingedSpaceMap (φ : BoundedAlgHom K A B) :
    locallyRingedSpace K B ⟶ locallyRingedSpace K A where
  toHom := (ringSheafedSpaceMap φ).hom
  prop y := openRingStalkMap_isLocalHom φ y

end Langlands.Analytic.PresentedAffinoidAlgebra.RationalChart

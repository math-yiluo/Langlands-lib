import Langlands.GroupScheme.RelativeLevi.CoordinateParabolicSplitNeighbourhood
import Langlands.GroupScheme.RelativeLevi.SplitMaximalTorusChartProof
import Langlands.GroupScheme.RelativeLevi.ParabolicClosedProof
import Langlands.GroupScheme.RelativeLevi.SplitParabolicFaceChart
import Langlands.GroupScheme.Reductive.GlobalSplitRootParametrization
import Langlands.GroupScheme.Torus.FibrewiseMaximalTransport
import Langlands.GroupScheme.Torus.LocalMaximalPropagation

/-! # Constructed affine etale face charts for a supplied relative parabolic -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom]
  (p : H ⟶ G)

local instance {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((GroupScheme.baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

/-- An actual affine etale chart of the original parabolic together with its
maximal coordinate torus, full root datum and genuine root parametrizations,
fixed integral presenting cocharacter, and canonical unscaled face chart. -/
structure AffineParabolicFaceChart (s : S) where
  ring : CommRingCat.{u}
  projection : Spec ring ⟶ S
  etale : Etale projection
  point : Spec ring
  point_over : projection point = s
  coordinateType : Type u
  coordinateFintype : Fintype coordinateType
  rootType : Type u
  rootFintype : Fintype rootType
  rootDatum : RootDatum rootType (coordinateType → ℤ) (coordinateType → ℤ)
  torus : letI := coordinateFintype
    splitTorus (Spec ring) coordinateType ⟶ (GroupScheme.baseChange projection).obj G
  maximal : letI := coordinateFintype
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ coordinateType) torus
  fibrewise : letI := coordinateFintype
    IsFibrewiseRootDatumOf coordinateType ((GroupScheme.baseChange projection).obj G) torus rootDatum
  roots : rootType → (Ga ring ⟶ (GroupScheme.baseChange projection).obj G)
  parametrized : letI := coordinateFintype
    ∀ a, IsRootParametrization torus (rootDatum.root a) (roots a)
  weight : coordinateType → ℤ
  represents : letI := coordinateFintype
    (Dynamic.parabolic (AffineRegularBorel.cocharacter torus weight)).IsRepresentedBy
      ((GroupScheme.baseChange projection).map p)
  chart : letI := coordinateFintype
    letI := rootFintype
    SplitParabolicFaceChart torus rootDatum roots weight

variable (hG : IsReductive G) (hp : IsRelativeParabolicSubgroup p)

include hG hp in
/-- Every point has a constructed actual affine etale face chart of its
supplied parabolic. All root and dynamic chart data are obtained from the
relative parabolic and reductivity hypotheses. -/
theorem nonempty_affineParabolicFaceChart (s : S) : Nonempty (AffineParabolicFaceChart p s) := by
  classical
  obtain ⟨R, hR, f, hf, x, hx, I, hI, hDI, t, ht, hm⟩ :=
    relativeParabolicSplitMaximalTorusCharts S G H p hG hp s
  let : CommRing R := hR
  let : Fintype I := hI
  let : DecidableEq I := hDI
  let GF := (GroupScheme.baseChange f).obj G
  let HF := (GroupScheme.baseChange f).obj H
  let pF : HF ⟶ GF := (GroupScheme.baseChange f).map p
  have hGF : IsReductive GF := hG.baseChange f
  have hpF : IsRelativeParabolicSubgroup pF := hp.baseChange hG f
  have htc : IsClosedSubgroup (t ≫ pF) := ht.comp
    (relativeParabolicClosed _ _ _ pF hGF hpF)
  have hmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) (t ≫ pF) := by
    intro z
    let b := geometricPoint (Spec (CommRingCat.of R)) z
    have hraw : IsMaximalTorus
        (T := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
        ((GroupScheme.baseChange b).map (t ≫ pF)) := by
      have he := IsMaximalTorus.iso_comp
        (T := splitTorus.commGroupScheme _ I)
        (T' := (CommGroupScheme.baseChange b).obj (splitTorus.commGroupScheme _ I))
        (splitTorus.baseChangeIso b I) (hm z)
      simpa only [b, pF, Category.assoc, Iso.hom_inv_id_assoc] using he
    have hres := isMaximalTorus_residueFibre_of_fieldPoint htc b hraw
    have hb : b (IsLocalRing.closedPoint
        (AlgebraicClosure ((Spec (CommRingCat.of R)).residueField z))) = z :=
      splitTorus.geometricPoint_closedPoint z
    let F (z' : Spec (CommRingCat.of R)) : Prop :=
      IsMaximalTorus (T := (CommGroupScheme.baseChange
        ((Spec (CommRingCat.of R)).fromSpecResidueField z')).obj
          (splitTorus.commGroupScheme _ I))
        ((GroupScheme.baseChange ((Spec (CommRingCat.of R)).fromSpecResidueField z')).map
          (t ≫ pF))
    exact Eq.mp (congrArg F hb) hres
  let D := principalParabolicSplitAt pF t hGF hpF hmax x
  let A := Localization.Away D.element
  let q := algebraBaseMap R A
  let b := q ≫ f
  let e : (GroupScheme.baseChange q).obj GF ≅ (GroupScheme.baseChange b).obj G :=
    Descent.pullbackComparison f q b rfl G
  let iA := splitTorus.baseChangeHom (K := A) GF I (t ≫ pF)
  let iB := iA ≫ e.hom
  let : Smooth GF.X.hom := hGF.smooth
  have hAmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iA :=
    hmax.baseChange_coordinates q
  have hBmax : IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ I) iB :=
    IsFibrewiseMaximalTorus.comp_ambientIso iA e hAmax
  have hPA : IsFibrewiseRootDatumOf I ((GroupScheme.baseChange q).obj GF) iA D.rootDatum :=
    D.fibrewise
  have hPB : IsFibrewiseRootDatumOf I ((GroupScheme.baseChange b).obj G) iB D.rootDatum :=
    IsFibrewiseRootDatumOf.comp_ambientIso iA e hPA
  let : Finite D.rootType := D.fibrewise.finite
  let : Fintype D.rootType := Fintype.ofFinite D.rootType
  have hfree (a : D.rootType) : Nonempty
      (splitTorus.exponentWeightSpace I ((GroupScheme.baseChange b).obj G) iB
        (D.rootDatum.root a) ≃ₗ[CommRingCat.of A] CommRingCat.of A) := by
    obtain ⟨l⟩ := D.free a
    exact ⟨(splitTorus.exponentWeightAmbientEquiv iA e (D.rootDatum.root a)).symm.trans l⟩
  let hGB := hG.baseChange b
  let fam := LocalRootGroup.rootParametrizationsOfFreeWeights iB hGB hBmax hPB hfree
  have hfam (a : D.rootType) : IsRootParametrization iB (D.rootDatum.root a) (fam a) :=
    LocalRootGroup.isRootParametrization_rootParametrizationsOfFreeWeights iB hGB hBmax hPB hfree a
  have hpar : (Dynamic.parabolic (AffineRegularBorel.cocharacter iB D.weight)).IsRepresentedBy
      ((GroupScheme.baseChange b).map p) := by
    have hd := isRepresentedBy_dynamicParabolic_direct p f q
      (AffineRegularBorel.cocharacter iA D.weight) D.represents
    simpa only [iB, e, AffineRegularBorel.cocharacter, Category.assoc] using hd
  let C : SplitParabolicFaceChart iB D.rootDatum fam D.weight :=
    Classical.choice (nonempty_splitParabolicFaceChart hGB hBmax hPB hfam)
  have hq : IsOpenImmersion q := by
    dsimp [q, algebraBaseMap]
    infer_instance
  let : IsOpenImmersion q := hq
  let : Etale f := hf
  have hrange : x ∈ Set.range q := by
    change x ∈ Set.range (PrimeSpectrum.comap (algebraMap R A))
    rw [PrimeSpectrum.localization_away_comap_range A D.element]
    exact D.avoids
  obtain ⟨y, hy⟩ := hrange
  exact ⟨{
    ring := CommRingCat.of A
    projection := b
    etale := inferInstance
    point := y
    point_over := (congrArg f hy).trans hx
    coordinateType := I
    coordinateFintype := hI
    rootType := D.rootType
    rootFintype := inferInstance
    rootDatum := D.rootDatum
    torus := iB
    maximal := hBmax
    fibrewise := hPB
    roots := fam
    parametrized := hfam
    weight := D.weight
    represents := hpar
    chart := C }⟩

/-- Choose the proved actual affine etale face chart through a supplied point. -/
def affineParabolicFaceChartAt (s : S) : AffineParabolicFaceChart p s :=
  Classical.choice (nonempty_affineParabolicFaceChart p hG hp s)

end Langlands.GroupScheme.RelativeLevi

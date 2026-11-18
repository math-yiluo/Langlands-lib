import Langlands.GroupScheme.RelativeLevi.FiniteFaceCoverGroups
import Langlands.GroupScheme.RelativeLevi.SplitFaceAffineTransport
import Langlands.GroupScheme.RelativeLevi.SplitRadicalFaceComparison
import Langlands.GroupScheme.Reductive.FibrewiseRootDatumBaseChange

/-! # Actual face models after arbitrary affine restriction -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 1000000

namespace Langlands.GroupScheme.RelativeLevi

open LocalSplitCell LocalSplitRootBaseChange
open SplitParabolicFaceChart (allRootIndex)

/-- Full actual split face data for a prescribed homomorphism over an affine
base, without requiring a point or an etale projection of that base. -/
structure AffineParabolicFaceModel {R : CommRingCat.{u}}
    {G H : GroupScheme (Spec R)} [IsAffineHom G.X.hom] (p : H ⟶ G) where
  coordinateType : Type u
  coordinateFintype : Fintype coordinateType
  rootType : Type u
  rootFintype : Fintype rootType
  rootDatum : RootDatum rootType (coordinateType → ℤ) (coordinateType → ℤ)
  torus : letI := coordinateFintype
    splitTorus (Spec R) coordinateType ⟶ G
  maximal : letI := coordinateFintype
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ coordinateType) torus
  fibrewise : letI := coordinateFintype
    IsFibrewiseRootDatumOf coordinateType G torus rootDatum
  roots : rootType → (Ga R ⟶ G)
  parametrized : letI := coordinateFintype
    ∀ a, IsRootParametrization torus (rootDatum.root a) (roots a)
  weight : coordinateType → ℤ
  represents : letI := coordinateFintype
    (Dynamic.parabolic (AffineRegularBorel.cocharacter torus weight)).IsRepresentedBy p
  chart : letI := coordinateFintype
    letI := rootFintype
    SplitParabolicFaceChart torus rootDatum roots weight
  terms : ℕ → SubgroupFunctor G
  terms_eq_allRootSubgroup : letI := coordinateFintype
    letI := rootFintype
    ∀ d, terms d = chart.allRootSubgroup d

namespace AffineParabolicFaceModel

variable {R : CommRingCat.{u}} {G H : GroupScheme (Spec R)}
  [IsAffineHom G.X.hom] {p : H ⟶ G} (M : AffineParabolicFaceModel p)

local instance affineFaceRestriction_M_coordinateType : Fintype M.coordinateType := M.coordinateFintype
local instance affineFaceRestriction_M_rootType : Fintype M.rootType := M.rootFintype
local instance modelAmbientAffine : IsAffine G.X.left := isAffine_of_isAffineHom G.X.hom

/-- The original ambient map of the actual face term in the model. -/
def termInclusion (d : ℕ) : M.chart.weights.groupScheme d ⟶ G :=
  M.chart.weights.inclusion d ≫ Dynamic.Affine.unipotentHom
    (AffineRegularBorel.cocharacter M.torus M.chart.cocharacter)

/-- The original model map has its full-root subgroup presentation on all tests. -/
theorem range_termInclusion_eq_allRootSubgroup (d : ℕ) :
    SubgroupFunctor.range (M.termInclusion d) = M.chart.allRootSubgroup d :=
  M.chart.range_inclusion_comp_eq_allRootSubgroup d

variable (N : AffineParabolicFaceModel p)

local instance affineFaceRestriction_N_coordinateType : Fintype N.coordinateType := N.coordinateFintype
local instance affineFaceRestriction_N_rootType : Fintype N.rootType := N.rootFintype

/-- Two full affine models of the same supplied radical have exactly the
same original unscaled term, independently of all chart choices. -/
theorem range_termInclusion_eq [Nontrivial R] {U : GroupScheme (Spec R)}
    (r : U ⟶ H) (hG : IsReductive G) (hr : IsRelativeUnipotentRadical r) (d : ℕ) :
    SubgroupFunctor.range (M.termInclusion d) =
      SubgroupFunctor.range (N.termInclusion d) := by
  classical
  exact M.chart.range_inclusion_eq_of_sameParabolic N.chart hG M.maximal N.maximal
    M.fibrewise N.fibrewise M.parametrized N.parametrized
    (unipotent_eq_of_same_suppliedRadical
      (AffineRegularBorel.cocharacter M.torus M.weight)
      (AffineRegularBorel.cocharacter N.torus N.weight) r hG M.represents N.represents hr)
    (M.represents.2.symm.trans N.represents.2) d

/-- The stored full-root terms retain precisely the original model maps. -/
theorem terms_eq_range_termInclusion (d : ℕ) :
    M.terms d = SubgroupFunctor.range (M.termInclusion d) := by
  rw [M.terms_eq_allRootSubgroup, M.range_termInclusion_eq_allRootSubgroup]

/-- The actual stored term functors agree for two models of the same radical. -/
theorem terms_eq [Nontrivial R] {U : GroupScheme (Spec R)}
    (r : U ⟶ H) (hG : IsReductive G) (hr : IsRelativeUnipotentRadical r) (d : ℕ) :
    M.terms d = N.terms d := by
  rw [M.terms_eq_range_termInclusion, N.terms_eq_range_termInclusion]
  exact M.range_termInclusion_eq N r hG hr d

end AffineParabolicFaceModel

variable {S : Scheme.{u}} {G H : GroupScheme S} [IsAffineHom G.X.hom] {p : H ⟶ G}

local instance restrictionAmbientAffine {T : Scheme.{u}} (b : T ⟶ S) :
    IsAffineHom ((baseChange b).obj G).X.hom :=
  MorphismProperty.pullback_snd G.X.hom b inferInstance

namespace AffineParabolicFaceChart

variable {s : S} (C : AffineParabolicFaceChart p s)

local instance affineFaceRestriction_C_coordinateType : Fintype C.coordinateType := C.coordinateFintype
local instance affineFaceRestriction_C_rootType : Fintype C.rootType := C.rootFintype
local instance restrictionSourceSchemeAffine :
    IsAffine ((baseChange C.projection).obj G).X.left :=
  isAffine_of_isAffineHom ((baseChange C.projection).obj G).X.hom

/-- The ORIGINAL chart inclusion has the full-root presentation on all tests. -/
theorem range_termInclusion_eq_allRootSubgroup (d : ℕ) :
    SubgroupFunctor.range (C.termInclusion d) = C.chart.allRootSubgroup d :=
  C.chart.range_inclusion_comp_eq_allRootSubgroup d

section Coefficients

variable (A : CommRingCat.{u}) [Algebra C.ring A]

local instance coefficientRestriction_iteratedAffine :
    IsAffineHom ((baseChange (algebraBaseMap C.ring A)).obj
      ((baseChange C.projection).obj G)).X.hom :=
  inferInstanceAs (IsAffineHom (CategoryTheory.Limits.pullback.snd
    ((baseChange C.projection).obj G).X.hom (algebraBaseMap C.ring A)))

/-- The original direct base map after coefficient restriction. -/
abbrev coefficientBaseMap : Spec A ⟶ S := algebraBaseMap C.ring A ≫ C.projection

/-- The actual tower comparison with the original direct ambient pullback. -/
abbrev coefficientAmbientIso :
    (baseChange (algebraBaseMap C.ring A)).obj ((baseChange C.projection).obj G) ≅
      (baseChange (C.coefficientBaseMap A)).obj G :=
  Descent.pullbackComparison C.projection (algebraBaseMap C.ring A)
    (C.coefficientBaseMap A) rfl G

/-- The transported actual coordinate torus in the original direct pullback. -/
abbrev coefficientTorus : splitTorus (Spec A) C.coordinateType ⟶
    (baseChange (C.coefficientBaseMap A)).obj G :=
  splitTorus.baseChangeHom (K := A) ((baseChange C.projection).obj G)
    C.coordinateType C.torus ≫ (C.coefficientAmbientIso A).hom

/-- Actual coefficient-base-changed roots in the original direct ambient group. -/
abbrev coefficientRoots (α : C.rootType) : Ga A ⟶
    (baseChange (C.coefficientBaseMap A)).obj G :=
  baseChangeRoot A (C.roots α) ≫ (C.coefficientAmbientIso A).hom

/-- The transported torus is maximal on every fibre. -/
theorem coefficientTorus_maximal (hG : IsReductive G) :
    IsFibrewiseMaximalTorus (T := splitTorus.commGroupScheme _ C.coordinateType)
      (C.coefficientTorus A) := by
  let : Smooth ((baseChange C.projection).obj G).X.hom := (hG.baseChange C.projection).smooth
  exact IsFibrewiseMaximalTorus.comp_ambientIso _ _
    (C.maximal.baseChange_coordinates (algebraBaseMap C.ring A))

/-- Coefficient restriction and the actual ambient comparison preserve the full datum. -/
theorem coefficientTorus_fibrewise :
    IsFibrewiseRootDatumOf C.coordinateType ((baseChange (C.coefficientBaseMap A)).obj G)
      (C.coefficientTorus A) C.rootDatum := by
  exact IsFibrewiseRootDatumOf.comp_ambientIso _ _ C.fibrewise.baseChange_implicit

/-- The transported actual root maps are genuine parametrizations. -/
theorem coefficientRoots_parametrized (α : C.rootType) :
    IsRootParametrization (C.coefficientTorus A) (C.rootDatum.root α)
      (C.coefficientRoots A α) :=
  (isRootParametrization_baseChangeRoot A C.torus (C.rootDatum.root α)
    (C.roots α) (C.parametrized α)).comp_iso (C.coefficientAmbientIso A) rfl

/-- The prescribed direct pullback of the parabolic retains its dynamic presentation. -/
theorem coefficientTorus_represents :
    (Dynamic.parabolic (AffineRegularBorel.cocharacter (C.coefficientTorus A) C.weight)).IsRepresentedBy
      ((baseChange (C.coefficientBaseMap A)).map p) := by
  let q := algebraBaseMap C.ring A
  let G₀ := (baseChange C.projection).obj G
  let i₁ := splitTorus.baseChangeHom (K := A) G₀ C.coordinateType C.torus
  have hrep : (Dynamic.parabolic (AffineRegularBorel.cocharacter i₁ C.weight)).IsRepresentedBy
      ((baseChange q).map ((baseChange C.projection).map p)) := by
    have ht := C.represents.baseChange q
    have hc : Dynamic.baseChangeCocharacter q (AffineRegularBorel.cocharacter C.torus C.weight) =
        AffineRegularBorel.cocharacter i₁ C.weight :=
      splitTorus.RelativeCocharacterCentralizer.cocharacter_baseChange
        C.coordinateType G₀ C.torus C.weight q
    rw [← Dynamic.parabolic_baseChange, hc] at ht
    exact ht
  have ht := isRepresentedBy_dynamicParabolic_direct p C.projection q
    (AffineRegularBorel.cocharacter i₁ C.weight) hrep
  simpa only [coefficientTorus, coefficientAmbientIso, coefficientBaseMap,
    AffineRegularBorel.cocharacter, Category.assoc] using ht

/-- A proved face chart on the transported full actual data. -/
def coefficientChart (hG : IsReductive G) :
    SplitParabolicFaceChart (C.coefficientTorus A) C.rootDatum (C.coefficientRoots A) C.weight :=
  Classical.choice (nonempty_splitParabolicFaceChart (hG.baseChange (C.coefficientBaseMap A))
    (C.coefficientTorus_maximal A hG) (C.coefficientTorus_fibrewise A)
    (C.coefficientRoots_parametrized A))

/-- The full actual face model in the direct original ambient pullback. -/
abbrev coefficientModel (hG : IsReductive G) :
    AffineParabolicFaceModel ((baseChange (C.coefficientBaseMap A)).map p) where
  coordinateType := C.coordinateType
  coordinateFintype := C.coordinateFintype
  rootType := C.rootType
  rootFintype := C.rootFintype
  rootDatum := C.rootDatum
  torus := C.coefficientTorus A
  maximal := C.coefficientTorus_maximal A hG
  fibrewise := C.coefficientTorus_fibrewise A
  roots := C.coefficientRoots A
  parametrized := C.coefficientRoots_parametrized A
  weight := C.weight
  represents := C.coefficientTorus_represents A
  chart := C.coefficientChart A hG
  terms := fun d => (C.coefficientChart A hG).allRootSubgroup d
  terms_eq_allRootSubgroup := fun _ => rfl

/-- The constructed coefficient model recovers every original actual term. -/
theorem range_coefficientModel_termInclusion (hG : IsReductive G) (d : ℕ) :
    SubgroupFunctor.range
      ((baseChange (algebraBaseMap C.ring A)).map (C.termInclusion d) ≫
        (C.coefficientAmbientIso A).hom) =
      (C.coefficientModel A hG).terms d := by
  let : Nontrivial C.ring := C.point.nontrivial
  have hheight := C.chart.faceHeight_eq_of_sameCoordinateData
    (C.coefficientChart A hG) (hG.baseChange C.projection) C.maximal C.fibrewise
  apply SubgroupFunctor.ext
  intro T
  rw [SubgroupFunctor.range_comp_carrier, SubgroupFunctor.range_baseChangeHom,
    C.range_termInclusion_eq_allRootSubgroup, C.chart.allRootSubgroup_baseChange]
  change (Langlands.GroupTheory.HeightFiltration.level
    (rootFactor (fun α => baseChangeRoot A (C.roots α)) (allRootIndex C.rootType) T)
    (fun k => C.chart.allRootWeight ((allRootIndex C.rootType) k)) (d + 1)).map
      ((yonedaGrp.map (C.coefficientAmbientIso A).hom).app (Opposite.op T)).hom =
    Langlands.GroupTheory.HeightFiltration.level
      (rootFactor (fun α => baseChangeRoot A (C.roots α) ≫
        (C.coefficientAmbientIso A).hom) (allRootIndex C.rootType) T)
      (fun k => (C.coefficientChart A hG).allRootWeight ((allRootIndex C.rootType) k))
      (d + 1)
  rw [Langlands.GroupTheory.HeightFiltration.map_level]
  congr 1
  · funext k
    exact map_rootFactor (fun α => baseChangeRoot A (C.roots α))
      (allRootIndex C.rootType) (C.coefficientAmbientIso A).hom T k
  · funext k
    exact congrArg Int.toNat
      (LinearMap.congr_fun hheight (C.rootDatum.rootSpanMem ℤ ((allRootIndex C.rootType) k)))

/-- Coefficient restriction constructs a model in the direct original ambient
pullback and recovers all original terms. -/
theorem exists_coefficientRestrictionModel (hG : IsReductive G) :
    ∃ M : AffineParabolicFaceModel
        ((baseChange (algebraBaseMap C.ring A ≫ C.projection)).map p),
      ∀ d, SubgroupFunctor.range
        ((baseChange (algebraBaseMap C.ring A)).map (C.termInclusion d) ≫
          (Descent.pullbackComparison C.projection (algebraBaseMap C.ring A)
            (algebraBaseMap C.ring A ≫ C.projection) rfl G).hom) =
        M.terms d :=
  ⟨C.coefficientModel A hG, C.range_coefficientModel_termInclusion A hG⟩

end Coefficients

/-- Restriction to any affine parameter scheme has a full actual model in
the direct pullback of the ORIGINAL ambient group, recovering every original
term after the actual tower comparison. -/
theorem exists_restrictionModel (hG : IsReductive G) (A : CommRingCat.{u})
    (b : Spec A ⟶ Spec C.ring) (a : Spec A ⟶ S) (h : b ≫ C.projection = a) :
    ∃ M : AffineParabolicFaceModel ((baseChange a).map p),
      ∀ d, SubgroupFunctor.range
        ((baseChange b).map (C.termInclusion d) ≫
          (Descent.pullbackComparison C.projection b a h G).hom) =
        M.terms d := by
  let : Algebra C.ring A := (Spec.preimage b).hom.toAlgebra
  have hb : algebraBaseMap C.ring A = b := Spec.map_preimage b
  let F (q : Spec A ⟶ Spec C.ring) : Prop :=
    ∀ (a : Spec A ⟶ S) (h : q ≫ C.projection = a),
      ∃ M : AffineParabolicFaceModel ((baseChange a).map p),
        ∀ d, SubgroupFunctor.range
          ((baseChange q).map (C.termInclusion d) ≫
            (Descent.pullbackComparison C.projection q a h G).hom) =
          M.terms d
  have hcoeff : F (algebraBaseMap C.ring A) := by
    intro a h
    subst a
    exact C.exists_coefficientRestrictionModel A hG
  exact (Eq.mp (congrArg F hb) hcoeff) a h

end AffineParabolicFaceChart
end Langlands.GroupScheme.RelativeLevi

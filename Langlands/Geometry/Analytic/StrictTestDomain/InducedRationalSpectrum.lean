import Langlands.Geometry.Analytic.StrictTestDomain.OpenSubgroupTransport
import Langlands.Topology.GroupAction.InducedSpace

/-! # Actual induced rational quotient spectra -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory Topology

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {ρ : RationalSpectralAction G P}

namespace OpenSubgroupTransport

/-- The actual ambient spectrum, indexed by its specified operator action. -/
def AmbientSpectrum (_ρ : RationalSpectralAction G P) := BanachSpectrum P

instance : TopologicalSpace (AmbientSpectrum ρ) :=
  inferInstanceAs (TopologicalSpace (BanachSpectrum P))

instance : MulAction G (AmbientSpectrum ρ) :=
  MulAction.compHom (BanachSpectrum P) ρ.toMonoidHom

instance : ContinuousSMul G (AmbientSpectrum ρ) where
  continuous_smul := ρ.continuous_globalSpectrumAction

variable (X : ρ.OpenSubgroupTransport)

/-- The actual rational quotient spectrum with its specified subgroup action. -/
def LocalSpectrum := BanachSpectrum X.domain.obj.algebra

instance : TopologicalSpace X.LocalSpectrum :=
  inferInstanceAs (TopologicalSpace (BanachSpectrum X.domain.obj.algebra))

instance localSpectrumMulAction : MulAction X.subgroup X.LocalSpectrum :=
  MulAction.compHom (BanachSpectrum X.domain.obj.algebra)
    ((ρ.sectionAction X.domain.obj).comp
      (ρ.invariantStabilizerInclusion X.subgroup X.domain).toMonoidHom)

instance localSpectrumSubgroupMulAction :
    MulAction X.subgroup.toSubgroup X.LocalSpectrum := localSpectrumMulAction X

instance localSpectrumContinuousSMul : ContinuousSMul X.subgroup X.LocalSpectrum where
  continuous_smul :=
    ((rationalSpectralLocalContinuity K P G ρ X.domain.obj).2.2).comp
      (((ρ.invariantStabilizerInclusion X.subgroup X.domain).continuous.comp
        continuous_fst).prodMk continuous_snd)

instance localSpectrumSubgroupContinuousSMul :
    ContinuousSMul X.subgroup.toSubgroup X.LocalSpectrum := localSpectrumContinuousSMul X

/-- The balanced quotient of the actual quotient spectrum. -/
abbrev InducedSpectrum :=
  TopologicalInduction.Space X.subgroup.toSubgroup X.LocalSpectrum

/-- A class in the actual balanced quotient. -/
def inducedMk (g : G) (x : X.LocalSpectrum) : X.InducedSpectrum :=
  TopologicalInduction.mk X.subgroup.toSubgroup g x

/-- The distinguished actual quotient spectrum inside the induced space. -/
def inducedUnit : C(X.LocalSpectrum, X.InducedSpectrum) :=
  ⟨TopologicalInduction.unit X.subgroup.toSubgroup,
    TopologicalInduction.continuous_unit⟩

theorem isOpenEmbedding_inducedUnit : IsOpenEmbedding X.inducedUnit :=
  TopologicalInduction.isOpenEmbedding_unit X.subgroup.isOpen'

@[simp]
theorem inducedMk_smul (a g : G) (x : X.LocalSpectrum) :
    a • X.inducedMk g x = X.inducedMk (a * g) x :=
  TopologicalInduction.smul_mk a g x

@[simp]
theorem inducedUnit_smul (h : X.subgroup) (x : X.LocalSpectrum) :
    X.inducedUnit (h • x) = (h : G) • X.inducedUnit x :=
  TopologicalInduction.unit_subgroup_smul h x

/-- The actual structural spectrum map before induction. -/
def localToAmbient : C(X.LocalSpectrum, AmbientSpectrum ρ) :=
  BanachSpectrum.comapContinuous X.domain.obj.baseMap.toBoundedRingHom

theorem localToAmbient_smul (h : X.subgroup) (x : X.LocalSpectrum) :
    X.localToAmbient (h • x) = (h : G) • X.localToAmbient x :=
  ρ.spectrumMap_smul X.domain.obj
    (ρ.invariantStabilizerInclusion X.subgroup X.domain h) x

/-- The canonical full-group equivariant ambient map, constructed by descent. -/
def ambientMap : C(X.InducedSpectrum, AmbientSpectrum ρ) :=
  TopologicalInduction.extend X.localToAmbient X.localToAmbient_smul

@[simp]
theorem ambientMap_mk (g : G) (x : X.LocalSpectrum) :
    X.ambientMap (X.inducedMk g x) = g • X.localToAmbient x := rfl

@[simp]
theorem ambientMap_unit (x : X.LocalSpectrum) :
    X.ambientMap (X.inducedUnit x) = X.localToAmbient x :=
  TopologicalInduction.lift_unit X.localToAmbient X.localToAmbient_smul x

theorem ambientMap_smul (g : G) (z : X.InducedSpectrum) :
    X.ambientMap (g • z) = g • X.ambientMap z :=
  TopologicalInduction.lift_smul X.localToAmbient X.localToAmbient_smul g z

namespace Hom

variable {X Y Z : ρ.OpenSubgroupTransport}

/-- The existing bounded pullback, on the actual spectrum carriers. -/
def localSpectrumMap (f : X ⟶ Y) : C(X.LocalSpectrum, Y.LocalSpectrum) :=
  BanachSpectrum.comapContinuous f.restriction.toBoundedRingHom

theorem localSpectrumMap_smul (f : X ⟶ Y) (h : X.subgroup)
    (x : X.LocalSpectrum) :
    f.localSpectrumMap (h • x) = f.groupHom h • f.localSpectrumMap x :=
  f.spectrum_equivariant h x

@[simp]
theorem localSpectrumMap_id (X : ρ.OpenSubgroupTransport) (x : X.LocalSpectrum) :
    (𝟙 X : X ⟶ X).localSpectrumMap x = x := by
  change BanachSpectrum.comap (𝟙 X : X ⟶ X).restriction.toBoundedRingHom x = x
  rw [restriction_id]
  exact BanachSpectrum.ext fun _ => rfl

@[simp]
theorem localSpectrumMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (x : X.LocalSpectrum) :
    (f ≫ g).localSpectrumMap x = g.localSpectrumMap (f.localSpectrumMap x) := by
  change BanachSpectrum.comap (f ≫ g).restriction.toBoundedRingHom x = _
  rw [restriction_comp]
  exact BanachSpectrum.ext fun _ => rfl

theorem localSpectrumMap_over (f : X ⟶ Y) (x : X.LocalSpectrum) :
    Y.localToAmbient (f.localSpectrumMap x) = f.label • X.localToAmbient x :=
  f.spectrumMap_restriction x

/-- The label correction makes the seed equivariant for the source subgroup. -/
def inducedSeed (f : X ⟶ Y) : C(X.LocalSpectrum, Y.InducedSpectrum) :=
  ⟨fun x => f.label⁻¹ • Y.inducedUnit (f.localSpectrumMap x),
    (continuous_const_smul f.label⁻¹).comp
      (Y.inducedUnit.continuous.comp f.localSpectrumMap.continuous)⟩

theorem inducedSeed_smul (f : X ⟶ Y) (h : X.subgroup) (x : X.LocalSpectrum) :
    f.inducedSeed (h • x) = (h : G) • f.inducedSeed x := by
  change f.label⁻¹ • Y.inducedUnit (f.localSpectrumMap (h • x)) =
    (h : G) • (f.label⁻¹ • Y.inducedUnit (f.localSpectrumMap x))
  rw [f.localSpectrumMap_smul, Y.inducedUnit_smul, ← mul_smul, ← mul_smul]
  rw [groupHom_apply]
  simp [mul_assoc]

/-- The actual continuous full-group equivariant map on balanced quotients. -/
def inducedMap (f : X ⟶ Y) : C(X.InducedSpectrum, Y.InducedSpectrum) :=
  TopologicalInduction.extend f.inducedSeed f.inducedSeed_smul

@[simp]
theorem inducedMap_mk (f : X ⟶ Y) (a : G) (x : X.LocalSpectrum) :
    f.inducedMap (X.inducedMk a x) =
      Y.inducedMk (a * f.label⁻¹) (f.localSpectrumMap x) := by
  change a • (f.label⁻¹ • Y.inducedUnit (f.localSpectrumMap x)) = _
  rw [← mul_smul]
  exact TopologicalInduction.smul_unit _ _

theorem inducedMap_smul (f : X ⟶ Y) (g : G) (z : X.InducedSpectrum) :
    f.inducedMap (g • z) = g • f.inducedMap z :=
  TopologicalInduction.lift_smul f.inducedSeed f.inducedSeed_smul g z

@[simp]
theorem inducedMap_id (X : ρ.OpenSubgroupTransport) (z : X.InducedSpectrum) :
    (𝟙 X : X ⟶ X).inducedMap z = z := by
  induction z using Quotient.inductionOn with
  | h p =>
    change (𝟙 X : X ⟶ X).inducedMap (X.inducedMk p.1 p.2) = _
    simp
    rfl

@[simp]
theorem inducedMap_comp (f : X ⟶ Y) (g : Y ⟶ Z) (z : X.InducedSpectrum) :
    (f ≫ g).inducedMap z = g.inducedMap (f.inducedMap z) := by
  induction z using Quotient.inductionOn with
  | h p =>
    change (f ≫ g).inducedMap (X.inducedMk p.1 p.2) =
      g.inducedMap (f.inducedMap (X.inducedMk p.1 p.2))
    simp [mul_assoc]

/-- Every induced transport arrow lies over the identity of the ambient spectrum. -/
@[simp]
theorem ambientMap_inducedMap (f : X ⟶ Y) (z : X.InducedSpectrum) :
    Y.ambientMap (f.inducedMap z) = X.ambientMap z := by
  induction z using Quotient.inductionOn with
  | h p =>
    change Y.ambientMap (f.inducedMap (X.inducedMk p.1 p.2)) = _
    rw [inducedMap_mk, ambientMap_mk, localSpectrumMap_over, mul_smul,
      inv_smul_smul]
    rfl

end Hom

/-- The actual full-group action on the induced quotient as a categorical action. -/
def inducedSpectrumAction : Action TopCat.{max u v} G where
  V := TopCat.of X.InducedSpectrum
  ρ :=
    { toFun := fun g => TopCat.ofHom
        ⟨fun z => g • z, continuous_const_smul g⟩
      map_one' := by
        apply TopCat.ext
        intro z
        exact one_smul G z
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro z
        exact mul_smul g h z }

/-- Joint continuity is inherited from the constructed balanced quotient. -/
def inducedContinuousSpectrum : ContAction TopCat.{max u v} G :=
  ⟨X.inducedSpectrumAction, (Action.isContinuous_def _).mpr
    (show Continuous (fun p : G × X.InducedSpectrum => p.1 • p.2) from continuous_smul)⟩

/-- Actual balanced rational spectra and their transport maps form a diagram
of continuous actions of the full operator group. -/
def inducedSpectrumFunctor :
    ρ.OpenSubgroupTransport ⥤ ContAction TopCat.{max u v} G where
  obj X := X.inducedContinuousSpectrum
  map f := ObjectProperty.homMk
    { hom := TopCat.ofHom f.inducedMap
      comm := fun g => by
        apply TopCat.ext
        intro z
        exact f.inducedMap_smul g z }
  map_id X := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    exact Hom.inducedMap_id X
  map_comp f g := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    exact Hom.inducedMap_comp f g

/-- Forget the full-group actions while retaining the actual induced spaces. -/
def inducedTopologicalSpaceFunctor :
    ρ.OpenSubgroupTransport ⥤ TopCat.{max u v} :=
  inducedSpectrumFunctor ⋙ forget₂ _ TopCat

end OpenSubgroupTransport

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

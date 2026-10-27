import Langlands.Geometry.Analytic.StrictTestDomain.SpectralOverBase

/-! # Common open stabilizers and subgroup restriction of rational spectra -/

noncomputable section

universe u v w w'

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- The actual intersection of the open setwise stabilizers of a finite family
of rational loci. The finite index type may have any universe or be empty. -/
def finiteLocusOpenSubgroup {I : Type w} [Finite I] (D : I → RationalData K P) :
    OpenSubgroup G :=
  OpenSubgroup.iInfOfFinite (fun i => ρ.locusOpenSubgroup (D i))

@[simp]
theorem mem_finiteLocusOpenSubgroup {I : Type w} [Finite I]
    (D : I → RationalData K P) (g : G) :
    g ∈ ρ.finiteLocusOpenSubgroup D ↔ ∀ i, g ∈ ρ.locusOpenSubgroup (D i) := by
  change g ∈ (⨅ i, (ρ.locusOpenSubgroup (D i)).toSubgroup) ↔ _
  exact Subgroup.mem_iInf

/-- This is the largest open subgroup preserving every locus of the family. -/
theorem le_finiteLocusOpenSubgroup_iff {I : Type w} [Finite I]
    (D : I → RationalData K P) (V : OpenSubgroup G) :
    V ≤ ρ.finiteLocusOpenSubgroup D ↔ ∀ i, V ≤ ρ.locusOpenSubgroup (D i) := by
  constructor
  · intro h i g hg
    exact (ρ.mem_finiteLocusOpenSubgroup D g).mp (h hg) i
  · intro h g hg
    exact (ρ.mem_finiteLocusOpenSubgroup D g).mpr (fun i => h i hg)

@[simp]
theorem finiteLocusOpenSubgroup_empty {I : Type w} [Finite I] [IsEmpty I]
    (D : I → RationalData K P) : ρ.finiteLocusOpenSubgroup D = ⊤ := by
  ext g
  simp

/-- Shrink a prescribed open subgroup to preserve every locus of a finite family. -/
def finiteFamilyOpenSubgroup (U : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → RationalData K P) : OpenSubgroup G :=
  U ⊓ ρ.finiteLocusOpenSubgroup D

@[simp]
theorem mem_finiteFamilyOpenSubgroup (U : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → RationalData K P) (g : G) :
    g ∈ ρ.finiteFamilyOpenSubgroup U D ↔
      g ∈ U ∧ ∀ i, g ∈ ρ.locusOpenSubgroup (D i) := by
  simp [finiteFamilyOpenSubgroup]

theorem finiteFamilyOpenSubgroup_le (U : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → RationalData K P) : ρ.finiteFamilyOpenSubgroup U D ≤ U :=
  inf_le_left

theorem finiteFamilyOpenSubgroup_le_stabilizer (U : OpenSubgroup G)
    {I : Type w} [Finite I] (D : I → RationalData K P) (i : I) :
    ρ.finiteFamilyOpenSubgroup U D ≤ ρ.locusOpenSubgroup (D i) :=
  inf_le_right.trans (OpenSubgroup.iInfOfFinite_le _ i)

/-- The constructed subgroup is largest among the subgroups of U preserving
every member of the finite family. -/
theorem le_finiteFamilyOpenSubgroup_iff (U V : OpenSubgroup G)
    {I : Type w} [Finite I] (D : I → RationalData K P) :
    V ≤ ρ.finiteFamilyOpenSubgroup U D ↔
      V ≤ U ∧ ∀ i, V ≤ ρ.locusOpenSubgroup (D i) := by
  rw [finiteFamilyOpenSubgroup, le_inf_iff, le_finiteLocusOpenSubgroup_iff]

@[simp]
theorem finiteFamilyOpenSubgroup_empty (U : OpenSubgroup G)
    {I : Type w} [Finite I] [IsEmpty I] (D : I → RationalData K P) :
    ρ.finiteFamilyOpenSubgroup U D = U := by
  simp [finiteFamilyOpenSubgroup]

/-- The continuous inclusion of one open subgroup into another. -/
def openSubgroupInclusion {U V : OpenSubgroup G} (h : V ≤ U) : V →ₜ* U where
  toFun g := ⟨(g : G), h g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- A U-invariant rational domain is V-invariant whenever V is contained in U. -/
theorem invariantRationalProperty_le {U V : OpenSubgroup G} (h : V ≤ U) :
    ρ.invariantRationalProperty U ≤ ρ.invariantRationalProperty V :=
  fun _ hd => h.trans hd

/-- Change the group while retaining the actual rational presentations and
all their bounded restriction maps. -/
def invariantRestrictionFunctor {U V : OpenSubgroup G} (h : V ≤ U) :
    ρ.InvariantRationalDomain U ⥤ ρ.InvariantRationalDomain V :=
  ObjectProperty.ιOfLE (ρ.invariantRationalProperty_le h)

/-- The subgroup-change functor retains exactly the original inclusion homs. -/
def invariantRestrictionFullyFaithful {U V : OpenSubgroup G} (h : V ≤ U) :
    (ρ.invariantRestrictionFunctor h).FullyFaithful :=
  ObjectProperty.fullyFaithfulιOfLE _

@[simp]
theorem invariantRestrictionFunctor_obj_obj {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    ((ρ.invariantRestrictionFunctor h).obj d).obj = d.obj :=
  rfl

@[simp]
theorem invariantRestrictionFunctor_forget {U V : OpenSubgroup G} (h : V ≤ U) :
    ρ.invariantRestrictionFunctor h ⋙ (ρ.invariantRationalProperty V).ι =
      (ρ.invariantRationalProperty U).ι :=
  rfl

@[simp]
theorem invariantRestrictionFunctor_id (U : OpenSubgroup G) :
    ρ.invariantRestrictionFunctor (le_refl U) = 𝟭 (ρ.InvariantRationalDomain U) :=
  rfl

@[simp]
theorem invariantRestrictionFunctor_comp {U V W : OpenSubgroup G}
    (h : V ≤ U) (k : W ≤ V) :
    ρ.invariantRestrictionFunctor h ⋙ ρ.invariantRestrictionFunctor k =
      ρ.invariantRestrictionFunctor (k.trans h) :=
  rfl

/-- The actual rational spectrum diagram commutes with restriction of continuous
actions along the continuous subgroup inclusion. -/
theorem invariantSpectrumFunctor_restrict {U V : OpenSubgroup G} (h : V ≤ U) :
    ρ.invariantRestrictionFunctor h ⋙ ρ.invariantSpectrumFunctor V =
      ρ.invariantSpectrumFunctor U ⋙
        ContAction.res TopCat.{u} (openSubgroupInclusion h) :=
  rfl

/-- The restricted global spectrum is compatible with a second subgroup change. -/
theorem restrictedGlobalSpectrum_restrict {U V : OpenSubgroup G} (h : V ≤ U) :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).obj
        (ρ.restrictedGlobalSpectrum U) = ρ.restrictedGlobalSpectrum V :=
  rfl

/-- The actual equivariant structural maps agree under subgroup restriction. -/
theorem invariantSpectrumToBase_restrict {U V : OpenSubgroup G} (h : V ≤ U)
    (d : ρ.InvariantRationalDomain U) :
    (ContAction.res TopCat.{u} (openSubgroupInclusion h)).map
        (ρ.invariantSpectrumToBase U d) =
      ρ.invariantSpectrumToBase V ((ρ.invariantRestrictionFunctor h).obj d) :=
  rfl

/-- Every finite diagram of actual rational domains lifts after shrinking any
prescribed open subgroup to the constructed common locus stabilizer. -/
def finiteInvariantDiagram (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalData K P) :
    J ⥤ ρ.InvariantRationalDomain (ρ.finiteFamilyOpenSubgroup U F.obj) :=
  ObjectProperty.lift _ F (fun j =>
    ρ.finiteFamilyOpenSubgroup_le_stabilizer U F.obj j)

/-- Forgetting the common invariance recovers the input rational diagram exactly. -/
@[simp]
theorem finiteInvariantDiagram_forget (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalData K P) :
    ρ.finiteInvariantDiagram U F ⋙
        (ρ.invariantRationalProperty (ρ.finiteFamilyOpenSubgroup U F.obj)).ι = F :=
  rfl

/-- A finite rational diagram gives a diagram of actual continuous equivariant
quotient spectra over the restricted global spectrum. -/
def finiteInvariantSpectrumOverDiagram (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalData K P) :
    J ⥤ Over (ρ.restrictedGlobalSpectrum (ρ.finiteFamilyOpenSubgroup U F.obj)) :=
  ρ.finiteInvariantDiagram U F ⋙
    ρ.invariantSpectrumOverFunctor (ρ.finiteFamilyOpenSubgroup U F.obj)

/-- The constructed finite equivariant diagram retains the actual quotient
spectra and the continuous maps induced by the input bounded restrictions. -/
@[simp]
theorem finiteInvariantSpectrumOverDiagram_forget (U : OpenSubgroup G)
    {J : Type w} [Category.{w'} J] [Finite J] (F : J ⥤ RationalData K P) :
    ρ.finiteInvariantSpectrumOverDiagram U F ⋙
        Over.forget (ρ.restrictedGlobalSpectrum (ρ.finiteFamilyOpenSubgroup U F.obj)) ⋙
        forget₂ _ TopCat.{u} = F ⋙ RationalData.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

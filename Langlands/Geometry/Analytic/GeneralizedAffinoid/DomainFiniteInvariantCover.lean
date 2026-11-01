import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainInvariantLocus

/-! # Common open stabilizers and finite equivariant spectrum quotient covers -/

noncomputable section

universe u v w

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory Topology

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The actual intersection of the open locus stabilizers of a finite family.
The finite index type may have any universe and may be empty. -/
def finiteLocusOpenSubgroup {I : Type w} [Finite I] (D : I → Domain K P) :
    OpenSubgroup G :=
  OpenSubgroup.iInfOfFinite (fun i => ρ.locusOpenSubgroup (D i))

@[simp]
theorem mem_finiteLocusOpenSubgroup {I : Type w} [Finite I]
    (D : I → Domain K P) (g : G) :
    g ∈ ρ.finiteLocusOpenSubgroup D ↔ ∀ i, g ∈ ρ.locusOpenSubgroup (D i) := by
  change g ∈ (⨅ i, (ρ.locusOpenSubgroup (D i)).toSubgroup) ↔ _
  exact Subgroup.mem_iInf

theorem le_finiteLocusOpenSubgroup_iff {I : Type w} [Finite I]
    (D : I → Domain K P) (J : OpenSubgroup G) :
    J ≤ ρ.finiteLocusOpenSubgroup D ↔ ∀ i, J ≤ ρ.locusOpenSubgroup (D i) := by
  constructor
  · intro h i g hg
    exact (ρ.mem_finiteLocusOpenSubgroup D g).mp (h hg) i
  · intro h g hg
    exact (ρ.mem_finiteLocusOpenSubgroup D g).mpr (fun i => h i hg)

@[simp]
theorem finiteLocusOpenSubgroup_empty {I : Type w} [Finite I] [IsEmpty I]
    (D : I → Domain K P) : ρ.finiteLocusOpenSubgroup D = ⊤ := by
  ext g
  simp

/-- Shrink a prescribed open subgroup to preserve every actual represented locus. -/
def finiteFamilyOpenSubgroup (H : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → Domain K P) : OpenSubgroup G :=
  H ⊓ ρ.finiteLocusOpenSubgroup D

@[simp]
theorem mem_finiteFamilyOpenSubgroup (H : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → Domain K P) (g : G) :
    g ∈ ρ.finiteFamilyOpenSubgroup H D ↔
      g ∈ H ∧ ∀ i, g ∈ ρ.locusOpenSubgroup (D i) := by
  simp [finiteFamilyOpenSubgroup]

theorem finiteFamilyOpenSubgroup_le (H : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → Domain K P) : ρ.finiteFamilyOpenSubgroup H D ≤ H :=
  inf_le_left

theorem finiteFamilyOpenSubgroup_le_stabilizer (H : OpenSubgroup G)
    {I : Type w} [Finite I] (D : I → Domain K P) (i : I) :
    ρ.finiteFamilyOpenSubgroup H D ≤ ρ.locusOpenSubgroup (D i) :=
  inf_le_right.trans (OpenSubgroup.iInfOfFinite_le _ i)

/-- The constructed subgroup is largest inside H preserving the entire family. -/
theorem le_finiteFamilyOpenSubgroup_iff (H J : OpenSubgroup G)
    {I : Type w} [Finite I] (D : I → Domain K P) :
    J ≤ ρ.finiteFamilyOpenSubgroup H D ↔
      J ≤ H ∧ ∀ i, J ≤ ρ.locusOpenSubgroup (D i) := by
  rw [finiteFamilyOpenSubgroup, le_inf_iff, le_finiteLocusOpenSubgroup_iff]

@[simp]
theorem finiteFamilyOpenSubgroup_empty (H : OpenSubgroup G)
    {I : Type w} [Finite I] [IsEmpty I] (D : I → Domain K P) :
    ρ.finiteFamilyOpenSubgroup H D = H := by
  simp [finiteFamilyOpenSubgroup]

/-- Keep each full representation as an object invariant under the common subgroup. -/
def finiteInvariantFamily (H : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → Domain K P) (i : I) :
    ρ.InvariantDomain (ρ.finiteFamilyOpenSubgroup H D) :=
  ⟨D i, ρ.finiteFamilyOpenSubgroup_le_stabilizer H D i⟩

@[simp]
theorem finiteInvariantFamily_obj (H : OpenSubgroup G) {I : Type w} [Finite I]
    (D : I → Domain K P) (i : I) :
    (ρ.finiteInvariantFamily H D i).obj = D i :=
  rfl

/-- The target retains its representation after shrinking the acting subgroup. -/
def finiteInvariantTarget (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    {I : Type w} [Finite I] (D : I → Domain K P) :
    ρ.InvariantDomain (ρ.finiteFamilyOpenSubgroup H D) :=
  ⟨d.obj, (ρ.finiteFamilyOpenSubgroup_le H D).trans d.property⟩

@[simp]
theorem finiteInvariantTarget_obj (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    {I : Type w} [Finite I] (D : I → Domain K P) :
    (ρ.finiteInvariantTarget H d D).obj = d.obj :=
  rfl

/-- Every input bounded restriction is retained as an invariant-domain arrow. -/
def finiteInvariantFamilyArrow (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    {I : Type w} [Finite I] (D : I → Domain K P) (f : ∀ i, D i ⟶ d.obj) (i : I) :
    ρ.finiteInvariantFamily H D i ⟶ ρ.finiteInvariantTarget H d D :=
  ObjectProperty.homMk (f i)

@[simp]
theorem finiteInvariantFamilyArrow_hom (H : OpenSubgroup G) (d : ρ.InvariantDomain H)
    {I : Type w} [Finite I] (D : I → Domain K P) (f : ∀ i, D i ⟶ d.obj) (i : I) :
    (ρ.finiteInvariantFamilyArrow H d D f i).hom = f i :=
  rfl

variable (H : OpenSubgroup G) (d : ρ.InvariantDomain H) (c : Domain.FiniteCover d.obj)

/-- The actual section-spectrum action on one member of the unchanged cover. -/
def finiteCoverComponentAction (i : Fin c.size) :
    Action TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj) :=
  (ρ.invariantSpectrumActionFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).obj
    (ρ.finiteInvariantFamily H c.obj i)

/-- The component's structural quotient followed by the original locus inclusion. -/
def finiteCoverComponent (i : Fin c.size) :
    ρ.finiteCoverComponentAction H d c i ⟶
      ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) :=
  ρ.invariantSpectrumToLocus (ρ.finiteFamilyOpenSubgroup H c.obj)
      (ρ.finiteInvariantFamily H c.obj i) ≫
    (ρ.invariantLocusActionFunctor (ρ.finiteFamilyOpenSubgroup H c.obj)).map
      (ρ.finiteInvariantFamilyArrow H d c.obj c.map i)

@[simp]
theorem finiteCoverComponent_apply (i : Fin c.size)
    (x : BanachSpectrum (c.obj i).algebra) :
    (ρ.finiteCoverComponent H d c i).hom x = c.componentMap i x :=
  rfl

/-- The action on the finite disjoint union preserves each component and uses
the constructed inverse bounded section pullback there. -/
def finiteCoverSpectrumAction :
    Action TopCat.{u} (ρ.finiteFamilyOpenSubgroup H c.obj) where
  V := TopCat.of (Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        { toFun := fun x => ⟨x.1,
            ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c x.1).ρ g) x.2⟩
          continuous_toFun := continuous_sigma fun i =>
            continuous_sigmaMk.comp
              ((ρ.finiteCoverComponentAction H d c i).ρ g).hom.continuous }
      map_one' := by
        apply TopCat.ext
        rintro ⟨i, x⟩
        change (⟨i, ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ 1) x⟩ :
          Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) = ⟨i, x⟩
        rw [map_one]
        rfl
      map_mul' := by
        intro g h
        apply TopCat.ext
        rintro ⟨i, x⟩
        change (⟨i, ConcreteCategory.hom
          ((ρ.finiteCoverComponentAction H d c i).ρ (g * h)) x⟩ :
            Σ i : Fin c.size, BanachSpectrum (c.obj i).algebra) =
          ⟨i, ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ g)
            (ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ h) x)⟩
        rw [map_mul]
        rfl }

@[simp]
theorem finiteCoverSpectrumAction_mk (g : ρ.finiteFamilyOpenSubgroup H c.obj)
    (i : Fin c.size) (x : BanachSpectrum (c.obj i).algebra) :
    ConcreteCategory.hom ((ρ.finiteCoverSpectrumAction H d c).ρ g) ⟨i, x⟩ =
      Sigma.mk i
        (ConcreteCategory.hom ((ρ.finiteCoverComponentAction H d c i).ρ g) x) :=
  rfl

/-- The actual finite spectrum quotient is an equivariant map to the target
represented locus with its restricted ambient action. -/
def finiteCoverQuotient :
    ρ.finiteCoverSpectrumAction H d c ⟶
      ρ.invariantLocusAction (ρ.finiteFamilyOpenSubgroup H c.obj)
        (ρ.finiteInvariantTarget H d c.obj) where
  hom := TopCat.ofHom c.totalMap
  comm g := by
    apply TopCat.ext
    rintro ⟨i, x⟩
    exact ConcreteCategory.congr_hom ((ρ.finiteCoverComponent H d c i).comm g) x

@[simp]
theorem finiteCoverQuotient_hom :
    (ρ.finiteCoverQuotient H d c).hom = TopCat.ofHom c.totalMap :=
  rfl

theorem finiteCoverQuotient_surjective :
    Function.Surjective (ρ.finiteCoverQuotient H d c).hom :=
  c.totalMap_surjective

theorem finiteCoverQuotient_isClosedMap :
    IsClosedMap (ρ.finiteCoverQuotient H d c).hom :=
  c.totalMap_isClosedMap

theorem finiteCoverQuotient_isQuotientMap :
    IsQuotientMap (ρ.finiteCoverQuotient H d c).hom :=
  c.totalMap_isQuotientMap

/-- The exact quotient topology can be detected on the unchanged components. -/
theorem finiteCoverQuotient_isOpen_iff (s : Set d.obj.locus) :
    IsOpen s ↔ ∀ i, IsOpen ((ρ.finiteCoverComponent H d c i).hom ⁻¹' s) :=
  c.isOpen_iff s

theorem finiteCoverQuotient_isClosed_iff (s : Set d.obj.locus) :
    IsClosed s ↔ ∀ i, IsClosed ((ρ.finiteCoverComponent H d c i).hom ⁻¹' s) :=
  c.isClosed_iff s

/-- Continuity out of the target is detected on the equivariant cover components,
with no equivariance condition on the map being tested. -/
theorem finiteCoverQuotient_continuous_iff {Y : Type w} [TopologicalSpace Y]
    (f : d.obj.locus → Y) :
    Continuous f ↔ ∀ i, Continuous (f ∘ (ρ.finiteCoverComponent H d c i).hom) :=
  c.continuous_iff f

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

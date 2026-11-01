import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralAction
import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory

/-! # Actual equivariant diagrams of invariant represented domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- The constructed local forward action extends the actual base action
as an equality of full bounded maps. -/
@[simp]
theorem sectionAction_comp_baseMap (d : Domain K P) (g : ρ.locusOpenSubgroup d) :
    (ρ.sectionAction d g).hom.comp d.baseMap =
      d.baseMap.comp (ρ.toMonoidHom (g : G)).hom := by
  apply BoundedAlgHom.ext
  exact ρ.sectionAction_baseMap d g

/-- Actual restrictions commute with section actions when the same group
element preserves both represented loci. -/
theorem sectionAction_restriction {d e : Domain K P} (f : d ⟶ e)
    (g : G) (hd : g ∈ ρ.locusOpenSubgroup d) (he : g ∈ ρ.locusOpenSubgroup e) :
    f.restriction.comp (ρ.sectionAction e ⟨g, he⟩).hom =
      (ρ.sectionAction d ⟨g, hd⟩).hom.comp f.restriction :=
  (stabilizerSectionMap_restriction f (ρ.toMonoidHom g) hd he).symm

/-- The actual structural spectrum map intertwines inverse pullback actions. -/
theorem spectrumMap_smul (d : Domain K P) (g : ρ.locusOpenSubgroup d)
    (x : BanachSpectrum d.algebra) :
    d.spectrumMap ((ρ.sectionAction d g) • x) =
      ρ.toMonoidHom (g : G) • d.spectrumMap x :=
  stabilizerSectionAction_spectrumMap d (ρ.stabilizerHom d g) x

/-- Domains whose actual represented loci are preserved by every element of H. -/
def invariantDomainProperty (H : OpenSubgroup G) : ObjectProperty (Domain K P) :=
  fun d => H ≤ ρ.locusOpenSubgroup d

/-- The full category of represented domains invariant under a common open subgroup. -/
abbrev InvariantDomain (H : OpenSubgroup G) :=
  (ρ.invariantDomainProperty H).FullSubcategory

/-- The continuous inclusion of the common group into the local open stabilizer. -/
def invariantStabilizerInclusion (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    H →ₜ* ρ.locusOpenSubgroup d.obj where
  toFun g := ⟨(g : G), d.property g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- The common subgroup acts by the constructed bounded automorphisms on each
actual represented section algebra. -/
def invariantSectionAction (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    H →* Aut d.obj.algebra :=
  (ρ.sectionAction d.obj).comp (ρ.invariantStabilizerInclusion H d).toMonoidHom

@[simp]
theorem invariantSectionAction_baseMap (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (g : H) (a : P) :
    (ρ.invariantSectionAction H d g).hom.toAlgHom (d.obj.baseMap a) =
      d.obj.baseMap ((ρ.toMonoidHom (g : G)).hom.toAlgHom a) :=
  ρ.sectionAction_baseMap d.obj (ρ.invariantStabilizerInclusion H d g) a

/-- Restriction is equivariant as an equality of full bounded algebra maps. -/
theorem invariantSectionAction_restriction (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e) (g : H) :
    f.hom.restriction.comp (ρ.invariantSectionAction H e g).hom =
      (ρ.invariantSectionAction H d g).hom.comp f.hom.restriction :=
  ρ.sectionAction_restriction f.hom g _ _

/-- In geometric direction the actual section algebra carries the inverse
of its forward bounded automorphism action. -/
def invariantAffinoidAction (H : OpenSubgroup G) (d : ρ.InvariantDomain H) :
    Action (PresentedAffinoidSpace K) H where
  V := Opposite.op d.obj.algebra
  ρ :=
    { toFun := fun g => Quiver.Hom.op (ρ.invariantSectionAction H d g).inv
      map_one' := by
        rw [map_one]
        rfl
      map_mul' := fun g h => by
        rw [map_mul]
        rfl }

/-- The full invariant domain category is realized by actual geometric
affinoid actions and their bounded restrictions. -/
def invariantAffinoidActionFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Action (PresentedAffinoidSpace K) H where
  obj d := ρ.invariantAffinoidAction H d
  map f :=
    { hom := Quiver.Hom.op f.hom.restriction
      comm := fun g => by
        apply Quiver.Hom.unop_inj
        change (ρ.invariantSectionAction H _ g).inv.comp f.hom.restriction =
          f.hom.restriction.comp (ρ.invariantSectionAction H _ g).inv
        have heq := ρ.invariantSectionAction_restriction H f g⁻¹
        rw [map_inv, map_inv] at heq
        exact heq.symm }
  map_id _ := by
    apply Action.Hom.ext
    rfl
  map_comp _ _ := by
    apply Action.Hom.ext
    rfl

/-- Forgetting the group action recovers the actual represented-domain
affinoid realization, including its bounded maps. -/
@[simp]
theorem invariantAffinoidActionFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantAffinoidActionFunctor H ⋙ Action.forget (PresentedAffinoidSpace K) H =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.toAffinoidSpace K P :=
  rfl

/-- Actual spectra and bounded pullbacks form an equivariant topological-space
diagram. Each group element acts continuously; joint continuity is separate. -/
def invariantSpectrumActionFunctor (H : OpenSubgroup G) :
    ρ.InvariantDomain H ⥤ Action TopCat.{u} H :=
  ρ.invariantAffinoidActionFunctor H ⋙ (affinoidSpectrumFunctor K).mapAction H

@[simp]
theorem invariantSpectrumActionFunctor_obj_apply (H : OpenSubgroup G)
    (d : ρ.InvariantDomain H) (g : H) (x : BanachSpectrum d.obj.algebra)
    (b : d.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (((ρ.invariantSpectrumActionFunctor H).obj d).ρ g) x) b =
        x ((ρ.invariantSectionAction H d g).inv.toAlgHom b) :=
  rfl

@[simp]
theorem invariantSpectrumActionFunctor_map_apply (H : OpenSubgroup G)
    {d e : ρ.InvariantDomain H} (f : d ⟶ e)
    (x : BanachSpectrum d.obj.algebra) (b : e.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.invariantSpectrumActionFunctor H).map f).hom x) b =
        x (f.hom.restriction b) :=
  rfl

/-- The underlying topological diagram is exactly the published actual
represented-domain spectrum realization. -/
@[simp]
theorem invariantSpectrumActionFunctor_forget (H : OpenSubgroup G) :
    ρ.invariantSpectrumActionFunctor H ⋙ Action.forget TopCat.{u} H =
      (ρ.invariantDomainProperty H).ι ⋙ Domain.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

import Langlands.Geometry.Analytic.StrictTestDomain.SpectralLocalContinuityProof
import Langlands.Geometry.Analytic.NormContinuousAction

/-! # Continuous spectra of invariant rational domains -/

noncomputable section

universe u v

namespace Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

open CategoryTheory

attribute [local instance] NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedStrictAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : RationalSpectralAction G P)

/-- The actual inverse-pullback action of the open rational-locus stabilizer. -/
def spectrumAction (d : RationalData K P) :
    Action TopCat.{u} (ρ.locusOpenSubgroup d) where
  V := TopCat.of (BanachSpectrum d.algebra)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (ρ.sectionAction d g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change (ρ.sectionAction d 1) • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change (ρ.sectionAction d (g * h)) • x =
          (ρ.sectionAction d g) • ((ρ.sectionAction d h) • x)
        rw [map_mul, mul_smul] }

/-- Joint continuity follows from the published rational spectral theorem. -/
def spectrum (d : RationalData K P) :
    ContAction TopCat.{u} (ρ.locusOpenSubgroup d) :=
  ⟨ρ.spectrumAction d, (Action.isContinuous_def _).mpr
    ((rationalSpectralLocalContinuity K P G ρ d).2.2)⟩

@[simp]
theorem spectrum_apply (d : RationalData K P) (g : ρ.locusOpenSubgroup d)
    (x : BanachSpectrum d.algebra) (b : d.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom ((ρ.spectrum d).obj.ρ g) x) b =
        x ((ρ.sectionAction d g).inv.toAlgHom b) :=
  rfl

@[simp]
theorem sectionAction_comp_baseMap (d : RationalData K P) (g : ρ.locusOpenSubgroup d) :
    (ρ.sectionAction d g).hom.comp d.baseMap =
      d.baseMap.comp (ρ.toMonoidHom (g : G)).hom := by
  apply BoundedAlgHom.ext
  exact ρ.sectionAction_baseMap d g

/-- The actual map to the base spectrum intertwines inverse-pullback actions. -/
theorem spectrumMap_smul (d : RationalData K P) (g : ρ.locusOpenSubgroup d)
    (x : BanachSpectrum d.algebra) :
    d.spectrumMap ((ρ.sectionAction d g) • x) =
      ρ.toMonoidHom (g : G) • d.spectrumMap x := by
  apply BanachSpectrum.ext
  intro a
  have h := ρ.sectionAction_baseMap d (g⁻¹) a
  rw [map_inv] at h
  have hg : ρ.toMonoidHom ((g⁻¹ : ρ.locusOpenSubgroup d) : G) =
      (ρ.toMonoidHom (g : G))⁻¹ := by simp
  rw [hg] at h
  exact congrArg (fun b : d.algebra => x b) h

/-- Restriction between invariant rational loci commutes with the forward
section automorphisms, even for different chosen presentations. -/
theorem sectionAction_restriction {d e : RationalData K P} (h : d ⟶ e)
    (g : G) (hd : g ∈ ρ.locusOpenSubgroup d) (he : g ∈ ρ.locusOpenSubgroup e) :
    h.restriction.comp (ρ.sectionAction e ⟨g, he⟩).hom =
      (ρ.sectionAction d ⟨g, hd⟩).hom.comp h.restriction := by
  apply e.hom_ext
  rw [BoundedAlgHom.comp_assoc, sectionAction_comp_baseMap,
    ← BoundedAlgHom.comp_assoc, h.restriction_comp_baseMap,
    BoundedAlgHom.comp_assoc, h.restriction_comp_baseMap,
    sectionAction_comp_baseMap]

/-- Contravariant bounded restriction gives an equivariant spectrum map. -/
theorem spectrum_restriction_equivariant {d e : RationalData K P} (h : d ⟶ e)
    (g : G) (hd : g ∈ ρ.locusOpenSubgroup d) (he : g ∈ ρ.locusOpenSubgroup e)
    (x : BanachSpectrum d.algebra) :
    BanachSpectrum.comap h.restriction.toBoundedRingHom
        ((ρ.sectionAction d ⟨g, hd⟩) • x) =
      (ρ.sectionAction e ⟨g, he⟩) •
        BanachSpectrum.comap h.restriction.toBoundedRingHom x := by
  apply BanachSpectrum.ext
  intro a
  have ht := ρ.sectionAction_restriction h g⁻¹
    ((ρ.locusOpenSubgroup d).inv_mem hd) ((ρ.locusOpenSubgroup e).inv_mem he)
  change h.restriction.comp (ρ.sectionAction e (⟨g, he⟩⁻¹)).hom =
    (ρ.sectionAction d (⟨g, hd⟩⁻¹)).hom.comp h.restriction at ht
  rw [map_inv, map_inv] at ht
  exact congrArg (fun f : BoundedAlgHom K e.algebra d.algebra => x (f a)) ht.symm

/-- Rational domains whose actual loci are preserved by every element of U. -/
def invariantRationalProperty (U : OpenSubgroup G) :
    ObjectProperty (RationalData K P) :=
  fun d => U ≤ ρ.locusOpenSubgroup d

/-- The full inclusion category of rational presentations invariant under U. -/
abbrev InvariantRationalDomain (U : OpenSubgroup G) :=
  (ρ.invariantRationalProperty U).FullSubcategory

/-- The continuous inclusion into the domain's open locus stabilizer. -/
def invariantStabilizerInclusion (U : OpenSubgroup G)
    (d : ρ.InvariantRationalDomain U) : U →ₜ* ρ.locusOpenSubgroup d.obj where
  toFun g := ⟨(g : G), d.property g.property⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_subtype_val.subtype_mk _

/-- Restrict the actual local continuous spectrum action to the fixed subgroup. -/
def invariantSpectrum (U : OpenSubgroup G) (d : ρ.InvariantRationalDomain U) :
    ContAction TopCat.{u} U :=
  (ContAction.res TopCat.{u} (ρ.invariantStabilizerInclusion U d)).obj
    (ρ.spectrum d.obj)

/-- Actual quotient spectra and rational inclusions form a diagram of
continuous U-actions. -/
def invariantSpectrumFunctor (U : OpenSubgroup G) :
    ρ.InvariantRationalDomain U ⥤ ContAction TopCat.{u} U where
  obj d := ρ.invariantSpectrum U d
  map h := ObjectProperty.homMk
    { hom := TopCat.ofHom (BanachSpectrum.comapContinuous h.hom.restriction.toBoundedRingHom)
      comm := fun g => by
        apply TopCat.ext
        intro x
        exact ρ.spectrum_restriction_equivariant h.hom (g : G)
          _ _ x }
  map_id d := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    change BanachSpectrum.comap
      (𝟙 d.obj : d.obj ⟶ d.obj).restriction.toBoundedRingHom x = x
    rw [RationalData.Inclusion.restriction_id]
    exact BanachSpectrum.ext fun _ => rfl
  map_comp h k := by
    apply ObjectProperty.hom_ext _
    apply Action.Hom.ext
    apply TopCat.ext
    intro x
    change BanachSpectrum.comap
      (h.hom ≫ k.hom).restriction.toBoundedRingHom x = _
    rw [RationalData.Inclusion.restriction_comp]
    exact BanachSpectrum.ext fun _ => rfl

@[simp]
theorem invariantSpectrumFunctor_map_apply (U : OpenSubgroup G)
    {d e : ρ.InvariantRationalDomain U} (h : d ⟶ e)
    (x : BanachSpectrum d.obj.algebra) (b : e.obj.algebra) :
    BanachSpectrum.toMulRingSeminorm
      (((ρ.invariantSpectrumFunctor U).map h).hom.hom x) b =
        x (h.hom.restriction b) :=
  rfl

/-- Forgetting the actions recovers the published actual rational spectrum
diagram exactly, including its bounded restriction maps. -/
@[simp]
theorem invariantSpectrumFunctor_forget (U : OpenSubgroup G) :
    ρ.invariantSpectrumFunctor U ⋙ forget₂ _ TopCat.{u} =
      (ρ.invariantRationalProperty U).ι ⋙ RationalData.toTopologicalSpace K P :=
  rfl

end Langlands.Analytic.StrictTestDomain.RationalAutomorphism.RationalSpectralAction

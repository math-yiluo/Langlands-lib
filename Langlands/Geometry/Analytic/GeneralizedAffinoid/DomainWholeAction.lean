import Langlands.Geometry.Analytic.GeneralizedAffinoid.DomainSpectralAction

/-! # Whole-domain stabilizers and actual global spectrum actions -/

noncomputable section

universe u v

namespace Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

open CategoryTheory

attribute [local instance] Langlands.Analytic.NormContinuousAffinoidAction.topCatSelfForget

variable {K : Type u} [NormedField K] [IsUltrametricDist K] [CompleteSpace K]
  {P : PresentedAffinoidAlgebra K}
  {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  (ρ : DomainSpectralAction G P)

/-- Every actual bounded automorphism preserves the whole represented locus. -/
theorem mem_wholeLocusOpenSubgroup (g : G) :
    g ∈ ρ.locusOpenSubgroup (Domain.whole K P) := by
  rw [mem_locusOpenSubgroup]
  change (fun x : BanachSpectrum P => ρ.toMonoidHom g • x) '' Set.univ = Set.univ
  rw [Set.image_univ]
  exact Set.range_eq_univ.mpr (MulAction.surjective (ρ.toMonoidHom g))

/-- Continuous inclusion into the constructed stabilizer of the whole spectrum. -/
def wholeStabilizerHom : G →ₜ* ρ.locusOpenSubgroup (Domain.whole K P) where
  toFun g := ⟨g, ρ.mem_wholeLocusOpenSubgroup g⟩
  map_one' := rfl
  map_mul' _ _ := rfl
  continuous_toFun := continuous_id.subtype_mk _

@[simp]
theorem wholeStabilizerHom_coe (g : G) : (ρ.wholeStabilizerHom g : G) = g := rfl

/-- The whole domain uses the base algebra itself. Its section automorphism
therefore equals the original automorphism as a full bounded algebra map. -/
@[simp]
theorem sectionAction_whole (g : G) :
    ρ.sectionAction (Domain.whole K P) (ρ.wholeStabilizerHom g) =
      ρ.toMonoidHom g := by
  apply Aut.ext
  apply BoundedAlgHom.ext
  intro a
  exact ρ.sectionAction_baseMap (Domain.whole K P) (ρ.wholeStabilizerHom g) a

/-- The original inverse bounded maps supply the actual global action. -/
def globalSpectrumAction : Action TopCat.{u} G where
  V := TopCat.of (BanachSpectrum P)
  ρ :=
    { toFun := fun g => TopCat.ofHom
        (BanachSpectrum.comapContinuous (ρ.toMonoidHom g).inv.toBoundedRingHom)
      map_one' := by
        apply TopCat.ext
        intro x
        change ρ.toMonoidHom 1 • x = x
        simp
      map_mul' := by
        intro g h
        apply TopCat.ext
        intro x
        change ρ.toMonoidHom (g * h) • x =
          ρ.toMonoidHom g • (ρ.toMonoidHom h • x)
        rw [map_mul, mul_smul] }

@[simp]
theorem globalSpectrumAction_apply (g : G) (x : BanachSpectrum P) (a : P) :
    BanachSpectrum.toMulRingSeminorm
      (ConcreteCategory.hom (ρ.globalSpectrumAction.ρ g) x) a =
        x ((ρ.toMonoidHom g).inv.toAlgHom a) := rfl

end Langlands.Analytic.PresentedAffinoidAlgebra.DomainAutomorphism.DomainSpectralAction

import Langlands.BruhatTits.IntegralModels.TorusRootModelFamily
import Langlands.BruhatTits.IntegralModels.RootFiltrationModelComparison
import Langlands.Geometry.Building.RootFixerDepthClosure

/-! # Compatible comparisons of supplied torus/root model families -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.LocalGalois.Separable
open Langlands.Geometry.Building

namespace Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
  [IsNonarchimedeanLocalField F]
  {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
  [IsAffineHom G.X.hom]
  {C : MaximalUnramified.BuildingData F G} {E : UnramifiedZeroDatum F G}
  {x : C.Apartment} {Ω Ω' : Set C.Apartment}
  {N N' : IntegralModel (fixedFieldIntegers F) (inertiaFixedField F) G}
  (A : TorusRootModelFamilyData C E x Ω N)
  (B : TorusRootModelFamilyData C E x Ω' N')

/-- The torus factor is compatibly isomorphic because both exact point images
are the same torus Iwahori subgroup. The extension criterion is explicit. -/
def torusComparisonIso
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F)) :
    B.torusModel.Iso A.torusModel (CategoryTheory.Iso.refl E.T.toGrp) :=
  IntegralModel.isoOfIntegralPointsEq B.torusModel A.torusModel hext
    B.torusSmooth A.torusSmooth (B.torusPoints_eq.trans A.torusPoints_eq.symm)

/-- Canonical generic comparisons for the common torus/root index. -/
def genericComparisonIso : ∀ j, B.genericGroup j ≅ A.genericGroup j
  | none => CategoryTheory.Iso.refl _
  | some a => (B.rootModel a).genericIso (A.rootModel a)

theorem genericComparisonIso_hom_comp (j : Option (relativeRoots C.i)) :
    (A.genericComparisonIso B j).hom ≫ A.genericMap j = B.genericMap j := by
  cases j with
  | none => exact Category.id_comp _
  | some a => exact (B.rootModel a).genericIso_hom_comp (A.rootModel a)

/-- Every factor comparison is an actual model homomorphism under the
extension criterion and the supplied pointwise depth inequalities. -/
def comparisonHom
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hdepth : ∀ a : relativeRoots C.i,
      C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω') :
    ∀ j, (B.model j).Hom (A.model j) (A.genericComparisonIso B j).hom
  | none => (A.torusComparisonIso B hext).toHom
  | some a => (A.rootModel a).comparisonHom (B.rootModel a) hext (hdepth a)

/-- All factor comparisons commute with the supplied ambient model maps. -/
theorem comparisonHom_comp
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hdepth : ∀ a : relativeRoots C.i,
      C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω')
    (ψ : N'.Hom N (𝟙 G)) (j : Option (relativeRoots C.i)) :
    (A.comparisonHom B hext hdepth j).hom ≫ (A.modelMap j).hom =
      (B.modelMap j).hom ≫ ψ.hom := by
  cases j with
  | none =>
    change (A.torusComparisonIso B hext).iso.hom ≫ A.torusMap.hom =
      B.torusMap.hom ≫ ψ.hom
    apply IntegralModel.hom_eq_of_generic
    apply (cancel_mono N.genericIso.hom).mp
    simp only [CategoryTheory.Functor.map_comp, Category.assoc,
      A.torusMap.generic_comm, ψ.generic_comm, Category.comp_id]
    rw [← Category.assoc, (A.torusComparisonIso B hext).generic_comm]
    simp only [CategoryTheory.Iso.refl_hom, Category.comp_id]
    exact B.torusMap.generic_comm.symm
  | some a =>
    exact (A.rootModel a).comparisonHom_comp (B.rootModel a) hext (hdepth a)
      (A.rootMap a) (B.rootMap a) ψ

/-- Base change to the actual residue field preserves every compatibility
square. -/
theorem comparisonHom_specialFibre_comp
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hdepth : ∀ a : relativeRoots C.i,
      C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω')
    (ψ : N'.Hom N (𝟙 G)) (j : Option (relativeRoots C.i)) :
    (A.comparisonHom B hext hdepth j).specialFibreMap ≫
        (A.modelMap j).specialFibreMap =
      (B.modelMap j).specialFibreMap ≫ ψ.specialFibreMap := by
  unfold IntegralModel.Hom.specialFibreMap
  rw [← CategoryTheory.Functor.map_comp, A.comparisonHom_comp B hext hdepth ψ j,
    CategoryTheory.Functor.map_comp]

/-- The torus comparison remains an actual isomorphism on special fibres. -/
def torusSpecialFibreComparisonIso
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F)) :
    B.torusModel.specialFibre ≅ A.torusModel.specialFibre :=
  (GroupScheme.baseChange (IntegralModel.residueBaseMap (fixedFieldIntegers F))).mapIso
    (A.torusComparisonIso B hext).iso

@[simp] theorem torusSpecialFibreComparisonIso_hom
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hdepth : ∀ a : relativeRoots C.i,
      C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω') :
    (A.torusSpecialFibreComparisonIso B hext).hom =
      (A.comparisonHom B hext hdepth none).specialFibreMap := rfl

/-- Affine closure ordering supplies all the depth comparisons required by
the family maps. These are the literal closure hypotheses of the host target. -/
theorem rootDepth_le_of_subset_affineClosure
    (hne : Ω.Nonempty)
    (hbdd : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))
    (hcl : Ω ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω')
    (a : relativeRoots C.i) :
    C.apartment.rootFixerDepth a x Ω ≤ C.apartment.rootFixerDepth a x Ω' :=
  C.apartment.rootFixerDepth_le_of_subset_affineClosure a x hne
    (hbdd (-C.apartment.affineFunctional a x 0)) hcl

/-- Family maps for subsets ordered by the exact initial affine closure. -/
def comparisonHomOfClosure
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hne : Ω.Nonempty)
    (hbdd : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))
    (hcl : Ω ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω') :
    ∀ j, (B.model j).Hom (A.model j) (A.genericComparisonIso B j).hom :=
  A.comparisonHom B hext
    (rootDepth_le_of_subset_affineClosure hne hbdd hcl)

/-- The closure-specialized maps satisfy the same ambient compatibility. -/
theorem comparisonHomOfClosure_comp
    (hext : IntegralModel.HasSmoothHomExtension
      (R := fixedFieldIntegers F) (L := inertiaFixedField F))
    (hne : Ω.Nonempty)
    (hbdd : ∀ f : C.Apartment →ᵃ[ℝ] ℝ, BddAbove (f '' Ω'))
    (hcl : Ω ⊆ @closure C.Apartment
      (⨅ f : C.Apartment →ᵃ[ℝ] ℝ, TopologicalSpace.induced f inferInstance) Ω')
    (ψ : N'.Hom N (𝟙 G)) (j : Option (relativeRoots C.i)) :
    (A.comparisonHomOfClosure B hext hne hbdd hcl j).hom ≫ (A.modelMap j).hom =
      (B.modelMap j).hom ≫ ψ.hom :=
  A.comparisonHom_comp B hext _ ψ j

end Langlands.BruhatTits.IntegralModels.TorusRootModelFamilyData

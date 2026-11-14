import Langlands.BruhatTits.IntegralModels.UnramifiedIncidentRootSurvival
import Langlands.Geometry.Building.ApartmentIncidentRootDepth

/-! # Ordinary incident roots in an upper unramified reductive quotient -/

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.Geometry.Building
open Langlands.LocalGalois.Separable

namespace Langlands.BruhatTits.IntegralModels

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of (inertiaFixedField F)))}
    [IsAffineHom G.X.hom]
    (C : MaximalUnramified.BuildingData F G) (E : UnramifiedZeroDatum F G)
    (x : C.Apartment)
    (D : RelativeComponentModelData (fixedFieldIntegers F) (inertiaFixedField F) G)
    (hD : D.neutral.integralPoints =
      E.zeroPoints ⊓ C.pointwiseFixer (C.apartmentMap '' {x}))
    (hpositive : UnramifiedRootPositiveReductionStatement.{u})
    (T : IntegralTorusData D C.S C.i) (hT : IsSplitTorus T.torus.toGrp)
    (Q : SpecialFibreQuotientData D) (hQ : Q.IsReductiveQuotient)

private instance incidentQuotient_mono : Mono C.i.hom.hom.left :=
  mono_of_isMaximalSplitTorus C.isMaximalSplitTorus

include hD hpositive hT hQ

/-- Every ordinary affine root through the modeled point has an actual
quotient root with its exact canonically specialized derivative character. -/
theorem exists_unramified_quotient_root_of_incidentAffineRoot
    {ψ : C.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ C.affineRoots) (hx : ψ x = 0) :
    ∃ a : relativeRoots C.i, ψ.linear = rootForm C.i a ∧
      T.characterSpecialization hT a.val ∈
        relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  obtain ⟨a, hlin, g, -, hg⟩ :=
    C.apartment.exists_rootDepthBoundary_of_affineRoot hψ
  have hboundary : C.apartment.IsRootDepthBoundary x a 0 g := by
    simpa only [hx] using (hg x).1
  exact ⟨a, hlin, unramified_quotient_root_of_depth_boundary
    C E x D hD hpositive T hT Q hQ a g hboundary.1 hboundary.2⟩

/-- The prescribed derivative root, rather than merely some root with the
same real form, survives under canonical character specialization. -/
theorem unramified_quotient_root_of_incidentAffineRoot
    (a : relativeRoots C.i) {ψ : C.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ C.affineRoots) (hx : ψ x = 0)
    (hlin : ψ.linear = rootForm C.i a) :
    T.characterSpecialization hT a.val ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  obtain ⟨b, hb, hroot⟩ := exists_unramified_quotient_root_of_incidentAffineRoot
    C E x D hD hpositive T hT Q hQ hψ hx
  have hba : b = a :=
    Langlands.BruhatTits.SpecialCompact.rootForm_injective_of_split
      C.isMaximalSplitTorus.isSplitSubtorus.1 C.i (hb.symm.trans hlin)
  subst b
  exact hroot

/-- An ordinary root through another point also survives in the supplied
model at every point of that point's full sign facet. -/
theorem unramified_quotient_root_of_facet_incidentAffineRoot
    (a : relativeRoots C.i) {p : C.Apartment} {ψ : C.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ C.affineRoots) (hp : ψ p = 0)
    (hlin : ψ.linear = rootForm C.i a)
    (hx : x ∈ AffineRootSystem.facet C.affineRoots p) :
    T.characterSpecialization hT a.val ∈
      relativeRoots (T.specialFibreInclusion ≫ Q.projection) := by
  have hxzero : ψ x = 0 := by
    have hs := hx ψ hψ
    rw [hp, sign_zero] at hs
    exact sign_eq_zero_iff.mp hs.symm
  exact unramified_quotient_root_of_incidentAffineRoot
    C E x D hD hpositive T hT Q hQ a hψ hxzero hlin

/-- The quotient root of a prescribed incident derivative, with the exact
canonical specialized character. -/
def unramifiedIncidentQuotientRoot
    (a : relativeRoots C.i)
    (ha : ∃ ψ ∈ C.affineRoots, ψ x = 0 ∧ ψ.linear = rootForm C.i a) :
    relativeRoots (T.specialFibreInclusion ≫ Q.projection) :=
  ⟨T.characterSpecialization hT a.val, by
    obtain ⟨ψ, hψ, hx, hlin⟩ := ha
    exact unramified_quotient_root_of_incidentAffineRoot
      C E x D hD hpositive T hT Q hQ a hψ hx hlin⟩

@[simp] theorem unramifiedIncidentQuotientRoot_character
    (a : relativeRoots C.i)
    (ha : ∃ ψ ∈ C.affineRoots, ψ x = 0 ∧ ψ.linear = rootForm C.i a) :
    (unramifiedIncidentQuotientRoot C E x D hD hpositive T hT Q hQ a ha).val =
      T.characterSpecialization hT a.val := rfl

end Langlands.BruhatTits.IntegralModels

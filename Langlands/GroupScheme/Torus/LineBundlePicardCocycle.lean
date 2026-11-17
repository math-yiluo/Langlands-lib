import Langlands.AlgebraicGeometry.Modules.UnitCocyclePicardTrivial
import Langlands.GroupScheme.Torus.LocalCocycle
import Langlands.GroupScheme.CocycleAffineRefinement

/-! # Torus cocycles from triviality of actual line bundles -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.UnitCocycleDescent

set_option backward.isDefEq.respectTransparency false in
/-- Effective line-bundle descent turns the actual Picard hypothesis into a
unit primitive on an affine faithfully flat cover of any base scheme. -/
theorem exists_unit_coboundary_of_lineBundlesTrivial
    {S X : Scheme.{u}}
    (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
    (p : X ⟶ S) [IsAffineHom p] [Flat p] [Surjective p]
    (c : ∀ (Z : Scheme.{u}) (a b : Z ⟶ X), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ)
    (hnat : IsNatural p c) (hmul : IsMultiplicative p c) :
    ∃ q : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{u}) (a b : Z ⟶ X) (h : a ≫ p = b ≫ p),
      c Z a b h =
        Units.map a.appTop.hom.toMonoidHom q *
          (Units.map b.appTop.hom.toMonoidHom q)⁻¹ := by
  obtain ⟨L, α, hα⟩ := unitCocycleDescentEffective X S p
    inferInstance inferInstance inferInstance c hnat hmul
  obtain ⟨βL⟩ := hPic L
  let β : L.obj ≅ SheafOfModules.unit S.ringCatSheaf :=
    (LineBundle.forget S).mapIso βL
  let α₀ := (Scheme.Modules.pullback p).mapIso β ≪≫ pullbackUnitIso p
  let e := α₀.symm ≪≫ α
  refine ⟨(structureAutScalar e)⁻¹, fun Z a b h => ?_⟩
  have hcan : equalCompositeUnitAut p a b h α₀ = Iso.refl _ := by
    rw [show α₀ = (Scheme.Modules.pullback p).mapIso β ≪≫ pullbackUnitIso p from rfl,
      equalCompositeUnitAut_of_iso, equalCompositeUnitAut_pullbackUnitIso]
  have heq : α = α₀ ≪≫ e := by simp [e]
  have hrefl : structureAutScalar (Iso.refl (SheafOfModules.unit Z.ringCatSheaf)) =
      (1 : Γ(Z, ⊤)ˣ) := Units.ext rfl
  rw [← hα, heq, equalCompositeUnitAut_change, hcan]
  simp only [structureAutScalar_trans, structureAutScalar_symm,
    structureAutScalar_pullback, hrefl, one_mul, map_inv, inv_inv]

end Langlands.Scheme.Modules

namespace Langlands.GroupScheme.Cocycle

open Langlands.AlgebraicGeometry.Picard

variable {S : Scheme.{u}}
  (hPic : ∀ L : LineBundle S, Nonempty (L ≅ LineBundle.trivial S))
  {I : Type u} [Finite I] {U : Over S}
  (ξ : Cocycle (splitTorus S I) U)

section AffineCover

variable [IsAffineHom U.hom] [Flat U.hom] [Surjective U.hom]

/-- A chosen torus primitive using the actual line-bundle Picard hypothesis. -/
def splitLineBundlePicardCochain : U ⟶ (splitTorus S I).X :=
  (splitTorus.pointsEquiv I U).symm fun i =>
    Classical.choose
      (Langlands.Scheme.Modules.exists_unit_coboundary_of_lineBundlesTrivial
        hPic U.hom (ξ.unitCoordinate i)
        (ξ.unitCoordinate_isNatural i) (ξ.unitCoordinate_isMultiplicative i))

/-- The chosen cochain cobounds the cocycle on every test scheme over S. -/
theorem splitLineBundlePicardCochain_spec {Z : Over S} (a b : Z ⟶ U) :
    ξ.toFun a b = (a ≫ ξ.splitLineBundlePicardCochain hPic) *
      (b ≫ ξ.splitLineBundlePicardCochain hPic)⁻¹ := by
  apply (splitTorus.pointsEquiv I Z).injective
  funext i
  have h := Classical.choose_spec
    (Langlands.Scheme.Modules.exists_unit_coboundary_of_lineBundlesTrivial
      hPic U.hom (ξ.unitCoordinate i)
      (ξ.unitCoordinate_isNatural i) (ξ.unitCoordinate_isMultiplicative i))
    Z.left a.left b.left ((Over.w a).trans (Over.w b).symm)
  rw [ξ.unitCoordinate_eq i Z a.left b.left (Over.w a) (Over.w b)] at h
  rw [show (Over.homMk a.left (Over.w a) : Z ⟶ U) = a from by ext; rfl,
    show (Over.homMk b.left (Over.w b) : Z ⟶ U) = b from by ext; rfl] at h
  simpa [splitTorus.pointsEquiv_naturality, splitLineBundlePicardCochain,
    splitTorus.unitsRestrict] using h

include hPic in
/-- Actual line-bundle triviality kills split-torus cocycles on an affine
faithfully flat morphism over any scheme. -/
theorem isTrivial_split_of_lineBundlesTrivial : ξ.IsTrivial :=
  ⟨ξ.splitLineBundlePicardCochain hPic, ξ.splitLineBundlePicardCochain_spec hPic⟩

end AffineCover

include hPic in
/-- On an affine base the same vanishing holds on every single fppf cover. -/
theorem isTrivial_split_fppf_of_lineBundlesTrivial [IsAffine S]
    [Flat U.hom] [Surjective U.hom] [LocallyOfFinitePresentation U.hom] :
    ξ.IsTrivial := by
  apply ξ.isTrivial_of_affine_fppf
  intro W _ _ _ _ ζ
  exact ζ.isTrivial_split_of_lineBundlesTrivial hPic

end Langlands.GroupScheme.Cocycle

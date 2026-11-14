import Langlands.AlgebraicGeometry.Modules.UnitCocycleDescentEffectiveProof
import Langlands.AlgebraicGeometry.Picard.AffineLineBundlePicard

/-! # Global unit coboundaries from trivial module Picard groups -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.Scheme.Modules

open Langlands.SchemeModule
open Langlands.AlgebraicGeometry.Picard
open Langlands.Scheme.UnitCocycleDescent

/-- Changing a trivialization by an automorphism of the structure sheaf changes
its comparison by the two pullbacks of that automorphism. -/
theorem equalCompositeUnitAut_change
    {X Y Z : Scheme.{u}} (p : X ⟶ Y) (a b : Z ⟶ X)
    (h : a ≫ p = b ≫ p) {M : Y.Modules}
    (α : (Scheme.Modules.pullback p).obj M ≅ SheafOfModules.unit X.ringCatSheaf)
    (e : SheafOfModules.unit X.ringCatSheaf ≅ SheafOfModules.unit X.ringCatSheaf) :
    equalCompositeUnitAut p a b h (α ≪≫ e) =
      (structureAutPullback a e).symm ≪≫ equalCompositeUnitAut p a b h α ≪≫
        structureAutPullback b e := by
  ext1
  simp [equalCompositeUnitAut, structureAutPullback]

/-- A natural multiplicative unit cocycle on an affine faithfully flat cover of
`Spec R` is a global coboundary if the module Picard group of `R` is trivial. -/
theorem exists_unit_coboundary_of_pic_trivial
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    {X : Scheme.{u}} (p : X ⟶ Spec R)
    [IsAffineHom p] [Flat p] [Surjective p]
    (c : ∀ (Z : Scheme.{u}) (a b : Z ⟶ X), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ)
    (hnat : IsNatural p c) (hmul : IsMultiplicative p c) :
    ∃ q : Γ(X, ⊤)ˣ, ∀ (Z : Scheme.{u}) (a b : Z ⟶ X) (h : a ≫ p = b ≫ p),
      c Z a b h =
        Units.map a.appTop.hom.toMonoidHom q *
          (Units.map b.appTop.hom.toMonoidHom q)⁻¹ := by
  obtain ⟨L, α, hα⟩ := unitCocycleDescentEffective X (Spec R) p
    inferInstance inferInstance inferInstance c hnat hmul
  obtain ⟨β⟩ := nonempty_lineBundle_iso_structureSheaf_of_pic_trivial L
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

/-- A chosen global unit cobounding the given natural multiplicative cocycle. -/
def unitCoboundaryOfPicTrivial
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    {X : Scheme.{u}} (p : X ⟶ Spec R)
    [IsAffineHom p] [Flat p] [Surjective p]
    (c : ∀ (Z : Scheme.{u}) (a b : Z ⟶ X), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ)
    (hnat : IsNatural p c) (hmul : IsMultiplicative p c) : Γ(X, ⊤)ˣ :=
  (exists_unit_coboundary_of_pic_trivial p c hnat hmul).choose

theorem unitCoboundaryOfPicTrivial_spec
    {R : CommRingCat.{u}} [Subsingleton (CommRing.Pic R)]
    {X : Scheme.{u}} (p : X ⟶ Spec R)
    [IsAffineHom p] [Flat p] [Surjective p]
    (c : ∀ (Z : Scheme.{u}) (a b : Z ⟶ X), a ≫ p = b ≫ p → Γ(Z, ⊤)ˣ)
    (hnat : IsNatural p c) (hmul : IsMultiplicative p c)
    (Z : Scheme.{u}) (a b : Z ⟶ X) (h : a ≫ p = b ≫ p) :
    c Z a b h =
      Units.map a.appTop.hom.toMonoidHom (unitCoboundaryOfPicTrivial p c hnat hmul) *
        (Units.map b.appTop.hom.toMonoidHom (unitCoboundaryOfPicTrivial p c hnat hmul))⁻¹ :=
  (exists_unit_coboundary_of_pic_trivial p c hnat hmul).choose_spec Z a b h

end Langlands.Scheme.Modules

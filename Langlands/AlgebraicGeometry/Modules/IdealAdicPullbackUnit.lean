import Langlands.AlgebraicGeometry.Modules.IdealAdicQuotientDescent

/-! # The pullback unit descends through ideals killed on the source -/

noncomputable section

universe u

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

namespace Langlands.AlgebraicGeometry.Modules.IdealAdic

variable {R : CommRingCat.{u}} {X Y : Scheme.{u}} (f : X ⟶ Spec R)

/-- The actual ring map on an inverse-image open preserves the base scalar. -/
lemma app_scalar (i : Y ⟶ X) (U : X.Opens) (a : R) :
    i.app U (scalar f U a) = scalar (i ≫ f) (i ⁻¹ᵁ U) a := by
  change (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op ≫ i.app U)
    ((DerivedSections.structureRingHom f) a) = _
  rw [Scheme.Hom.naturality]
  rfl

/-- If the composite to the affine base kills an ideal, the actual pullback
unit kills its local multiples. -/
lemma pullbackUnit_annihilates (I : Ideal R) (i : Y ⟶ X)
    (h : ∀ a ∈ I, DerivedSections.structureRingHom (i ≫ f) a = 0)
    (M : X.Modules) (U : X.Opens) (a : R) (ha : a ∈ I) (m : Γ(M, U)) :
    ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U
      (scalar f U a • m) = 0 := by
  rw [Scheme.Modules.Hom.app_smul]
  have hz : i.app U (scalar f U a) = 0 := by
    rw [app_scalar]
    change (Y.presheaf.map (homOfLE (show i ⁻¹ᵁ U ≤ ⊤ from le_top)).op)
      (DerivedSections.structureRingHom (i ≫ f) a) = 0
    rw [h a ha, map_zero]
  change i.app U (scalar f U a) •
    (show Γ((Scheme.Modules.pullback i).obj M, i ⁻¹ᵁ U) from
      ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M).app U m) = 0
  rw [hz, zero_smul]

/-- The canonical quotient-to-pulled-back-module map, considered on the
original scheme by pushforward. -/
def pullbackUnitDesc (I : Ideal R) (i : Y ⟶ X)
    (h : ∀ a ∈ I, DerivedSections.structureRingHom (i ≫ f) a = 0)
    (M : X.Modules) :
    quotient f I M ⟶ (Scheme.Modules.pushforward i).obj
      ((Scheme.Modules.pullback i).obj M) :=
  desc f I ((Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M)
    (pullbackUnit_annihilates f I i h M)

@[reassoc (attr := simp)]
lemma projection_pullbackUnitDesc (I : Ideal R) (i : Y ⟶ X)
    (h : ∀ a ∈ I, DerivedSections.structureRingHom (i ≫ f) a = 0)
    (M : X.Modules) :
    projection f I M ≫ pullbackUnitDesc f I i h M =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app M :=
  projection_desc _ _ _ _

end Langlands.AlgebraicGeometry.Modules.IdealAdic

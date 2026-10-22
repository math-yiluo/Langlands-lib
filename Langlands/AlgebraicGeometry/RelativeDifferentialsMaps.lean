import Langlands.AlgebraicGeometry.RelativeDifferentialsUniversal
import Langlands.AlgebraicGeometry.RelativeDerivationsFunctorial

/-! # Induced maps on relative differential sheaves -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme.Modules

namespace Langlands.Scheme

variable {X Y Z S : AlgebraicGeometry.Scheme.{u}}

/-- The morphism of differentials adjoint to the pullback differential. -/
def relativeDifferentialsPushforwardMap (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S}
    (w : g ≫ fY = fX) :
    relativeDifferentials fY ⟶ (pushforward g).obj (relativeDifferentials fX) :=
  relativeDifferentialsDesc fY
    (RelativeDerivation.precompOver g w (relativeDifferentialsDerivation fX))

@[simp]
lemma relativeDifferentialsPushforwardMap_fac (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX) :
    RelativeDerivation.postcomp (relativeDifferentialsDerivation fY)
      (relativeDifferentialsPushforwardMap g w) =
        RelativeDerivation.precompOver g w (relativeDifferentialsDerivation fX) :=
  relativeDifferentialsDesc_fac _ _

/-- The induced morphism from the pulled-back relative differential sheaf. -/
def relativeDifferentialsMap (g : X ⟶ Y) {fX : X ⟶ S} {fY : Y ⟶ S}
    (w : g ≫ fY = fX) :
    (pullback g).obj (relativeDifferentials fY) ⟶ relativeDifferentials fX :=
  ((pullbackPushforwardAdjunction g).homEquiv _ _).symm
    (relativeDifferentialsPushforwardMap g w)

@[simp]
lemma relativeDifferentialsMap_adjoint (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX) :
    (pullbackPushforwardAdjunction g).homEquiv _ _ (relativeDifferentialsMap g w) =
      relativeDifferentialsPushforwardMap g w :=
  Equiv.apply_symm_apply _ _

/-- Characterization by the universal derivations, expressed under adjunction. -/
@[simp]
lemma relativeDifferentialsMap_fac (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX) :
    RelativeDerivation.postcomp (relativeDifferentialsDerivation fY)
      ((pullbackPushforwardAdjunction g).homEquiv _ _ (relativeDifferentialsMap g w)) =
        RelativeDerivation.precompOver g w (relativeDifferentialsDerivation fX) := by
  rw [relativeDifferentialsMap_adjoint, relativeDifferentialsPushforwardMap_fac]

/-- The adjoint sends the differential of a local section to its pulled-back differential. -/
lemma relativeDifferentialsMap_adjoint_app (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX)
    (U : Y.Opens) (a : Γ(Y, U)) :
    ((pullbackPushforwardAdjunction g).homEquiv _ _ (relativeDifferentialsMap g w)).app U
        ((relativeDifferentialsDerivation fY).app U a) =
      (relativeDifferentialsDerivation fX).app (g ⁻¹ᵁ U) (g.app U a) := by
  have h := congrArg (fun d : RelativeDerivation fY
      ((pushforward g).obj (relativeDifferentials fX)) => d.app U a)
    (relativeDifferentialsMap_fac g w)
  simpa only [RelativeDerivation.postcomp_app, RelativeDerivation.precompOver_app] using h

/-- Uniqueness of the induced pullback morphism from its action on derivations. -/
lemma relativeDifferentialsMap_unique (g : X ⟶ Y)
    {fX : X ⟶ S} {fY : Y ⟶ S} (w : g ≫ fY = fX)
    (α : (pullback g).obj (relativeDifferentials fY) ⟶ relativeDifferentials fX)
    (h : RelativeDerivation.postcomp (relativeDifferentialsDerivation fY)
      ((pullbackPushforwardAdjunction g).homEquiv _ _ α) =
        RelativeDerivation.precompOver g w (relativeDifferentialsDerivation fX)) :
    α = relativeDifferentialsMap g w := by
  apply ((pullbackPushforwardAdjunction g).homEquiv _ _).injective
  apply relativeDifferentials_hom_ext fY
  rw [relativeDifferentialsMap_fac]
  exact h

end Langlands.Scheme

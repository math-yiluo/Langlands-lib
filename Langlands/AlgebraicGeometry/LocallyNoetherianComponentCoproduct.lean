import Langlands.AlgebraicGeometry.LocallyNoetherianComponentSchemes
import Mathlib.AlgebraicGeometry.Limits

/-! # Reconstruction from the actual open connected-component schemes -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

set_option autoImplicit false
set_option maxHeartbeats 400000

namespace Langlands.AlgebraicGeometry

variable (X : Scheme.{u}) [IsLocallyNoetherian X]

/-- The original scheme is a coproduct of its actual open component schemes. -/
def componentCoproductIsColimit : IsColimit (Cofan.mk X (componentι X)) :=
  Classical.choice (nonempty_isColimit_cofanMk_of (componentι X)
    (by simpa only [Scheme.Opens.opensRange_ι] using componentOpen_iSup X)
    (by
      intro c d hcd
      simpa only [Scheme.Opens.opensRange_ι] using componentOpen_disjoint X hcd))

instance componentCoproductDesc_isIso : IsIso (Sigma.desc (componentι X)) :=
  (Cofan.nonempty_isColimit_iff_isIso_sigmaDesc (Cofan.mk X (componentι X))).mp
    ⟨componentCoproductIsColimit X⟩

/-- Canonical isomorphism from the coproduct of the actual component schemes. -/
def componentCoproductIso : (∐ componentScheme X) ≅ X :=
  asIso (Sigma.desc (componentι X))

@[simp] theorem componentCoproductIso_hom :
    (componentCoproductIso X).hom = Sigma.desc (componentι X) := rfl

@[reassoc (attr := simp)] theorem componentCoproductIso_ι
    (c : _root_.ConnectedComponents X) :
    Sigma.ι (componentScheme X) c ≫ (componentCoproductIso X).hom = componentι X c := by
  simp

@[reassoc (attr := simp)] theorem componentι_componentCoproductIso_inv
    (c : _root_.ConnectedComponents X) :
    componentι X c ≫ (componentCoproductIso X).inv = Sigma.ι (componentScheme X) c := by
  rw [← componentCoproductIso_ι X c, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- Assemble an arbitrary family of actual component maps into an original
scheme morphism. The component index need not be finite or nonempty. -/
def componentDesc {Y : Scheme.{u}}
    (f : ∀ c : _root_.ConnectedComponents X, componentScheme X c ⟶ Y) : X ⟶ Y :=
  (componentCoproductIso X).inv ≫ Sigma.desc f

@[reassoc (attr := simp)] theorem componentι_componentDesc {Y : Scheme.{u}}
    (f : ∀ c : _root_.ConnectedComponents X, componentScheme X c ⟶ Y)
    (c : _root_.ConnectedComponents X) :
    componentι X c ≫ componentDesc X f = f c := by
  simp [componentDesc, ← Category.assoc]

/-- Morphisms are determined by restriction to the actual component schemes. -/
theorem component_hom_ext {Y : Scheme.{u}} {f g : X ⟶ Y}
    (hfg : ∀ c : _root_.ConnectedComponents X, componentι X c ≫ f = componentι X c ≫ g) :
    f = g := by
  apply (componentOpenCover X).hom_ext
  exact hfg

/-- Reconstruction of a morphism from all its component restrictions. -/
@[simp] theorem componentDesc_restrict {Y : Scheme.{u}} (f : X ⟶ Y) :
    componentDesc X (fun c => componentι X c ≫ f) = f := by
  apply component_hom_ext X
  intro c
  simp

/-- Postcomposition commutes with the constructed assembly of component maps. -/
@[reassoc] theorem componentDesc_comp {Y Z : Scheme.{u}}
    (f : ∀ c : _root_.ConnectedComponents X, componentScheme X c ⟶ Y) (g : Y ⟶ Z) :
    componentDesc X f ≫ g = componentDesc X (fun c => f c ≫ g) := by
  apply component_hom_ext X
  intro c
  simp

end Langlands.AlgebraicGeometry

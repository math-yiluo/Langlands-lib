import Langlands.Sheaf.Equivariant.Topological
import Mathlib.Topology.Sheaves.SheafOfFunctions
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.RepresentationTheory.Rep.Basic

/-!
# Equivariant sheaves of module-valued functions

The transport map for a label `g` pulls a function back along `x ↦ g • x`
and applies the coefficient operator `ρ g⁻¹`. Ordinary inclusions give
ordinary restriction. The sheaf proof is transferred from Mathlib's sheaf
of arbitrary functions, through the limit-reflecting forgetful functor.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe u uG uR

variable (R : Type uR) [CommRing R]
variable (G : Type uG) [Group G] (X : Type u) [TopologicalSpace X] [MulAction G X]

/-- Global sections as actual representations on modules. -/
def sectionRepresentation :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G :=
  sections G X (ModuleCat.{u} R) ⋙ Rep.ActionToRep R G

namespace FunctionSheaf

variable {R G X} {M : Type u} [AddCommGroup M] [Module R M]
variable (ρ : Representation R G M)

/-- Pullback along a labelled arrow, with the inverse coefficient operator. -/
def pullback {U V : ActionOpens G X} (f : U ⟶ V) :
    (V.openSet → M) →ₗ[R] (U.openSet → M) where
  toFun s x := ρ f.label⁻¹ (s ⟨f.label • x.1, f.mapsTo x.1 x.2⟩)
  map_add' s t := by ext x; exact map_add _ _ _
  map_smul' r s := by ext x; exact map_smul _ _ _

@[simp]
theorem pullback_apply {U V : ActionOpens G X} (f : U ⟶ V)
    (s : V.openSet → M) (x : U.openSet) :
    pullback ρ f s x = ρ f.label⁻¹ (s ⟨f.label • x.1, f.mapsTo x.1 x.2⟩) := rfl

/-- Actual functions on each open, with group transport and restriction maps. -/
def presheaf : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R where
  obj U := ModuleCat.of R (U.unop.openSet → M)
  map f := ModuleCat.ofHom (pullback ρ f.unop)
  map_id U := by
    ext s x
    simp [pullback]
  map_comp f g := by
    ext s x
    simp [pullback, mul_smul, map_mul, Module.End.mul_apply]

/-- After forgetting coefficients, ordinary restriction is the function presheaf. -/
def underlyingIso :
    (underlyingPresheaf G X (ModuleCat.{u} R)).obj (presheaf (X := X) ρ) ⋙
        forget (ModuleCat.{u} R) ≅
      TopCat.presheafToType (TopCat.of X) M :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro U V f
    apply ConcreteCategory.hom_ext
    intro s
    funext x
    change ρ (1 : G)⁻¹ (s ⟨(1 : G) • x.1, _⟩) = s ⟨x.1, _⟩
    simp)

/-- The module-valued sheaf condition follows from the ordinary function sheaf. -/
theorem isSheaf :
    ((underlyingPresheaf G X (ModuleCat.{u} R)).obj (presheaf (X := X) ρ)).IsSheaf := by
  apply (CategoryTheory.Presheaf.isSheaf_iff_isSheaf_forget
    (Opens.grothendieckTopology X) _ (forget (ModuleCat.{u} R))).2
  exact (TopCat.Presheaf.isSheaf_iso_iff (underlyingIso (X := X) ρ)).2
    (TopCat.Presheaf.toType_isSheaf (TopCat.of X) M)

/-- A constructed object of the equivariant sheaf category. -/
def sheaf : TopologicalSheaf G X (ModuleCat.{u} R) :=
  ⟨presheaf ρ, isSheaf ρ⟩

/-- The global left action combines coefficient action and inverse point action. -/
theorem sectionAction_apply (g : G)
    (s : (ActionOpens.top (G := G) (X := X)).openSet → M)
    (x : (ActionOpens.top (G := G) (X := X)).openSet) :
    ((sectionAction (presheaf ρ)).ρ g).hom s x =
      ρ g (s ⟨g⁻¹ • x.1, by trivial⟩) := by
  change ρ (g⁻¹)⁻¹ (s ⟨g⁻¹ • x.1, _⟩) = _
  simp only [inv_inv]

variable {P Q : Rep.{u} R G}

/-- A coefficient intertwiner acts pointwise on functions and respects transport. -/
def map (f : P ⟶ Q) : sheaf (X := X) P.ρ ⟶ sheaf (X := X) Q.ρ :=
  ObjectProperty.homMk
    { app U := ModuleCat.ofHom
        { toFun s x := f.hom (s x)
          map_add' s t := by ext x; exact map_add _ _ _
          map_smul' r s := by ext x; exact map_smul _ _ _ }
      naturality U V h := by
        ext s
        funext x
        exact Rep.hom_comm_apply f h.unop.label⁻¹ _ }

variable (R G X)

/-- Equivariant function sheaves depend functorially on the coefficient representation. -/
def functor : Rep.{u} R G ⥤ TopologicalSheaf G X (ModuleCat.{u} R) where
  obj P := sheaf P.ρ
  map f := map f
  map_id P := by
    apply ObjectProperty.hom_ext
    ext U s
    rfl
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext U s
    rfl

/-- Constant functions define a natural equivariant map from the coefficients. -/
def constantSections :
    Rep.RepToAction R G ⟶ functor R G X ⋙ sections G X (ModuleCat.{u} R) where
  app P :=
    { hom := ModuleCat.ofHom
        { toFun m _ := m
          map_add' _ _ := rfl
          map_smul' _ _ := rfl }
      comm g := by
        ext m
        funext x
        change P.ρ g m = P.ρ (g⁻¹)⁻¹ m
        rw [inv_inv] }
  naturality P Q f := by
    apply Action.Hom.ext
    ext m
    rfl

end FunctionSheaf

end Langlands.Sheaf.Equivariant

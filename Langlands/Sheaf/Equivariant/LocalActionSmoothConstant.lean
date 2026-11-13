import Langlands.Sheaf.Equivariant.LocalActionSmoothPart
import Langlands.Sheaf.Equivariant.LocalActionConstant

/-!
# Constant locally discrete sheaves for a local action system

For a local action system with admissible refinements, constant presheaves of modules are
locally discrete: they are discrete, and objects with admissible local actions cover. The
sheafification of a locally discrete presheaf of modules is locally discrete: the canonical
map to the sheafification factors through the locally discrete part, which is a sheaf, so the
locally discrete part of the sheafification is all of it. Hence the constant sheaf functor
takes values in locally discrete sheaves. Under sheafification this functor is exact.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant.LocalActionSystem

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uR w

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T) {R : Type uR} [CommRing R]
variable [L.HasAdmissibleRefinements J]

/-- A morphism from a locally discrete presheaf of modules factors through the locally
discrete part of its target. -/
def smoothPresheafLift {P F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hP : L.IsLocallyDiscrete J P)
    (f : P ⟶ F) : P ⟶ smoothPresheaf L J F where
  app U := ModuleCat.ofHom (LinearMap.codRestrict _ (f.app U).hom fun s =>
    map_mem_smoothSubmodule_of_hom L J f (hP U.unop s))
  naturality U V g := by
    ext s
    apply Subtype.ext
    exact congrArg (fun k => k.hom s) (f.naturality g)

@[reassoc (attr := simp)]
theorem smoothPresheafLift_comp_ι {P F : Tᵒᵖ ⥤ ModuleCat.{w} R}
    (hP : L.IsLocallyDiscrete J P) (f : P ⟶ F) :
    smoothPresheafLift L J hP f ≫ smoothPresheafι L J F = f :=
  rfl

/-- The sheafification of a locally discrete presheaf of modules is locally discrete. The
canonical map `P ⟶ sheafify J P` factors through the locally discrete part of the
sheafification, which is a sheaf; the induced map from the sheafification to its locally
discrete part is a section of the inclusion, so every section of the sheafification is
locally discrete. -/
theorem isLocallyDiscrete_sheafify [HasWeakSheafify J (ModuleCat.{w} R)]
    {P : Tᵒᵖ ⥤ ModuleCat.{w} R} (hP : L.IsLocallyDiscrete J P) :
    L.IsLocallyDiscrete J (sheafify J P) := by
  have hS : Presheaf.IsSheaf J (sheafify J P) :=
    ((presheafToSheaf J (ModuleCat.{w} R)).obj P).property
  let ψ := sheafifyLift J (smoothPresheafLift L J hP (toSheafify J P))
    (smoothPresheaf_isSheaf (L := L) (J := J) hS)
  have hψ : ψ ≫ smoothPresheafι L J (sheafify J P) = 𝟙 _ := by
    apply sheafify_hom_ext J _ _ hS
    rw [← Category.assoc, toSheafify_sheafifyLift, Category.comp_id]
    rfl
  rw [isLocallyDiscrete_iff_forall_mem]
  intro U s
  have h := congrArg (fun k => (k.app (op U)).hom s) hψ
  change ((ψ.app (op U)).hom s).1 = s at h
  rw [← h]
  exact ((ψ.app (op U)).hom s).2

/-- Constant presheaves of modules are locally discrete. -/
theorem isLocallyDiscrete_const (M : ModuleCat.{w} R) :
    L.IsLocallyDiscrete J ((Functor.const Tᵒᵖ).obj M) :=
  IsDiscrete.isLocallyDiscrete L (HasAdmissibleRefinements.covers (L := L) (J := J))
    (isDiscrete_const L M)

variable (R)

section Functor

variable [HasWeakSheafify J (ModuleCat.{w} R)]

/-- The constant sheaf of a module is locally discrete. -/
theorem smoothSheafProperty_constantSheaf (M : ModuleCat.{w} R) :
    L.smoothSheafProperty (ModuleCat.{w} R) J ((constantSheaf J (ModuleCat.{w} R)).obj M) :=
  isLocallyDiscrete_sheafify L J (isLocallyDiscrete_const L J M)

/-- The constant sheaf functor, with values in locally discrete sheaves. -/
def smoothConstantSheaf : ModuleCat.{w} R ⥤ L.SmoothSheaf (ModuleCat.{w} R) J :=
  (L.smoothSheafProperty (ModuleCat.{w} R) J).lift (constantSheaf J (ModuleCat.{w} R))
    (smoothSheafProperty_constantSheaf L J R)

/-- Followed by the inclusion into all sheaves, the locally discrete constant sheaf functor
is the constant sheaf functor. -/
theorem smoothConstantSheaf_comp_inclusion :
    smoothConstantSheaf L J R ⋙ L.smoothSheafInclusion (ModuleCat.{w} R) J =
      constantSheaf J (ModuleCat.{w} R) :=
  rfl

end Functor

section Exact

variable [HasSheafify J (ModuleCat.{w} R)]

instance smoothConstantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (smoothConstantSheaf L J R) :=
  haveI : PreservesFiniteLimits
      (smoothConstantSheaf L J R ⋙ L.smoothSheafInclusion (ModuleCat.{w} R) J) :=
    inferInstanceAs (PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} R)))
  preservesFiniteLimits_of_reflects_of_preserves _
    (L.smoothSheafInclusion (ModuleCat.{w} R) J)

instance smoothConstantSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (smoothConstantSheaf L J R) :=
  haveI : PreservesFiniteColimits
      (smoothConstantSheaf L J R ⋙ L.smoothSheafInclusion (ModuleCat.{w} R) J) :=
    inferInstanceAs (PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} R)))
  preservesFiniteColimits_of_reflects_of_preserves _
    (L.smoothSheafInclusion (ModuleCat.{w} R) J)

instance smoothConstantSheaf_additive : (smoothConstantSheaf L J R).Additive :=
  Functor.additive_of_preserves_binary_products _

end Exact

end Langlands.Sheaf.Equivariant.LocalActionSystem

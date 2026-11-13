import Langlands.Sheaf.Equivariant.LocalActionDiscretePart
import Mathlib.CategoryTheory.Sites.ConstantSheaf

/-!
# Constant discrete sheaves for a local action system

For a local action system on a site, constant presheaves of modules are discrete, since every
arrow acts on their sections by the identity. Assume that every covering sieve of an object with
an admissible local action is refined by a finite locally equivariant family. Then the
sheafification of a discrete presheaf of modules is discrete: the canonical map to the
sheafification factors through the discrete part, which is a sheaf, so the discrete part of the
sheafification is all of it. Hence the constant sheaf functor takes values in discrete sheaves.
Under sheafification this functor is exact: it preserves finite limits and finite colimits.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory CategoryTheory.Limits Opposite

universe v u uG uR w

variable {T : Type u} [Category.{v} T] {G : Type uG} [Group G] [TopologicalSpace G]
variable (L : LocalActionSystem T G) (J : GrothendieckTopology T) {R : Type uR} [CommRing R]

/-- Constant presheaves of modules are discrete: every arrow acts on their sections by the
identity. -/
theorem isDiscrete_const (M : ModuleCat.{w} R) : L.IsDiscrete ((Functor.const Tᵒᵖ).obj M) :=
  fun _ H _ _ _ => ⟨H, le_rfl, fun _ _ => rfl⟩

/-- A morphism from a discrete presheaf of modules factors through the discrete part of its
target. -/
def discretePresheafLift {P F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hP : L.IsDiscrete P) (f : P ⟶ F) :
    P ⟶ discretePresheaf L F where
  app U := ModuleCat.ofHom (LinearMap.codRestrict _ (f.app U).hom fun s =>
    map_mem_discreteSubmodule_of_hom L f ((isDiscrete_iff_forall_mem L P).1 hP _ s))
  naturality U V g := by
    ext s
    apply Subtype.ext
    exact congrArg (fun k => k.hom s) (f.naturality g)

@[reassoc (attr := simp)]
theorem discretePresheafLift_comp_ι {P F : Tᵒᵖ ⥤ ModuleCat.{w} R} (hP : L.IsDiscrete P)
    (f : P ⟶ F) : discretePresheafLift L hP f ≫ discretePresheafι L F = f :=
  rfl

variable {L J}

/-- The sheafification of a discrete presheaf of modules is discrete. The canonical map
`P ⟶ sheafify J P` factors through the discrete part of the sheafification, which is a sheaf;
the induced map from the sheafification to its discrete part is a section of the inclusion, so
every section of the sheafification is discrete. -/
theorem isDiscrete_sheafify [HasWeakSheafify J (ModuleCat.{w} R)]
    [L.HasFiniteEquivariantRefinements J] {P : Tᵒᵖ ⥤ ModuleCat.{w} R} (hP : L.IsDiscrete P) :
    L.IsDiscrete (sheafify J P) := by
  have hS : Presheaf.IsSheaf J (sheafify J P) :=
    ((presheafToSheaf J (ModuleCat.{w} R)).obj P).property
  let ψ := sheafifyLift J (discretePresheafLift L hP (toSheafify J P))
    (discretePresheaf_isSheaf hS)
  have hψ : ψ ≫ discretePresheafι L (sheafify J P) = 𝟙 _ := by
    apply sheafify_hom_ext J _ _ hS
    rw [← Category.assoc, toSheafify_sheafifyLift, Category.comp_id]
    rfl
  rw [isDiscrete_iff_forall_mem]
  intro U s
  have h := congrArg (fun k => (k.app (op U)).hom s) hψ
  change ((ψ.app (op U)).hom s).1 = s at h
  rw [← h]
  exact ((ψ.app (op U)).hom s).2

variable (L J R)

section Functor

variable [HasWeakSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]

/-- The constant sheaf of a module is discrete. -/
theorem discreteSheafProperty_constantSheaf (M : ModuleCat.{w} R) :
    L.discreteSheafProperty (ModuleCat.{w} R) J ((constantSheaf J (ModuleCat.{w} R)).obj M) :=
  isDiscrete_sheafify (isDiscrete_const L M)

/-- The constant sheaf functor, with values in discrete sheaves. -/
def discreteConstantSheaf : ModuleCat.{w} R ⥤ L.DiscreteSheaf (ModuleCat.{w} R) J :=
  (L.discreteSheafProperty (ModuleCat.{w} R) J).lift (constantSheaf J (ModuleCat.{w} R))
    (discreteSheafProperty_constantSheaf L J R)

/-- Followed by the inclusion into all sheaves, the discrete constant sheaf functor is the
constant sheaf functor. -/
theorem discreteConstantSheaf_comp_inclusion :
    discreteConstantSheaf L J R ⋙ L.discreteSheafInclusion (ModuleCat.{w} R) J =
      constantSheaf J (ModuleCat.{w} R) :=
  rfl

end Functor

section Exact

variable [HasSheafify J (ModuleCat.{w} R)] [L.HasFiniteEquivariantRefinements J]

instance constantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} R)) :=
  inferInstanceAs (PreservesFiniteLimits
    (Functor.const Tᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} R)))

instance constantSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} R)) :=
  inferInstanceAs (PreservesFiniteColimits
    (Functor.const Tᵒᵖ ⋙ presheafToSheaf J (ModuleCat.{w} R)))

instance discreteConstantSheaf_preservesFiniteLimits :
    PreservesFiniteLimits (discreteConstantSheaf L J R) :=
  haveI : PreservesFiniteLimits
      (discreteConstantSheaf L J R ⋙ L.discreteSheafInclusion (ModuleCat.{w} R) J) :=
    inferInstanceAs (PreservesFiniteLimits (constantSheaf J (ModuleCat.{w} R)))
  preservesFiniteLimits_of_reflects_of_preserves _
    (L.discreteSheafInclusion (ModuleCat.{w} R) J)

instance discreteConstantSheaf_preservesFiniteColimits :
    PreservesFiniteColimits (discreteConstantSheaf L J R) :=
  haveI : PreservesFiniteColimits
      (discreteConstantSheaf L J R ⋙ L.discreteSheafInclusion (ModuleCat.{w} R) J) :=
    inferInstanceAs (PreservesFiniteColimits (constantSheaf J (ModuleCat.{w} R)))
  preservesFiniteColimits_of_reflects_of_preserves _
    (L.discreteSheafInclusion (ModuleCat.{w} R) J)

instance discreteConstantSheaf_additive : (discreteConstantSheaf L J R).Additive :=
  Functor.additive_of_preserves_binary_products _

end Exact

end Langlands.Sheaf.Equivariant

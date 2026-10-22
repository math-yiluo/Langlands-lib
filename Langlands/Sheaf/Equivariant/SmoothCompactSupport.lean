import Langlands.Sheaf.Equivariant.CompactSupport
import Langlands.Representation.Smooth.SmoothPart.Definitions
import Langlands.Representation.Category.Basic

/-!
# Smooth compactly supported sections

Apply the existing smooth-vector construction to the actual representation
on compactly supported sections. No automatic smoothness of all sections
is assumed.
-/

noncomputable section

namespace Langlands.Sheaf.Equivariant

open CategoryTheory TopologicalSpace Opposite

universe u uG uW

variable {R : Type u} [CommRing R]
variable {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
variable {X : Type u} [TopologicalSpace X] [MulAction G X] [ContinuousConstSMul G X]

namespace SmoothCompactSections

variable (F : (ActionOpens G X)ᵒᵖ ⥤ ModuleCat.{u} R)

/-- The actual smooth part of the compact-section representation. -/
abbrev representation :=
  Langlands.smoothPart (CompactSections.representation F)

/-- Every vector of the constructed representation has an open fixing subgroup. -/
theorem isSmooth : Langlands.IsSmooth (representation F) := by
  intro s
  obtain ⟨K, hK⟩ := s.property
  refine ⟨K, ?_⟩
  intro k
  apply Subtype.ext
  exact hK k

set_option backward.isDefEq.respectTransparency false in
omit [IsTopologicalGroup G] in
/-- The image in global sections consists exactly of compact smooth sections. -/
theorem exists_preimage_iff (s : F.obj (op ActionOpens.top)) :
    (∃ t : Langlands.smoothVectors (CompactSections.representation F), t.val.val = s) ↔
      IsCompact (Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F) s) ∧
        Langlands.IsSmoothVector (CompactSections.globalRepresentation F) s := by
  constructor
  · rintro ⟨t, rfl⟩
    refine ⟨t.val.property, ?_⟩
    obtain ⟨K, hK⟩ := t.property
    refine ⟨K, ?_⟩
    intro k
    exact congrArg Subtype.val (hK k)
  · rintro ⟨hs, K, hK⟩
    refine ⟨⟨⟨s, hs⟩, K, ?_⟩, rfl⟩
    intro k
    apply Subtype.ext
    exact hK k

variable (R G X)

/-- Smooth compact sections and induced maps, valued in Mathlib representations. -/
def functor : TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Rep.{u} R G where
  obj F := Rep.of (representation F.obj)
  map f := Rep.ofHom (Langlands.smoothMap (CompactSections.map f))
  map_id _ := by
    ext s
    rfl
  map_comp _ _ := by
    ext s
    rfl

/-- Bundle the proved smooth section actions in the published smooth category. -/
def smoothFunctor :
    TopologicalSheaf G X (ModuleCat.{u} R) ⥤ Langlands.SmoothRep.{u, uG, u} R G :=
  (Langlands.smoothRepProperty R G).lift (functor R G X)
    (fun F => isSmooth F.obj)

/-- Forgetting the smoothness witness recovers the original section functor. -/
def smoothFunctorToRepIso :
    smoothFunctor R G X ⋙ Langlands.SmoothRep.toRep ≅ functor R G X :=
  (Langlands.smoothRepProperty R G).liftCompιIso (functor R G X)
    (fun F => isSmooth F.obj)

/-- The natural equivariant inclusion into all compactly supported sections. -/
def inclusion : functor R G X ⟶ CompactSections.functor R G X where
  app F := Rep.ofHom (Langlands.smoothInclusion (CompactSections.representation F.obj))
  naturality _ _ _ := by
    ext s
    rfl

/-- The natural equivariant inclusion into all global sections. -/
def globalInclusion : functor R G X ⟶ sectionRepresentation R G X :=
  inclusion R G X ≫ CompactSections.inclusion R G X

variable {R G X}
variable {W : Type uW} [AddCommGroup W] [Module R W]
variable {σ : Representation R G W}

set_option backward.isDefEq.respectTransparency false in
/-- Restrict an equivariant global-section map whose values have compact support. -/
def compactLift (f : σ.IntertwiningMap (CompactSections.globalRepresentation F))
    (hc : ∀ w, IsCompact
      (Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F) (f w))) :
    σ.IntertwiningMap (CompactSections.representation F) where
  toLinearMap := f.toLinearMap.codRestrict
    (Langlands.Sheaf.CompactSupport.submodule (CompactSections.ordinary F)) hc
  isIntertwining' g := by
    apply LinearMap.ext
    intro w
    apply Subtype.ext
    exact congrArg (fun m : W →ₗ[R] F.obj (op ActionOpens.top) => m w)
      (f.isIntertwining' g)

/-- The same map from a smooth representation factors through smooth compact sections. -/
def lift (hσ : Langlands.IsSmooth σ)
    (f : σ.IntertwiningMap (CompactSections.globalRepresentation F))
    (hc : ∀ w, IsCompact
      (Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F) (f w))) :
    σ.IntertwiningMap (representation F) :=
  Langlands.smoothLift hσ (compactLift F f hc)

@[simp]
theorem lift_apply (hσ : Langlands.IsSmooth σ)
    (f : σ.IntertwiningMap (CompactSections.globalRepresentation F))
    (hc : ∀ w, IsCompact
      (Langlands.Sheaf.CompactSupport.support (CompactSections.ordinary F) (f w)))
    (w : W) :
    (lift F hσ f hc w).val.val = f w := rfl

/-- A map into smooth compact sections is determined by its global-section values. -/
theorem hom_ext {f g : σ.IntertwiningMap (representation F)}
    (h : ∀ w, (f w).val.val = (g w).val.val) : f = g := by
  apply Representation.IntertwiningMap.ext
  apply LinearMap.ext
  intro w
  apply Subtype.ext
  apply Subtype.ext
  exact h w

end SmoothCompactSections

end Langlands.Sheaf.Equivariant

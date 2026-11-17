import Langlands.GroupScheme.Descent.EtaleReflection

/-! # Reflection of group-scheme properties along fppf covers -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj CategoryTheory.Obj

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 800000

namespace Langlands.GroupScheme

variable {S U : Scheme.{u}} (p : U ⟶ S) [Flat p] [LocallyOfFinitePresentation p]
  [Surjective p]

/-- Affineness of the structure morphism descends along a surjective fppf map. -/
theorem isAffineHom_of_baseChange_of_fppf (G : GroupScheme S)
    (hG : IsAffineHom ((GroupScheme.baseChange p).obj G).X.hom) : IsAffineHom G.X.hom :=
  MorphismProperty.of_pullback_snd_of_descendsAlong
    (P := @IsAffineHom) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (f := G.X.hom) (g := p) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hG

/-- Closedness of a subgroup descends along a surjective fppf map. -/
theorem IsClosedSubgroup.of_baseChange_of_fppf {H G : GroupScheme S} {i : H ⟶ G}
    (hi : IsClosedSubgroup ((GroupScheme.baseChange p).map i)) : IsClosedSubgroup i :=
  MorphismProperty.of_isPullback_of_descendsAlong
    (P := @IsClosedImmersion) (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
    (baseChange_map_isPullback p i) ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ hi

/-- Surjective fppf base change detects whether an actual group map is invertible. -/
theorem isIso_of_baseChange_of_fppf {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] : IsIso f := by
  let : IsIso ((GroupScheme.baseChange p).map f).hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget U).map
      ((GroupScheme.baseChange p).map f).hom.hom))
  have : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @LocallyOfFinitePresentation)
      (baseChange_map_isPullback p f)
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget S).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    infer_instance
  have : IsIso f.hom.hom := isIso_of_reflects_iso f.hom.hom (Over.forget S)
  let e : H ≅ G := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- The actual isomorphism recovered from invertibility after an fppf cover. -/
def isoOfFppfBaseChange {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] : H ≅ G :=
  letI := isIso_of_baseChange_of_fppf p f
  asIso f

@[simp]
theorem isoOfFppfBaseChange_hom {H G : GroupScheme S} (f : H ⟶ G)
    [IsIso ((GroupScheme.baseChange p).map f)] :
    (isoOfFppfBaseChange p f).hom = f := rfl

end Langlands.GroupScheme

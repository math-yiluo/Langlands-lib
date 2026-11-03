import Langlands.AlgebraicGeometry.Morphisms.FpqcFiniteDescent
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionHelpers
import Langlands.GroupScheme.CentralIsogeny.FpqcReflectionStatement

/-! # fpqc reflection of central isogenies -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.GroupScheme

/-- The underlying scheme morphism of a base-changed homomorphism is the base change of the
original underlying morphism along the projection from the base-changed target. -/
theorem baseChange_map_isPullback {S S' : Scheme.{u}} (b : S' ⟶ S) {G H : GroupScheme S}
    (f : G ⟶ H) :
    IsPullback ((GroupScheme.baseChange b).map f).hom.hom.left (pullback.fst G.X.hom b)
      (pullback.fst H.X.hom b) f.hom.hom.left := by
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd H.X.hom b)
      (pullback.fst G.X.hom b) b (f.hom.hom.left ≫ H.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback G.X.hom b).flip
  exact houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst H.X.hom b =
        pullback.fst G.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback H.X.hom b).flip

set_option backward.isDefEq.respectTransparency.types false in
/-- An fpqc change of base reflects central isogenies: finiteness, flatness, surjectivity and
local finite presentation descend along the fpqc projection of the target, and centrality of
the full kernel is reflected on every test scheme. -/
theorem centralIsogenyFpqcReflection : CentralIsogenyFpqcReflectionStatement.{u} := by
  intro S S' b _ _ _ G H f hf
  have hp := baseChange_map_isPullback b f
  have hQ : (@Surjective ⊓ @Flat ⊓ @QuasiCompact : MorphismProperty Scheme.{u})
      (pullback.fst H.X.hom b) :=
    ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩
  refine ⟨⟨?_, ?_, ?_⟩, ?_, isCentral_kernelι_of_baseChange b f hf.isCentral_kernelι⟩
  · exact MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.isFinite
  · exact MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.flat
  · exact MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.surjective
  · exact MorphismProperty.of_isPullback_of_descendsAlong hp hQ hf.locallyOfFinitePresentation

end Langlands.GroupScheme

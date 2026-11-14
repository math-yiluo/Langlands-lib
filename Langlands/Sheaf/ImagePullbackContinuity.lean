import Mathlib.CategoryTheory.Sites.CoverPreserving
import Mathlib.CategoryTheory.Sites.PrecoverageToGrothendieck
import Mathlib.CategoryTheory.Limits.Shapes.Pullback.IsPullback.Basic

/-!
# Continuity of functors whose images of some squares are pullbacks

Let `F : C ⥤ D` be a functor such that every cospan `V → U ← W` of `C` has a commutative square
over it whose image under `F` is a pullback square of `D`. Then for precoverages `J` on `C`
and `K` on `D` such that `F` sends `J`-coverings to `K`-coverings, `F` is continuous for the
generated Grothendieck topologies. No pullbacks in `D` other than these images are needed.

The intended use is the forgetful functor `Qét(X(G)) ⥤ Qét(X)` from Berkovich's site of a
`G`-space `X`, whose continuity is the statement that the morphism `b : X → X(G)` is a
morphism of sites.
-/

namespace Langlands.Sheaf

open CategoryTheory CategoryTheory.Limits Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Every cospan `f : V ⟶ U`, `g : W ⟶ U` of `C` has a commutative square
`p₁ ≫ f = p₂ ≫ g` over it whose image under `F` is a pullback square. -/
def HasImagePullbacks (F : C ⥤ D) : Prop :=
  ∀ ⦃U V W : C⦄ (f : V ⟶ U) (g : W ⟶ U), ∃ (P : C) (p₁ : P ⟶ V) (p₂ : P ⟶ W),
    p₁ ≫ f = p₂ ≫ g ∧ IsPullback (F.map p₁) (F.map p₂) (F.map f) (F.map g)

namespace HasImagePullbacks

/-- A functor from a category with pullbacks which preserves pullbacks has image pullbacks:
the pullback squares themselves. -/
theorem of_hasPullbacks (F : C ⥤ D) [HasPullbacks C] [PreservesLimitsOfShape WalkingCospan F] :
    HasImagePullbacks F := fun _ _ _ f g =>
  ⟨pullback f g, pullback.fst f g, pullback.snd f g, pullback.condition,
    F.map_isPullback (IsPullback.of_hasPullback f g)⟩

variable {F : C ⥤ D} (hF : HasImagePullbacks F)
include hF

/-- A functor with image pullbacks is compatible-preserving: two arrows into the images of
members of a family, with the same composite, factor through the image of a common square. -/
theorem compatiblePreserving (K : GrothendieckTopology D) : CompatiblePreserving.{w} K F where
  compatible ℱ Z T x hx Y₁ Y₂ X f₁ f₂ g₁ g₂ hg₁ hg₂ he := by
    obtain ⟨P, p₁, p₂, hp, hpb⟩ := hF g₁ g₂
    have h1 := hpb.lift_fst f₁ f₂ he
    have h2 := hpb.lift_snd f₁ f₂ he
    generalize hpb.lift f₁ f₂ he = m at h1 h2
    subst h1 h2
    rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply]
    exact congrArg (ℱ.obj.map m.op) (hx p₁ p₂ hg₁ hg₂ hp)

/-- A functor with image pullbacks which sends `J`-coverings to `K`-coverings sends covering
sieves of the generated topology to covering sieves. The proof is by induction on the
generation of the topology; the pullback step uses the image pullbacks. -/
theorem coverPreserving (J : Precoverage C) (K : Precoverage D) (hJK : J ≤ K.comap F) :
    CoverPreserving J.toGrothendieck K.toGrothendieck F where
  cover_preserve {U} S hS := by
    change J.Saturate U S at hS
    induction hS with
    | of U R hR =>
      refine K.toGrothendieck.superset_covering ?_
        (Precoverage.generate_mem_toGrothendieck (hJK U hR))
      rw [Sieve.generate_le_iff]
      intro Y g hg
      cases hg with
      | of hf => exact ⟨_, _, 𝟙 _, ⟨_, 𝟙 _, _, hf, Category.id_comp _⟩, (Category.id_comp _).symm⟩
    | top U =>
      rw [Sieve.functorPushforward_top]
      exact K.toGrothendieck.top_mem _
    | pullback U S _ V f ih =>
      refine K.toGrothendieck.superset_covering ?_ (K.toGrothendieck.pullback_stable (F.map f) ih)
      rintro T h ⟨W, s, k, hs, hk⟩
      obtain ⟨P, p₁, p₂, hp, hpb⟩ := hF f s
      refine ⟨P, p₁, hpb.lift h k hk, ?_, (hpb.lift_fst h k hk).symm⟩
      change S.arrows (p₁ ≫ f)
      rw [hp]
      exact S.downward_closed hs p₂
    | transitive U S R _ _ ihS ihR =>
      refine K.toGrothendieck.transitive ihS _ ?_
      rintro T h ⟨W, s, k, hs, rfl⟩
      refine K.toGrothendieck.superset_covering ?_ (K.toGrothendieck.pullback_stable k (ihR hs))
      rintro T' m ⟨W', r, n, hr, hn⟩
      refine ⟨W', r ≫ s, n, hr, ?_⟩
      rw [Functor.map_comp, ← Category.assoc n, ← hn, Category.assoc]

/-- A functor with image pullbacks which sends `J`-coverings to `K`-coverings is continuous
for the generated topologies: precomposition with it sends sheaves to sheaves. -/
theorem isContinuous (J : Precoverage C) (K : Precoverage D) (hJK : J ≤ K.comap F) :
    F.IsContinuous J.toGrothendieck K.toGrothendieck :=
  Functor.isContinuous_of_coverPreserving (hF.compatiblePreserving _)
    (hF.coverPreserving J K hJK)

end HasImagePullbacks

end Langlands.Sheaf

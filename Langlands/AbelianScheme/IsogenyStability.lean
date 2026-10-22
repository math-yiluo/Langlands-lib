import Langlands.AbelianScheme.IsogenyStabilityStatement
import Mathlib.CategoryTheory.MorphismProperty.Limits

/-! # Proof of stability of relative isogenies -/

universe u

open CategoryTheory AlgebraicGeometry

namespace Langlands.GroupScheme

instance : isogenyProperty.{u}.ContainsIdentities where
  id_mem _ := ⟨inferInstance, inferInstance, inferInstance⟩

instance : isogenyProperty.{u}.IsStableUnderComposition where
  comp_mem f g hf hg :=
    ⟨MorphismProperty.comp_mem (W := @IsFinite) f g hf.1 hg.1,
      MorphismProperty.comp_mem (W := @Flat) f g hf.2.1 hg.2.1,
      ⟨hg.2.2.surj.comp hf.2.2.surj⟩⟩

instance : isogenyProperty.{u}.IsStableUnderBaseChange where
  of_isPullback h hf :=
    ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @IsFinite) h hf.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) h hf.2.1,
      MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Surjective) h hf.2.2⟩

theorem isIsogeny_id {S : Scheme.{u}} (G : Grp (Over S)) :
    IsIsogeny (𝟙 G) :=
  isogenyProperty.id_mem G.X.left

theorem IsIsogeny.comp {S : Scheme.{u}} {G H K : Grp (Over S)}
    {f : G ⟶ H} {g : H ⟶ K} (hf : IsIsogeny f) (hg : IsIsogeny g) :
    IsIsogeny (f ≫ g) :=
  isogenyProperty.comp_mem f.hom.hom.left g.hom.hom.left hf hg

theorem IsIsogeny.baseChange {S T : Scheme.{u}} (b : T ⟶ S)
    {G H : Grp (Over S)} {f : G ⟶ H} (hf : IsIsogeny f) :
    IsIsogeny ((Over.pullback b).mapGrp.map f) :=
  isogenyProperty.overPullbackMap b f.hom.hom hf

theorem isogenyStability : IsogenyStabilityStatement.{u} :=
  ⟨fun _ G => isIsogeny_id G,
    fun _ _ _ _ _ _ hf hg => hf.comp hg,
    fun _ _ b _ _ _ hf => hf.baseChange b⟩

end Langlands.GroupScheme

import Langlands.GroupScheme.SubgroupBaseChange
import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent

/-! # Reflection of group-scheme isomorphisms under fpqc base change -/

set_option backward.isDefEq.respectTransparency false

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.GroupScheme

variable {S S' : Scheme.{u}} (b : S' ⟶ S)
variable {H G : GroupScheme S}

/-- An fpqc base change detects whether a given group homomorphism is an isomorphism. -/
theorem isIso_of_baseChange [Surjective b] [Flat b] [QuasiCompact b]
    (f : H ⟶ G) [IsIso ((GroupScheme.baseChange b).map f)] : IsIso f := by
  have : IsIso ((GroupScheme.baseChange b).map f).hom.hom := inferInstance
  have : IsIso ((GroupScheme.baseChange b).map f).hom.hom.left :=
    inferInstanceAs (IsIso ((Over.forget S').map
      ((GroupScheme.baseChange b).map f).hom.hom))
  have houter : IsPullback
      (((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.snd G.X.hom b)
      (pullback.fst H.X.hom b) b (f.hom.hom.left ≫ G.X.hom) := by
    change IsPullback (((Over.pullback b).map f.hom.hom).left ≫ _) _ _ _
    simpa only [Over.w f.hom.hom, Over.pullback_map_left, pullback.lift_snd] using
      (IsPullback.of_hasPullback H.X.hom b).flip
  have hp := houter.of_right
    (show ((GroupScheme.baseChange b).map f).hom.hom.left ≫ pullback.fst G.X.hom b =
        pullback.fst H.X.hom b ≫ f.hom.hom.left by
      change ((Over.pullback b).map f.hom.hom).left ≫ _ = _
      simp only [Over.pullback_map_left, pullback.lift_fst])
    (IsPullback.of_hasPullback G.X.hom b).flip
  have hIso : IsIso f.hom.hom.left :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme)
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hp
      ⟨⟨inferInstance, inferInstance⟩, inferInstance⟩ inferInstance
  have : IsIso ((Over.forget S).map f.hom.hom) := by
    change IsIso f.hom.hom.left
    exact hIso
  have hOver : IsIso f.hom.hom :=
    isIso_of_reflects_iso f.hom.hom (Over.forget S)
  let e : H ≅ G := Grp.mkIso' (asIso f.hom.hom)
  change IsIso e.hom
  infer_instance

/-- The isomorphism associated to a homomorphism detected to be invertible after fpqc base change. -/
def isoOfBaseChange [Surjective b] [Flat b] [QuasiCompact b]
    (f : H ⟶ G) [IsIso ((GroupScheme.baseChange b).map f)] : H ≅ G :=
  letI := isIso_of_baseChange b f
  asIso f

@[simp]
theorem isoOfBaseChange_hom [Surjective b] [Flat b] [QuasiCompact b]
    (f : H ⟶ G) [IsIso ((GroupScheme.baseChange b).map f)] :
    (isoOfBaseChange b f).hom = f :=
  rfl

section Field

variable (k K : Type u) [Field k] [Field K] [Algebra k K]

/-- The map of spectra of a field extension is faithfully flat and quasi-compact. -/
theorem fieldExtension_fpqc :
    Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      QuasiCompact (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
  have h : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) ∧
      Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    apply (flat_and_surjective_SpecMap_iff (CommRingCat.ofHom (algebraMap k K))).2
    change (algebraMap k K).FaithfullyFlat
    rw [RingHom.faithfullyFlat_algebraMap_iff]
    infer_instance
  exact ⟨h.2, h.1, inferInstance⟩

end Field

end Langlands.GroupScheme

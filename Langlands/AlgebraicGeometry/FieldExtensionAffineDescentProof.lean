import Mathlib
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat
import Langlands.AlgebraicGeometry.FieldExtensionAffineDescentStatement

/-!
# Affineness descends along arbitrary field extensions

Authors: Worker 1366 and Worker 1072.

The proof derives the qcqs hypotheses needed for flat base change of global sections,
then descends the canonical affinization isomorphism.
-/

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace Langlands.AlgebraicGeometry

namespace FieldExtensionAffineDescent

universe u

variable {k K : Type u} [Field k] [Field K] [Algebra k K]

/-- Every extension of fields is faithfully flat. -/
lemma faithfullyFlat_algebraMap :
    (CommRingCat.ofHom (algebraMap k K)).hom.FaithfullyFlat :=
  RingHom.faithfullyFlat_algebraMap_iff.2 inferInstance

local instance : Flat (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ((flat_and_surjective_SpecMap_iff _).2 faithfullyFlat_algebraMap).1

local instance : Surjective (Spec.map (CommRingCat.ofHom (algebraMap k K))) :=
  ((flat_and_surjective_SpecMap_iff _).2 faithfullyFlat_algebraMap).2

/-- Quasi-compactness follows from the continuous surjection from the affine base change. -/
lemma compactSpace_of_isAffine_pullback {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] :
    CompactSpace X :=
  Function.Surjective.compactSpace
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).continuous
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).surjective

/-- Quasi-separatedness descends along a surjective quasi-compact scheme morphism. -/
lemma quasiSeparatedSpace_of_surjective {Y X : Scheme.{u}} (p : Y ⟶ X) [Surjective p]
    [QuasiCompact p] [QuasiSeparatedSpace Y] : QuasiSeparatedSpace X := by
  refine ⟨fun U V hU hUc hV hVc ↦ ?_⟩
  have h : IsCompact (p.base ⁻¹' U ∩ p.base ⁻¹' V) :=
    QuasiSeparatedSpace.inter_isCompact _ _ (hU.preimage p.continuous)
      (QuasiCompact.isCompact_preimage (f := p) U hU hUc) (hV.preimage p.continuous)
      (QuasiCompact.isCompact_preimage (f := p) V hV hVc)
  have := h.image p.continuous
  rwa [← Set.preimage_inter, Set.image_preimage_eq _ p.surjective] at this

/-- Flat base change of global sections makes the affinization square cartesian. -/
lemma isPullback_toSpecΓ {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [CompactSpace X] [QuasiSeparatedSpace X] :
    IsPullback (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toSpecΓ
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
      (Spec.map (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop)
      X.toSpecΓ := by
  have hpo := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat f K
  have hR := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  refine IsPullback.of_right ?_ (Scheme.toSpecΓ_naturality _).symm hR
  have htop : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).toSpecΓ ≫
      Spec.map ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫
        (pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) =
      pullback.snd f (Spec.map (CommRingCat.ofHom (algebraMap k K))) := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  have hbot : X.toSpecΓ ≫ Spec.map ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appTop) =
      f := by
    rw [Spec.map_comp, ← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv,
      Category.comp_id]
  rw [htop, hbot]
  exact (IsPullback.of_hasPullback _ _).flip

/-- Descend the affinization isomorphism along the induced fpqc map of spectra. -/
theorem isAffine_of_isAffine_pullback {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of k))
    [IsAffine (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))))] : IsAffine X := by
  have : CompactSpace X := compactSpace_of_isAffine_pullback (K := K) f
  have : QuasiSeparatedSpace X :=
    quasiSeparatedSpace_of_surjective
      (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))))
  have hpb := isPullback_toSpecΓ (K := K) f
  have hpo := isPushout_appTop_pullback_fst_appTop_pullback_snd_of_flat f K
  have hR := isPullback_SpecMap_of_isPushout _ _ _ _ hpo
  have hflat : Flat (Spec.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) :=
    MorphismProperty.of_isPullback (P := @Flat) hR inferInstance
  have hsurj : Surjective (Spec.map (pullback.fst f
      (Spec.map (CommRingCat.ofHom (algebraMap k K)))).appTop) :=
    MorphismProperty.of_isPullback (P := @Surjective) hR inferInstance
  have hiso : IsIso X.toSpecΓ :=
    MorphismProperty.of_isPullback_of_descendsAlong
      (P := MorphismProperty.isomorphisms Scheme.{u})
      (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) hpb
      ⟨⟨hsurj, hflat⟩, inferInstance⟩ (inferInstanceAs (IsIso _))
  exact ⟨hiso⟩

end FieldExtensionAffineDescent

/-- Affineness descends along every extension of fields, for an arbitrary scheme. -/
theorem fieldExtensionAffineDescent : FieldExtensionAffineDescentStatement.{u} :=
  fun _ K _ _ _ _ f _ ↦ FieldExtensionAffineDescent.isAffine_of_isAffine_pullback (K := K) f

end Langlands.AlgebraicGeometry

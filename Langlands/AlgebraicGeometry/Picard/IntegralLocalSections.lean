import Langlands.AlgebraicGeometry.Picard.UnramifiedSections
import Mathlib.AlgebraicGeometry.Birational.RationalMap
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.IsIso

/-! # Integral separated morphisms with local sections -/

universe u
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
noncomputable section
namespace Langlands.AlgebraicGeometry

set_option backward.isDefEq.respectTransparency false in
theorem isIso_restrict_of_integral_section
    {S Z : Scheme.{u}} [IsIntegral Z]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [FormallyUnramified f]
    (U : S.Opens) [Nonempty U] (s : U.toScheme ⟶ Z) (hs : s ≫ f = U.ι) :
    IsIso (f ∣_ U) := by
  let W := f ⁻¹ᵁ U
  have : IsOpenImmersion (s ≫ f) := by rw [hs]; infer_instance
  have : IsOpenImmersion s := isOpenImmersion_of_comp_of_unramified s f
  have hr : Set.range s ⊆ Set.range W.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨s x, ?_⟩, rfl⟩
    change f (s x) ∈ U
    change (s ≫ f) x ∈ U
    rw [hs]
    exact x.2
  let t := IsOpenImmersion.lift W.ι s hr
  have ht : t ≫ W.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hq : t ≫ (f ∣_ U) = 𝟙 U.toScheme := by
    apply (cancel_mono U.ι).mp
    rw [Category.assoc, morphismRestrict_ι, ← Category.assoc, ht, hs,
      Category.id_comp]
  have : IsOpenImmersion t := by dsimp [t]; infer_instance
  have : IsClosedImmersion (t ≫ (f ∣_ U)) := by rw [hq]; infer_instance
  have : IsClosedImmersion t := IsClosedImmersion.of_comp t (f ∣_ U)
  have : Nonempty W.toScheme := Nonempty.map t inferInstance
  have : IsDominant t := ⟨t.isOpenEmbedding.isOpen_range.dense
    (Set.range_nonempty t)⟩
  have : Surjective t := surjective_of_isDominant_of_isClosed_range t
    t.isClosedEmbedding.isClosed_range
  have : IsIso t := (isIso_iff_isOpenImmersion_and_surjective t).mpr
    ⟨inferInstance, inferInstance⟩
  exact IsIso.of_isIso_fac_left hq

set_option backward.isDefEq.respectTransparency false in
theorem isOpenImmersion_of_integral_local_sections
    {S Z : Scheme.{u}} [IsIntegral Z]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [FormallyUnramified f]
    (hsec : ∀ z : Z, ∃ (U : S.Opens), f z ∈ U ∧
      ∃ s : U.toScheme ⟶ Z, s ≫ f = U.ι) : IsOpenImmersion f := by
  have hlocal (z : Z) : ∃ U : S.Opens, f z ∈ U ∧ IsIso (f ∣_ U) := by
    obtain ⟨U, hz, s, hs⟩ := hsec z
    have : Nonempty U := ⟨⟨f z, hz⟩⟩
    exact ⟨U, hz, isIso_restrict_of_integral_section f U s hs⟩
  have hinj : Function.Injective f := by
    intro x y hxy
    obtain ⟨U, hx, hi⟩ := hlocal x
    have := hi
    have hy : f y ∈ U := hxy ▸ hx
    have he : (f ∣_ U) ⟨x, hx⟩ = (f ∣_ U) ⟨y, hy⟩ := by
      apply Subtype.ext
      exact (congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ S => g ⟨x, hx⟩)
        (morphismRestrict_ι f U)).trans
        (hxy.trans (congrArg (fun g : (f ⁻¹ᵁ U).toScheme ⟶ S => g ⟨y, hy⟩)
          (morphismRestrict_ι f U)).symm)
    exact congrArg Subtype.val ((f ∣_ U).isOpenEmbedding.injective he)
  apply IsOpenImmersion.of_forall_source_exists f hinj
  intro z
  obtain ⟨U, hz, hi⟩ := hlocal z
  have := hi
  refine ⟨(f ⁻¹ᵁ U).toScheme, (f ⁻¹ᵁ U).ι, inferInstance, ?_, ?_⟩
  · exact ⟨⟨z, hz⟩, rfl⟩
  · rw [← morphismRestrict_ι]
    infer_instance

set_option backward.isDefEq.respectTransparency false in
theorem isOpenImmersion_of_isIso_stalkMap_of_integral
    {S Z : Scheme.{u}} [IsIntegral S] [IsIntegral Z]
    (f : Z ⟶ S) [IsSeparated f] [LocallyOfFiniteType f] [FormallyUnramified f]
    (hf : ∀ z : Z, IsIso (f.stalkMap z)) : IsOpenImmersion f := by
  apply isOpenImmersion_of_integral_local_sections f
  intro z
  have := hf z
  let a : Spec (S.presheaf.stalk (f z)) ⟶ Z :=
    Spec.map (inv (f.stalkMap z)) ≫ Z.fromSpecStalk z
  have ha : a ≫ f = S.fromSpecStalk (f z) := by
    dsimp [a]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  let r := Scheme.PartialMap.ofFromSpecStalk (𝟙 S) f a (by simpa using ha)
  refine ⟨r.domain, Scheme.PartialMap.mem_domain_ofFromSpecStalk _ _ _ _, r.hom, ?_⟩
  simpa [r] using Scheme.PartialMap.ofFromSpecStalk_comp (𝟙 S) f a (by simpa using ha)

end Langlands.AlgebraicGeometry

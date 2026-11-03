import Mathlib.AlgebraicGeometry.Morphisms.FlatDescent
import Mathlib.AlgebraicGeometry.Morphisms.LocalFlatDescent
import Mathlib.AlgebraicGeometry.ZariskisMainTheorem

/-! # fpqc descent of flatness, separatedness, properness and finiteness -/

universe u

open CategoryTheory CategoryTheory.Limits MorphismProperty AlgebraicGeometry

namespace Langlands.AlgebraicGeometry.FpqcDescent

/-- Flatness of ring maps descends along faithfully flat ring maps. -/
theorem flat_codescendsAlong_faithfullyFlat :
    RingHom.CodescendsAlong RingHom.Flat RingHom.FaithfullyFlat := by
  refine .mk _ RingHom.Flat.respectsIso fun R S T _ _ _ _ _ h h' ↦ ?_
  rw [RingHom.flat_algebraMap_iff] at h' ⊢
  rw [RingHom.faithfullyFlat_algebraMap_iff] at h
  exact Module.Flat.of_flat_tensorProduct R T S

/-- Flatness satisfies fpqc descent. -/
instance descendsAlong_flat_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @Flat (@Surjective ⊓ @Flat ⊓ @QuasiCompact) :=
  HasRingHomProperty.descendsAlong_flat flat_codescendsAlong_faithfullyFlat

/-- A morphism is separated exactly when its diagonal is universally closed. -/
theorem isSeparated_eq_diagonal_universallyClosed :
    @IsSeparated = MorphismProperty.diagonal @UniversallyClosed := by
  ext X Y f
  change IsSeparated f ↔ UniversallyClosed (pullback.diagonal f)
  rw [isSeparated_iff]
  constructor
  · intro h
    infer_instance
  · intro h
    exact .of_isPreimmersion _ (pullback.diagonal f).isClosedMap.isClosed_range

set_option backward.isDefEq.respectTransparency.types false in
/-- Separatedness satisfies fpqc descent. -/
instance descendsAlong_isSeparated_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsSeparated (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isSeparated_eq_diagonal_universallyClosed]
  infer_instance

set_option backward.isDefEq.respectTransparency.types false in
/-- Properness satisfies fpqc descent. -/
instance descendsAlong_isProper_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsProper (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  rw [isProper_eq]
  infer_instance

/-- Along a surjective map, finiteness of all fibres of a base change implies finiteness of all
fibres of the original map. -/
theorem finite_preimage_singleton_of_pullback_fst {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z)
    [Surjective f] (h : ∀ x, (pullback.fst f g ⁻¹' {x}).Finite) (z : Z) :
    (g ⁻¹' {z}).Finite := by
  obtain ⟨x, hx⟩ := f.surjective z
  refine ((h x).image (pullback.snd f g)).subset ?_
  intro y hy
  obtain ⟨a, ha, ha'⟩ := Scheme.Pullback.exists_preimage_pullback x y (hx.trans hy.symm)
  exact ⟨a, ha, ha'⟩

set_option backward.isDefEq.respectTransparency.types false in
/-- Finiteness satisfies fpqc descent. Properness descends, and local quasi-finiteness of the
proper descended map follows from finiteness of its fibres. -/
instance descendsAlong_isFinite_surjective_inf_flat_inf_quasicompact :
    DescendsAlong @IsFinite (@Surjective ⊓ @Flat ⊓ @QuasiCompact) := by
  apply DescendsAlong.mk'
  intro X Y Z f g _ hf hfst
  have : IsFinite (pullback.fst f g) := hfst
  have : Surjective f := hf.1.1
  have : IsProper g :=
    of_pullback_fst_of_descendsAlong (P := @IsProper) hf inferInstance
  have : LocallyQuasiFinite g :=
    .of_finite_preimage_singleton g
      (finite_preimage_singleton_of_pullback_fst f g (pullback.fst f g).finite_preimage_singleton)
  exact (IsFinite.iff_isProper_and_locallyQuasiFinite g).mpr ⟨inferInstance, inferInstance⟩

end Langlands.AlgebraicGeometry.FpqcDescent

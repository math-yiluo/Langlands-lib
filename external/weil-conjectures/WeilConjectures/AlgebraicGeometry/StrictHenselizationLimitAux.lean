/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.AlgebraicGeometry.Sites.StrictHenselizationLocal
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.Topology.JacobsonSpace
public import Mathlib.RingTheory.Algebraic.Basic

/-!
# Auxiliary lemmas on pointed étale neighbourhoods of a geometric point

For a geometric point `s : Spec Ω ⟶ S` of a scheme `S` over a field `K` we record the
compatibility of the maps `R ⟶ 𝒪^{sh}_{S,s}` from pointed étale neighbourhoods `Spec R` with the
`K`-structures, and show that if `s` lies over a non-closed point and `S` is locally of finite type
over `K`, some neighbourhood carries a function whose value at `s` is transcendental over `K`.
-/

@[expose] public section

universe u

open CategoryTheory Limits

namespace AlgebraicGeometry.Scheme

section Helpers

variable {S : Scheme.{u}} {Ω : Type u} [Field Ω] [IsSepClosed Ω] {s : Spec (.of Ω) ⟶ S}

lemma SpecPointedEtaleNeighborhood.specMap_ι_comp_hom (N : SpecPointedEtaleNeighborhood s) :
    Spec.map N.ι ≫ N.hom = strictLocalizationToBase s := by
  have h : inv ((affineNeighborhoodDiagram s).obj N.toAffine).toSpecΓ =
      Spec.map (Scheme.ΓSpecIso N.R).inv :=
    IsIso.inv_eq_of_hom_inv_id (toSpecΓ_SpecMap_ΓSpecIso_inv N.R)
  rw [← strictLocalizationCone_π_app_hom s N.toAffine, strictLocalizationCone_π_app,
    SpecPointedEtaleNeighborhood.ι, Spec.map_comp, h]
  rfl

/-- The ring of a pointed étale neighbourhood `Spec R` of `s` as an algebra over the ground field
`K` of `S`. -/
lemma SpecPointedEtaleNeighborhood.preimage_comp_ι {K : Type u} [Field K]
    (aS : S ⟶ Spec (.of K)) (N : SpecPointedEtaleNeighborhood s) :
    Spec.preimage (N.hom ≫ aS) ≫ N.ι = Spec.preimage (strictLocalizationToBase s ≫ aS) := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
    N.specMap_ι_comp_hom]

omit [IsSepClosed Ω] in
lemma SpecPointedEtaleNeighborhood.preimage_comp_pt {K : Type u} [Field K]
    (aS : S ⟶ Spec (.of K)) (N : SpecPointedEtaleNeighborhood s) :
    Spec.preimage (N.hom ≫ aS) ≫ N.pt = Spec.preimage (s ≫ aS) := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc, N.w]

omit [IsSepClosed Ω] in
lemma SpecPointedEtaleNeighborhood.finiteType_preimage {K : Type u} [Field K]
    (aS : S ⟶ Spec (.of K)) [LocallyOfFiniteType aS] (N : SpecPointedEtaleNeighborhood s) :
    (Spec.preimage (N.hom ≫ aS)).hom.FiniteType := by
  have : LocallyOfFiniteType (Spec.map (Spec.preimage (N.hom ≫ aS))) := by
    rw [Spec.map_preimage]
    infer_instance
  exact HasRingHomProperty.Spec_iff.mp this

lemma preimage_comp_strictHenselizationEval {K : Type u} [Field K] (aS : S ⟶ Spec (.of K)) :
    Spec.preimage (strictLocalizationToBase s ≫ aS) ≫ strictHenselizationEval s =
      Spec.preimage (s ≫ aS) := by
  refine Spec.map_injective ?_
  rw [Spec.map_comp, Spec.map_preimage, Spec.map_preimage, ← Category.assoc,
    spec_map_strictHenselizationEval_comp_strictLocalizationToBase]

/-- Two pointed étale neighbourhoods `Spec R₁`, `Spec R₂` of `s` are refined by a third one
`Spec R₃`, in the sense that the images of `R₁` and `R₂` in the strict henselization are contained
in that of `R₃`. -/
lemma SpecPointedEtaleNeighborhood.exists_range_subset (N₁ N₂ : SpecPointedEtaleNeighborhood s) :
    ∃ N₃ : SpecPointedEtaleNeighborhood s,
      Set.range N₁.ι ⊆ Set.range N₃.ι ∧ Set.range N₂.ι ⊆ Set.range N₃.ι := by
  have h (N : SpecPointedEtaleNeighborhood s) : Set.range N.ι ⊆
      Set.range (colimit.ι (strictHenselizationDiagram s) (Opposite.op N.toAffine)) := by
    rintro _ ⟨c, rfl⟩
    exact ⟨_, rfl⟩
  obtain ⟨N₃, hN₃⟩ := exists_specPointedEtaleNeighborhood_range_subset
    (IsCofiltered.min N₁.toAffine N₂.toAffine)
  exact ⟨N₃, (h N₁).trans ((range_colimit_ι_subset (IsCofiltered.minToLeft _ _)).trans hN₃),
    (h N₂).trans ((range_colimit_ι_subset (IsCofiltered.minToRight _ _)).trans hN₃)⟩

omit [IsSepClosed Ω] in
/-- If the geometric point `s` of a scheme `S` locally of finite type over a field `K` lies over
a non-closed point, then some pointed étale neighbourhood `Spec R` of `s` has a function `c ∈ R`
whose value at `s` is transcendental over `K`. -/
lemma exists_transcendental_pt {K : Type u} [Field K] (aS : S ⟶ Spec (.of K))
    [LocallyOfFiniteType aS] (hs : ¬ IsClosed {s (IsLocalRing.closedPoint Ω)}) :
    letI : Algebra K Ω := (Spec.preimage (s ≫ aS)).hom.toAlgebra
    ∃ (N : SpecPointedEtaleNeighborhood s) (c : N.R), Transcendental K (N.pt c) := by
  let : Algebra K Ω := (Spec.preimage (s ≫ aS)).hom.toAlgebra
  obtain ⟨R₀, j, hj, hmem, -⟩ := exists_affine_mem_range_and_range_subset
    (x := s (IsLocalRing.closedPoint Ω)) (U := ⊤) trivial
  have hsub : Set.range s ⊆ Set.range j := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint Ω)]
  have hl : IsOpenImmersion.lift j s hsub ≫ j = s := IsOpenImmersion.lift_fac _ _ _
  let N : SpecPointedEtaleNeighborhood s :=
    ⟨R₀, j, inferInstance, Spec.preimage (IsOpenImmersion.lift j s hsub),
      by rw [Spec.map_preimage, hl]⟩
  let : Algebra K R₀ := (Spec.preimage (N.hom ≫ aS)).hom.toAlgebra
  let f : R₀ →ₐ[K] Ω :=
    { N.pt.hom with
      commutes' k := congr($(N.preimage_comp_pt aS) k) }
  by_contra hcon
  push Not at hcon
  have halg : Algebra.IsAlgebraic K f.range := ⟨fun ⟨_, c, rfl⟩ ↦
    (isAlgebraic_algHom_iff f.range.val Subtype.val_injective).1
      (not_not.1 (hcon N c))⟩
  have hfield : IsField f.range := isField_of_isIntegral_of_isField' (Field.toIsField K)
  let := hfield.toField
  have hmax : (RingHom.ker f.toRingHom).IsMaximal := by
    have := RingHom.ker_isMaximal_of_surjective (f.rangeRestrict : R₀ →+* f.range)
      f.rangeRestrict_surjective
    have hker : RingHom.ker (f.rangeRestrict : R₀ →+* f.range) = RingHom.ker f.toRingHom := by
      ext x
      simp [RingHom.mem_ker, Subtype.ext_iff]
    rwa [hker] at this
  let P : Spec R₀ := Spec.map N.pt (IsLocalRing.closedPoint Ω)
  have hP : P.asIdeal = RingHom.ker f.toRingHom := by
    change Ideal.comap N.pt.hom (IsLocalRing.maximalIdeal Ω) = _
    rw [IsLocalRing.maximalIdeal_eq_bot]
    rfl
  have hPc : P ∈ closedPoints (Spec R₀) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal P).2 (hP ▸ hmax)
  have := LocallyOfFiniteType.jacobsonSpace aS
  rw [← j.isOpenEmbedding.preimage_closedPoints] at hPc
  apply hs
  have hjP : j P = s (IsLocalRing.closedPoint Ω) := by
    rw [← Scheme.Hom.comp_apply]
    exact congr($(N.w) (IsLocalRing.closedPoint Ω))
  rw [← hjP]
  exact hPc

end Helpers

end AlgebraicGeometry.Scheme

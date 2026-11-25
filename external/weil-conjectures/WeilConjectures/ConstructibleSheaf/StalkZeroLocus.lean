/-
Copyright (c) 2026 Claude. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import WeilConjectures.ConstructibleSheaf.Restriction
public import WeilConjectures.Mathlib.Topology.Spectral.ConstructibleTopology

/-!
# The vanishing locus of a constructible sheaf

For a sheaf of `Λ`-modules `Q` on the small étale site of `X`, `Etale.stalkZeroLocus Q` is the set
of points of `X` at all of whose geometric points the stalk of `Q` vanishes. For `Q`
constructible:

* vanishing at one geometric point over `x` already gives `x ∈ stalkZeroLocus Q`
  (`AlgebraicGeometry.Etale.mem_stalkZeroLocus_of_isZero_sheafFiber`);
* `stalkZeroLocus Q` is open in the constructible topology
  (`AlgebraicGeometry.Etale.isOpen_constructibleTopology_stalkZeroLocus`).

These are the inputs to Stacks 095M.
-/

@[expose] public section

universe u

open CategoryTheory Limits Opposite Topology

namespace AlgebraicGeometry

open Scheme

/-- A morphism from the spectrum of a field whose point lies in the range of an immersion
factors through it. -/
lemma IsImmersion.exists_comp_eq_of_field {X Y : Scheme.{u}} (f : X ⟶ Y) [IsImmersion f]
    {K : Type u} [Field K] (s : Spec (.of K) ⟶ Y)
    (hs : s.base (IsLocalRing.closedPoint K) ∈ Set.range f.base) : ∃ t, t ≫ f = s := by
  have hr : Set.range s.base ⊆ Set.range f.coborderRange.ι.base := by
    rintro _ ⟨p, rfl⟩
    rw [Scheme.Opens.range_ι]
    have : p = IsLocalRing.closedPoint K := Subsingleton.elim _ _
    subst this
    exact subset_coborder hs
  let s' := IsOpenImmersion.lift f.coborderRange.ι s hr
  have hs' : s' ≫ f.coborderRange.ι = s := IsOpenImmersion.lift_fac _ _ _
  have hmem : s'.base (IsLocalRing.closedPoint K) ∈ Set.range f.liftCoborder.base := by
    obtain ⟨x, hx⟩ := hs
    refine ⟨x, f.coborderRange.ι.isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, f.liftCoborder_ι, hx, ← Scheme.Hom.comp_apply, hs']
  obtain ⟨t, ht, -⟩ := IsClosedImmersion.existsUnique_fac_of_field f.liftCoborder s' hmem
  exact ⟨t, by rw [← f.liftCoborder_ι, ← Category.assoc, ht, hs']⟩

namespace Etale

variable {Λ : Type (u + 1)} [Ring Λ]

/-- For a locally constant `I`, vanishing of the stalk at one geometric point over `x` gives
vanishing at all of them. -/
lemma mem_stalkZeroLocus_of_isLocallyConstantSheaf {X : Scheme.{u}}
    (I : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsLocallyConstantSheaf I]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (h : IsZero ((pointSmallEtale s).sheafFiber.obj I)) :
    s.base (IsLocalRing.closedPoint Ω) ∈ stalkZeroLocus I := by
  obtain ⟨⟨𝒰, hc⟩⟩ := IsLocallyConstantSheaf.nonempty_locallyConstantDatum (F := I)
  obtain ⟨i, v, hv⟩ := 𝒰.exists_eq (s.base (IsLocalRing.closedPoint Ω))
  have : Etale (𝒰.f i) := 𝒰.map_prop i
  obtain ⟨N, ⟨e⟩⟩ := ((isConstant_over_iff_upperStar _ (𝒰.etalePrecoverageToEtale i) I).1
    (hc i)).mem_essImage
  have hN := (isZero_sheafFiber_iff_of_iso I (𝒰.f i) e.symm s ⟨v, hv⟩).1 h
  intro Ω' _ _ s' hs'
  exact (isZero_sheafFiber_iff_of_iso I (𝒰.f i) e.symm s' ⟨v, hv.trans hs'.symm⟩).2 hN

/-- Points of a stratum where the stalks vanish, read on the stratum. -/
lemma mem_stalkZeroLocus_iff_of_isImmersion {X T : Scheme.{u}}
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) (ι : T ⟶ X) [IsImmersion ι] (t : T) :
    ι t ∈ stalkZeroLocus Q ↔ t ∈ stalkZeroLocus ((ι)^*[ModuleCat.{u + 1} Λ].obj Q) := by
  constructor
  · intro h Ω _ _ s hs
    exact (h Ω (s ≫ ι) (by rw [Scheme.Hom.comp_apply, hs])).of_iso
      ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ι s).app Q)
  · intro h Ω _ _ s hs
    obtain ⟨t', rfl⟩ := IsImmersion.exists_comp_eq_of_field ι s ⟨t, hs.symm⟩
    have ht' : t'.base (IsLocalRing.closedPoint Ω) = t := ι.isEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply]; exact hs)
    exact (h Ω t' ht').of_iso ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) ι t').app Q).symm


/-- **For constructible sheaves, vanishing at one geometric point suffices.** -/
lemma mem_stalkZeroLocus_of_isZero_sheafFiber {X : Scheme.{u}}
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf Q]
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X)
    (h : IsZero ((pointSmallEtale s).sheafFiber.obj Q)) :
    s.base (IsLocalRing.closedPoint Ω) ∈ stalkZeroLocus Q := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := Q)
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp
    (S.iUnion_stratum_eq_univ ▸ Set.mem_univ (s.base (IsLocalRing.closedPoint Ω)))
  rw [← S.range_immersion] at hi
  obtain ⟨t, rfl⟩ := IsImmersion.exists_comp_eq_of_field (S.immersion i) s hi
  have := (hS i).toIsLocallyConstantSheaf
  rw [Scheme.Hom.comp_apply, mem_stalkZeroLocus_iff_of_isImmersion]
  exact mem_stalkZeroLocus_of_isLocallyConstantSheaf _ t (h.of_iso
    ((upperStarCompSheafFiberIso (ModuleCat.{u + 1} Λ) (S.immersion i) t).app Q))

/-- **The vanishing locus of a constructible sheaf is open in the constructible topology.** -/
theorem isOpen_constructibleTopology_stalkZeroLocus {X : Scheme.{u}} [CompactSpace X]
    (Q : Sheaf X.smallEtaleTopology (ModuleCat.{u + 1} Λ)) [IsConstructibleSheaf Q] :
    IsOpen[constructibleTopology X] (stalkZeroLocus Q) := by
  obtain ⟨S, hS⟩ := IsConstructibleSheaf.exists_stratification
    (FA := fun M N : ModuleCat.{u + 1} Λ ↦ M →ₗ[Λ] N) (CA := fun M : ModuleCat.{u + 1} Λ ↦ M)
    (F := Q)
  have heq : stalkZeroLocus Q = ⋃ i, (S.stratum i ∩ stalkZeroLocus Q) := by
    rw [← Set.iUnion_inter, S.iUnion_stratum_eq_univ, Set.univ_inter]
  rw [heq]
  refine @isOpen_iUnion X _ (constructibleTopology X) _ fun i ↦ ?_
  have := (hS i).toIsLocallyConstantSheaf
  have hcl := isClopen_stalkZeroLocus ((S.immersion i)^*[ModuleCat.{u + 1} Λ].obj Q)
  obtain ⟨O, hO, hOe⟩ := (S.immersion i).isEmbedding.isInducing.isOpen_iff.mp hcl.isOpen
  have : S.stratum i ∩ stalkZeroLocus Q = S.stratum i ∩ O := by
    rw [← S.range_immersion]
    ext x
    constructor
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      change t ∈ (S.immersion i).base ⁻¹' O
      rw [hOe, ← mem_stalkZeroLocus_iff_of_isImmersion]
      exact hx
    · rintro ⟨⟨t, rfl⟩, hx⟩
      refine ⟨⟨t, rfl⟩, ?_⟩
      rw [mem_stalkZeroLocus_iff_of_isImmersion, ← hOe]
      exact hx
  rw [this]
  exact @IsOpen.inter X (constructibleTopology X) _ _
    (@IsClopen.isOpen X (constructibleTopology X) _
      (S.isConstructible_stratum i).isClopen_constructibleTopology)
    (constructibleTopology_le O hO)

end Etale

end AlgebraicGeometry

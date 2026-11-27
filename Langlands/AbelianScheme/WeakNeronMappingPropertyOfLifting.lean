/-
Copyright 2026 Anthropic, PBC.
Released under the Apache License 2.0; see licenses/Anthropic-FLT/LICENSE.

Modified in Langlands-lib (2026): adapt the Anthropic Lean formalization of Fermat's Last
Theorem, commit 6e837e75355538c7f80bab5b956861e86c4eacc2,
P2M/Sol/S_NeronModelInfra_exists_nhds_extension_of_isProper_of_smooth.lean,
P2M/Sol/S_NeronModelInfra_exists_opens_extension_of_isProper_of_smooth.lean and
P2M/Sol/S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.lean.
The proper target is replaced by a separated scheme mapping to a proper one by a morphism
which is an isomorphism on generic fibres and through which points with values in discrete
valuation rings of ramification index one lift; the smooth test scheme need not be
quasi-compact. The upstream license, NOTICE and ATTRIBUTION.md are retained in
licenses/Anthropic-FLT/.
-/
import Langlands.AbelianScheme.WeakNeronMappingProperty
import Langlands.AlgebraicGeometry.SmoothDvrStalkRamification
import Langlands.AlgebraicGeometry.Picard.DiscreteValuationRingSelfProductLineBundleExtensionProof
import Langlands.AnthropicFLT.Theorems.Thm_AlgebraicGeometry_Smooth_isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
import Langlands.AnthropicFLT.Theorems.Thm_NeronModelInfra_genericFibreRestrict_injective_of_flat_of_isSeparated
import Langlands.AnthropicFLT.P2M.Sol.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk

/-! # The weak Néron mapping property from lifting over ramification index one -/

noncomputable section

universe u

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry NeronModelInfra

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

namespace Langlands.AbelianScheme.WeakNeronLifting

open Langlands.AlgebraicGeometry

/-- Every point of `X` with values in a discrete valuation ring of ramification index one
over `R` lifts along `h : W ⟶ X`. -/
def RamificationIndexOneLifting (R : Type u) [CommRing R] [IsLocalRing R] {X W : Scheme.{u}}
    (f : X ⟶ Spec (CommRingCat.of R)) (h : W ⟶ X) : Prop :=
  ∀ (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [Algebra R R']
    [IsLocalHom (algebraMap R R')], IsRamificationIndexOne R R' →
    ∀ a : Spec (CommRingCat.of R') ⟶ X,
      a ≫ f = Spec.map (CommRingCat.ofHom (algebraMap R R')) →
      ∃ a' : Spec (CommRingCat.of R') ⟶ W, a' ≫ h = a

open P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap
  in
/-- A point of an integral scheme lies in the domain of the rational map represented by a
partial map as soon as the map on the function field extends, compatibly with the base, to
the spectrum of the stalk at the point. -/
theorem mem_domain_toRationalMap_of_lift {X Y S : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)
    [IsIntegral X] [LocallyOfFiniteType sY] (f : X.PartialMap Y) (x : X)
    (l : Spec (X.presheaf.stalk x) ⟶ Y) (hl₂ : l ≫ sY = X.fromSpecStalk x ≫ sX)
    (hl₁ : Spec.map (X.presheaf.stalkSpecializes
      ((genericPoint_spec X).specializes trivial)) ≫ l = f.fromFunctionField) :
    x ∈ f.toRationalMap.domain := by
  refine Scheme.RationalMap.mem_domain.mpr
    ⟨Scheme.PartialMap.ofFromSpecStalk sX sY l hl₂,
     Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂, ?_⟩
  apply Scheme.RationalMap.eq_of_fromFunctionField_eq
  rw [Scheme.RationalMap.fromFunctionField_toRationalMap,
    Scheme.RationalMap.fromFunctionField_toRationalMap,
    partialMap_fromFunctionField_eq_of_mem _
      (Scheme.PartialMap.mem_domain_ofFromSpecStalk sX sY l hl₂),
    Scheme.PartialMap.fromSpecStalkOfMem_ofFromSpecStalk sX sY l hl₂]
  exact hl₁

variable (R K : Type u) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]
  [Field K] [Algebra R K] [IsFractionRing R K]

/-- A point of the spectrum of a discrete valuation ring other than the closed point is
the generic point, the image of the spectrum of the fraction field. -/
theorem mem_range_of_ne_closedPoint (s : Spec (CommRingCat.of R))
    (hs : s ≠ IsLocalRing.closedPoint R) :
    s ∈ Set.range (specGenericFibreInclusion R K).base := by
  refine ⟨IsLocalRing.closedPoint K, ?_⟩
  apply PrimeSpectrum.ext
  have h1 : ((specGenericFibreInclusion R K).base (IsLocalRing.closedPoint K)).asIdeal = ⊥ := by
    change Ideal.comap (algebraMap R K) (IsLocalRing.maximalIdeal K) = ⊥
    rw [IsLocalRing.maximalIdeal_eq_bot (R := K), Ideal.comap_bot_of_injective _
      (IsFractionRing.injective R K)]
  have h2 : s.asIdeal = ⊥ := by
    by_contra hne
    apply hs
    apply PrimeSpectrum.ext
    exact IsLocalRing.eq_maximalIdeal (Ring.DimensionLEOne.maximalOfPrime hne s.isPrime)
  rw [h1, h2]

variable {R K}
variable {X W : Scheme.{u}} {f : X ⟶ Spec (CommRingCat.of R)} {w : W ⟶ Spec (CommRingCat.of R)}
  {h : W ⟶ X}

/-- Two morphisms to `W` over the generic point which agree after composing with a map
`W ⟶ X` that is an isomorphism on generic fibres are equal. -/
theorem eq_of_comp_eq (hw : h ≫ f = w)
    (hgen : IsIso (pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp])))
    {Z : Scheme.{u}} (α β : Z ⟶ W) (hαβ : α ≫ h = β ≫ h) (hww : α ≫ w = β ≫ w)
    (hrange : Set.range (α ≫ w).base ⊆ Set.range (specGenericFibreInclusion R K).base) :
    α = β := by
  have hηo : IsOpenImmersion (specGenericFibreInclusion R K) :=
    isOpenImmersion_spec_fractionRing_of_dvr R K
  let γ := IsOpenImmersion.lift (specGenericFibreInclusion R K) (α ≫ w) hrange
  have hγ : γ ≫ specGenericFibreInclusion R K = α ≫ w := IsOpenImmersion.lift_fac _ _ _
  let α' := pullback.lift α γ hγ.symm
  let β' := pullback.lift β γ (by rw [hγ, hww])
  have hmap : α' ≫ pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp]) =
      β' ≫ pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp]) := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst, α', β', pullback.lift_fst_assoc]
      exact hαβ
    · simp only [Category.assoc, pullback.lift_snd, α', β', Category.comp_id]
  have hα'β' : α' = β' := (cancel_mono _).mp hmap
  have := congrArg (fun q => q ≫ pullback.fst w (specGenericFibreInclusion R K)) hα'β'
  simpa only [α', β', pullback.lift_fst] using this

/-- A point of a scheme over a discrete valuation ring which does not lie over the closed
point lies in the generic fibre. -/
theorem mem_opensRange_pullbackFst_of_ne_closedPoint
    [IsOpenImmersion (specGenericFibreInclusion R K)] {T : Scheme.{u}}
    (t : T ⟶ Spec (CommRingCat.of R)) (x : T) (hx : t.base x ≠ IsLocalRing.closedPoint R) :
    x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange := by
  rw [Scheme.Hom.opensRange_pullbackFst]
  change t.base x ∈ (specGenericFibreInclusion R K).opensRange
  rw [Scheme.Hom.mem_opensRange]
  exact mem_range_of_ne_closedPoint R K _ hx

open P2MW.S_AlgebraicGeometry_Scheme_PartialMap_mem_domain_toRationalMap_of_valuationRing_stalk.ValuativePartialMap
  in
/-- Local extension at a generic point of the closed fibre of a quasi-compact smooth test
scheme. -/
theorem exists_nhds_extension_of_quasiCompact [IsProper f] [LocallyOfFiniteType w]
    [IsSeparated w] (hw : h ≫ f = w)
    (hgen : IsIso (pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp])))
    (hlift : RamificationIndexOneLifting R f h)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t] [QuasiCompact t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd w (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgenη : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) w),
      (genericFibreRestrict R K w (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t
          (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  classical
  have hoi : IsOpenImmersion (specGenericFibreInclusion R K) :=
    isOpenImmersion_spec_fractionRing_of_dvr R K
  have : IsLocallyNoetherian T := LocallyOfFiniteType.isLocallyNoetherian t
  have : CompactSpace T := QuasiCompact.compactSpace_of_compactSpace t
  have : IsNoetherian T := {}
  have : IsReduced T := by
    have : ∀ x : T, _root_.IsReduced (T.presheaf.stalk x) := fun x =>
      have := (AlgebraicGeometry.Smooth.isDomain_and_isIntegrallyClosed_stalk_of_isDiscreteValuationRing
        R t x).1
      inferInstance
    exact isReduced_of_isReduced_stalk T
  obtain ⟨hdom, hdvr⟩ :=
    AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes R t η hηs hgenη
  let ξ : T := (T.fromSpecStalk η).base ⟨⊥, Ideal.isPrime_bot⟩
  have hξη : ξ ⤳ η := by
    have : ξ ∈ Set.range (T.fromSpecStalk η).base := ⟨_, rfl⟩
    rw [Scheme.range_fromSpecStalk] at this
    exact this
  have hξne : ξ ≠ η := by
    intro h
    have h2 : (T.fromSpecStalk η).base (IsLocalRing.closedPoint (T.presheaf.stalk η)) = η :=
      Scheme.fromSpecStalk_closedPoint
    have h3 : (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (T.presheaf.stalk η)) =
        IsLocalRing.closedPoint (T.presheaf.stalk η) :=
      (T.fromSpecStalk η).isEmbedding.injective (h.trans h2.symm)
    exact IsDiscreteValuationRing.not_a_field (T.presheaf.stalk η)
      (congrArg PrimeSpectrum.asIdeal h3).symm
  have hξt : t.base ξ ≠ IsLocalRing.closedPoint R := fun h => hξne (hgenη ξ hξη h)
  have hcomp : ∀ Z ∈ irreducibleComponents T, η ∈ Z → Z = closure {ξ} := by
    intro Z hZ hηZ
    have hZirr : IsIrreducible Z := hZ.1
    have hZcl : IsClosed Z := isClosed_of_mem_irreducibleComponents Z hZ
    have hz : IsGenericPoint hZirr.genericPoint Z := hZirr.isGenericPoint_genericPoint hZcl
    have hzmem : hZirr.genericPoint ∈ Set.range (T.fromSpecStalk η).base := by
      rw [Scheme.range_fromSpecStalk]; exact hz.specializes hηZ
    obtain ⟨q, hq⟩ := hzmem
    have hξz : ξ ⤳ hZirr.genericPoint := by
      rw [← hq]
      refine Specializes.map ?_ (T.fromSpecStalk η).base.hom.continuous
      exact (PrimeSpectrum.le_iff_specializes _ q).mp
        (show (⊥ : Ideal (T.presheaf.stalk η)) ≤ q.asIdeal from bot_le)
    have h1 : Z ⊆ closure {ξ} := by
      rw [← hz.def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hξz))
        isClosed_closure
    exact h1.antisymm (hZ.2 isIrreducible_singleton.closure h1)
  have hZ₀ : irreducibleComponent η ∈ irreducibleComponents T :=
    irreducibleComponent_mem_irreducibleComponents η
  have hZ₀eq : irreducibleComponent η = closure {ξ} := hcomp _ hZ₀ mem_irreducibleComponent
  let U₀ : T.Opens := T.irreducibleComponentOpen (irreducibleComponent η)
  have hηU₀ : η ∈ U₀ := by
    show η ∈ (⋃₀ (irreducibleComponents T \ {irreducibleComponent η}))ᶜ
    rintro ⟨Z, ⟨hZ, hZne⟩, hηZ⟩
    exact hZne ((hcomp Z hZ hηZ).trans hZ₀eq.symm)
  have hξU₀ : ξ ∈ U₀ := hξη.mem_open U₀.2 hηU₀
  have hU₀Z₀ : (U₀ : Set T) ⊆ irreducibleComponent η := by
    rw [← closure_sUnion_irreducibleComponents_sdiff_singleton
      TopologicalSpace.NoetherianSpace.finite_irreducibleComponents (irreducibleComponent η) hZ₀]
    exact subset_closure
  have hU₀irr : IsIrreducible (U₀ : Set T) :=
    ⟨⟨η, hηU₀⟩, hZ₀.1.2.open_subset U₀.2 hU₀Z₀⟩
  have : IrreducibleSpace U₀.toScheme := Subtype.irreducibleSpace hU₀irr
  have : IsIntegral U₀.toScheme :=
    (isIntegral_iff_irreducibleSpace_and_isReduced _).mpr ⟨‹_›, inferInstance⟩
  have : W.IsSeparated := ⟨by rw [← terminal.comp_from w]; infer_instance⟩
  have hY : ValuativeCriterion.Existence f := by
    have h : UniversallyClosed f := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  have hmemUgen : ∀ x : T, t.base x ≠ IsLocalRing.closedPoint R → x ∈ Ugen :=
    mem_opensRange_pullbackFst_of_ne_closedPoint t
  let D : U₀.toScheme.Opens := U₀.ι ⁻¹ᵁ Ugen
  have hξD : (⟨ξ, hξU₀⟩ : U₀.toScheme) ∈ D := by
    show U₀.ι.base ⟨ξ, hξU₀⟩ ∈ Ugen
    exact hmemUgen ξ hξt
  have hDdense : Dense (D : Set U₀.toScheme) := D.2.dense ⟨⟨ξ, hξU₀⟩, hξD⟩
  have hDrange : Set.range (D.ι ≫ U₀.ι).base ⊆
      Set.range (pullback.fst t (specGenericFibreInclusion R K)).base := by
    rintro _ ⟨z, rfl⟩
    rw [← Scheme.Hom.coe_opensRange]
    exact z.2
  let lD := IsOpenImmersion.lift (pullback.fst t (specGenericFibreInclusion R K)) (D.ι ≫ U₀.ι)
    hDrange
  let f₀ : U₀.toScheme.PartialMap W :=
    { domain := D
      dense_domain := hDdense
      hom := lD ≫ uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K) }
  have hf₀' : f₀.hom ≫ w = (lD ≫ pullback.snd t (specGenericFibreInclusion R K)) ≫
      specGenericFibreInclusion R K := by
    show (lD ≫ uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K)) ≫ w = _
    simp only [Category.assoc]
    rw [pullback.condition, reassoc_of% uK.2]
  have hf₀ : f₀.hom ≫ w = f₀.domain.ι ≫ (U₀.ι ≫ t) := by
    rw [hf₀', Category.assoc, ← pullback.condition, ← Category.assoc,
      IsOpenImmersion.lift_fac, Category.assoc]
  let η' : U₀.toScheme := ⟨η, hηU₀⟩
  have hιη : U₀.ι.base η' = η := rfl
  have hsmU : Smooth (U₀.ι ≫ t) := MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance
  have hη's : (U₀.ι ≫ t).base η' = IsLocalRing.closedPoint R := by
    show t.base (U₀.ι.base η') = _
    rw [hιη, hηs]
  have hgen' : ∀ y : U₀.toScheme, y ⤳ η' →
      (U₀.ι ≫ t).base y = IsLocalRing.closedPoint R → y = η' := by
    intro y hy hys
    apply U₀.ι.isOpenEmbedding.injective
    rw [hιη]
    apply hgenη
    · rw [← hιη]; exact hy.map U₀.ι.base.hom.continuous
    · exact hys
  obtain ⟨hd', hdvr'⟩ := @AlgebraicGeometry.Smooth.isDiscreteValuationRing_stalk_of_forall_specializes
    R _ _ _ _ (U₀.ι ≫ t) hsmU η' hη's hgen'
  let O := U₀.toScheme.presheaf.stalk η'
  -- The valuative criterion for the proper morphism `f`.
  have hcomm : (f₀.fromFunctionField ≫ h) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap O U₀.toScheme.functionField)) ≫
        (U₀.toScheme.fromSpecStalk η' ≫ U₀.ι ≫ t) := by
    rw [ofHom_algebraMap_stalk_functionField, Category.assoc, hw]
    change (f₀.domain.fromSpecStalkOfMem (genericPoint U₀.toScheme) _ ≫ f₀.hom) ≫ w = _
    rw [Category.assoc, hf₀, ← Category.assoc, Scheme.Opens.fromSpecStalkOfMem_ι,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk_assoc]
  obtain ⟨l₀, hl₀₁, hl₀₂⟩ := (hY
    { R := O
      commRing := inferInstance
      domain := (inferInstance : IsDomain O)
      valuationRing := inferInstance
      K := U₀.toScheme.functionField
      field := inferInstance
      algebra := (inferInstance : Algebra O U₀.toScheme.functionField)
      isFractionRing := (inferInstance : IsFractionRing O U₀.toScheme.functionField)
      i₁ := f₀.fromFunctionField ≫ h
      i₂ := U₀.toScheme.fromSpecStalk η' ≫ U₀.ι ≫ t
      commSq := ⟨hcomm⟩ }).exists_lift
  have hl₀₂' : l₀ ≫ f = U₀.toScheme.fromSpecStalk η' ≫ U₀.ι ≫ t := hl₀₂
  have hl₀₁' : Spec.map (U₀.toScheme.presheaf.stalkSpecializes
      ((genericPoint_spec U₀.toScheme).specializes trivial)) ≫ l₀ = f₀.fromFunctionField ≫ h := by
    rw [← ofHom_algebraMap_stalk_functionField]
    exact hl₀₁
  -- Lift through `h` using ramification index one.
  let φ := SmoothDvrStalk.stalkStructureMap R (U₀.ι ≫ t) η'
  let : Algebra R O := φ.hom.toAlgebra
  obtain ⟨hlh, hram⟩ := SmoothDvrStalk.stalk_isRamificationIndexOne R (U₀.ι ≫ t) η' hη's hgen' rfl
  have hφ : U₀.toScheme.fromSpecStalk η' ≫ U₀.ι ≫ t =
      Spec.map (CommRingCat.ofHom (algebraMap R O)) :=
    SmoothDvrStalk.fromSpecStalk_comp R (U₀.ι ≫ t) η'
  obtain ⟨l, hl⟩ := hlift O hram l₀ (hl₀₂'.trans hφ)
  have hl₂ : l ≫ w = U₀.toScheme.fromSpecStalk η' ≫ U₀.ι ≫ t := by
    rw [← hw, ← Category.assoc, hl, hl₀₂']
  have hl₁ : Spec.map (U₀.toScheme.presheaf.stalkSpecializes
      ((genericPoint_spec U₀.toScheme).specializes trivial)) ≫ l = f₀.fromFunctionField := by
    have hαβ : (Spec.map (U₀.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec U₀.toScheme).specializes trivial)) ≫ l) ≫ h =
        f₀.fromFunctionField ≫ h := by
      rw [Category.assoc, hl, hl₀₁']
    have hww : (Spec.map (U₀.toScheme.presheaf.stalkSpecializes
        ((genericPoint_spec U₀.toScheme).specializes trivial)) ≫ l) ≫ w =
        f₀.fromFunctionField ≫ w := by
      rw [← hw]
      simp only [← Category.assoc] at hαβ ⊢
      rw [hαβ]
    refine eq_of_comp_eq hw hgen _ _ hαβ hww ?_
    rw [hww]
    change Set.range ((f₀.domain.fromSpecStalkOfMem (genericPoint U₀.toScheme) _ ≫ f₀.hom) ≫
      w).base ⊆ _
    rw [Category.assoc, hf₀', ← Category.assoc, Scheme.Hom.comp_base, TopCat.coe_comp]
    exact Set.range_comp_subset_range _ _
  have hmem : η' ∈ f₀.toRationalMap.domain :=
    mem_domain_toRationalMap_of_lift (U₀.ι ≫ t) w f₀ η' l hl₂ hl₁
  let g₀ : U₀.toScheme.PartialMap W := f₀.toRationalMap.toPartialMap
  have hle : D ≤ g₀.domain := f₀.le_domain_toRationalMap
  have hres : U₀.toScheme.homOfLE hle ≫ g₀.hom = f₀.hom := by
    have h := f₀.toPartialMap_toRationalMap_restrict
    rw [Scheme.PartialMap.restrict_hom] at h
    exact h
  have : IsDominant (U₀.toScheme.homOfLE hle) :=
    AlgebraicGeometry.Opens.isDominant_homOfLE hDdense hle
  have hg₀ : g₀.hom ≫ w = g₀.domain.ι ≫ U₀.ι ≫ t := by
    apply ext_of_isDominant (U₀.toScheme.homOfLE hle)
    rw [reassoc_of% hres, hf₀, Scheme.homOfLE_ι_assoc]
  let U : T.Opens := U₀.ι ''ᵁ g₀.domain
  have hηU : η ∈ U := ⟨η', hmem, rfl⟩
  have hgU : ((U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom) ≫ w = U.ι ≫ t := by
    rw [Category.assoc, hg₀, Scheme.Hom.isoImage_inv_ι_assoc]
  refine ⟨U, hηU, ⟨(U₀.ι.isoImage g₀.domain).inv ≫ g₀.hom, hgU⟩, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
    have hθrange : Set.range (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι).base ⊆
        Set.range (D.ι ≫ U₀.ι).base := by
      rintro _ ⟨z, rfl⟩
      have hz : (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈
          (pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).opensRange := ⟨z, rfl⟩
      rw [Scheme.Hom.opensRange_pullbackFst] at hz
      obtain ⟨x, hx, hxe⟩ := ((pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K)).base z).2
      have hxD : x ∈ D := by
        change U₀.ι.base x ∈ (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact (congrArg (fun y : T => y ∈ t ⁻¹ᵁ (specGenericFibreInclusion R K).opensRange)
          hxe).mpr hz
      exact ⟨⟨x, hxD⟩, hxe⟩
    obtain ⟨θ, hθ⟩ : ∃ θ : pullback (U.ι ≫ t) (specGenericFibreInclusion R K) ⟶ D.toScheme,
        θ ≫ D.ι ≫ U₀.ι = pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫ U.ι :=
      ⟨IsOpenImmersion.lift (D.ι ≫ U₀.ι) _ hθrange, IsOpenImmersion.lift_fac _ _ _⟩
    have hA : pullback.fst (U.ι ≫ t) (specGenericFibreInclusion R K) ≫
        (U₀.ι.isoImage g₀.domain).inv = θ ≫ U₀.toScheme.homOfLE hle := by
      rw [← cancel_mono (g₀.domain.ι ≫ U₀.ι), Category.assoc, Scheme.Hom.isoImage_inv_ι,
        Category.assoc, Scheme.homOfLE_ι_assoc, hθ]
    rw [reassoc_of% hA, hres]
    show θ ≫ (lD ≫ uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K)) =
      pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t (specGenericFibreInclusion R K)
          U.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K)
    rw [← Category.assoc θ]
    congr 1
    rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K)), Category.assoc,
      IsOpenImmersion.lift_fac, hθ]
    simp only [pullback.map, pullback.lift_fst]
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
    rw [uK.2, pullback.lift_snd, Category.comp_id]

/-- Local extension at a generic point of the closed fibre of a smooth test scheme. -/
theorem exists_nhds_extension [IsProper f] [LocallyOfFiniteType w] [IsSeparated w]
    (hw : h ≫ f = w)
    (hgen : IsIso (pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp])))
    (hlift : RamificationIndexOneLifting R f h)
    {T : Scheme.{u}} (t : T ⟶ Spec (CommRingCat.of R)) [Smooth t]
    (uK : SchemeHomOver (pullback.snd t (specGenericFibreInclusion R K))
      (pullback.snd w (specGenericFibreInclusion R K)))
    (η : T) (hηs : t.base η = IsLocalRing.closedPoint R)
    (hgenη : ∀ y : T, y ⤳ η → t.base y = IsLocalRing.closedPoint R → y = η) :
    ∃ (U : T.Opens) (_ : η ∈ U) (g : SchemeHomOver (U.ι ≫ t) w),
      (genericFibreRestrict R K w (U.ι ≫ t) g).1 =
        pullback.map (U.ι ≫ t) (specGenericFibreInclusion R K) t
          (specGenericFibreInclusion R K) U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 := by
  obtain ⟨_, ⟨T₀ : T.Opens, hT₀, rfl⟩, hηT₀, -⟩ :=
    T.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ η) isOpen_univ
  have : IsAffine T₀.toScheme := hT₀
  let ι := specGenericFibreInclusion R K
  let t₀ := T₀.ι ≫ t
  have : Smooth t₀ := MorphismProperty.comp_mem @Smooth _ _ inferInstance inferInstance
  have : QuasiCompact t₀ := inferInstance
  let m₀ := pullback.map t₀ ι t ι T₀.ι (𝟙 _) (𝟙 _) (by simp [t₀]) (by simp)
  let uK₀ : SchemeHomOver (pullback.snd t₀ ι) (pullback.snd w ι) :=
    ⟨m₀ ≫ uK.1, by
      rw [Category.assoc, uK.2]
      exact (pullback.lift_snd _ _ _).trans (Category.comp_id _)⟩
  let η₀ : T₀.toScheme := ⟨η, hηT₀⟩
  have hgen₀ : ∀ y : T₀.toScheme, y ⤳ η₀ → t₀.base y = IsLocalRing.closedPoint R → y = η₀ := by
    intro y hy hys
    apply T₀.ι.isOpenEmbedding.injective
    exact hgenη _ (hy.map T₀.ι.base.hom.continuous) hys
  obtain ⟨U, hηU, g, hg⟩ :=
    exists_nhds_extension_of_quasiCompact hw hgen hlift t₀ uK₀ η₀ hηs hgen₀
  let U' : T.Opens := T₀.ι ''ᵁ U
  have hgw : ((T₀.ι.isoImage U).inv ≫ g.1) ≫ w = U'.ι ≫ t := by
    rw [Category.assoc, g.2, Scheme.Hom.isoImage_inv_ι_assoc]
  refine ⟨U', ⟨η₀, hηU, rfl⟩, ⟨(T₀.ι.isoImage U).inv ≫ g.1, hgw⟩, ?_⟩
  apply pullback.hom_ext
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
    let m := pullback.map (U'.ι ≫ t) ι (U.ι ≫ t₀) ι (T₀.ι.isoImage U).inv (𝟙 _) (𝟙 _)
      (by simp [t₀, U']) (by simp)
    have hm : pullback.fst (U'.ι ≫ t) ι ≫ (T₀.ι.isoImage U).inv =
        m ≫ pullback.fst (U.ι ≫ t₀) ι := by
      simp [m, pullback.map]
    have key : m ≫ pullback.map (U.ι ≫ t₀) ι t₀ ι U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ m₀ =
        pullback.map (U'.ι ≫ t) ι t ι U'.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) := by
      apply pullback.hom_ext
      · simp only [m, m₀, Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
        rw [Scheme.Hom.isoImage_inv_ι]
      · simp [m, m₀, pullback.map]
    rw [reassoc_of% hm, ← genericFibreRestrict_coe_comp_fst (R := R) (K := K) w (U.ι ≫ t₀) g, hg]
    change m ≫ (pullback.map (U.ι ≫ t₀) ι t₀ ι U.ι (𝟙 _) (𝟙 _)
          (Category.comp_id _) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
        m₀ ≫ uK.1) ≫ pullback.fst w ι = _
    rw [← key]
    simp only [Category.assoc]
    rfl
  · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
    rw [uK.2, pullback.lift_snd, Category.comp_id]

/-- A separated scheme `W` of finite type over a discrete valuation ring has the weak Néron
mapping property as soon as it maps to a proper scheme `X` by a morphism which is an
isomorphism on generic fibres and through which every point of `X` with values in a
discrete valuation ring of ramification index one lifts. -/
theorem weakNeronMappingProperty_of_lifting [IsProper f] [LocallyOfFiniteType w]
    [IsSeparated w] (hw : h ≫ f = w)
    (hgen : IsIso (pullback.map w (specGenericFibreInclusion R K) f
      (specGenericFibreInclusion R K) h (𝟙 _) (𝟙 _) (by rw [Category.comp_id, hw])
      (by rw [Category.comp_id, Category.id_comp])))
    (hlift : RamificationIndexOneLifting R f h) :
    WeakNeronMappingProperty R K w := by
  classical
  intro T t ht uK
  have hoi : IsOpenImmersion (specGenericFibreInclusion R K) :=
    isOpenImmersion_spec_fractionRing_of_dvr R K
  let Ts := {x : T // t.base x = IsLocalRing.closedPoint R}
  have hS : IsClosed {y : T | t.base y = IsLocalRing.closedPoint R} :=
    ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (IsLocalRing.maximalIdeal.isMaximal R)).preimage t.base.hom.continuous
  have : QuasiSober Ts := hS.isClosedEmbedding_subtypeVal.quasiSober
  let ι := Option (irreducibleComponents Ts)
  have hZirr : ∀ Z : irreducibleComponents Ts, IsIrreducible (Z.1 : Set Ts) := fun Z => Z.2.1
  have hZcl : ∀ Z : irreducibleComponents Ts, IsClosed (Z.1 : Set Ts) := fun Z =>
    isClosed_of_mem_irreducibleComponents _ Z.2
  let ηZ : irreducibleComponents Ts → Ts := fun Z => (hZirr Z).genericPoint
  have hηZ : ∀ Z, IsGenericPoint (ηZ Z) (Z.1 : Set Ts) := fun Z =>
    (hZirr Z).isGenericPoint_genericPoint (hZcl Z)
  have hgenZ : ∀ Z : irreducibleComponents Ts, ∀ y : T, y ⤳ (ηZ Z).1 →
      t.base y = IsLocalRing.closedPoint R → y = (ηZ Z).1 := by
    intro Z y hy hys
    let y' : Ts := ⟨y, hys⟩
    have hy' : y' ⤳ ηZ Z := Topology.IsInducing.subtypeVal.specializes_iff.mp hy
    have h1 : (Z.1 : Set Ts) ⊆ closure {y'} := by
      rw [← (hηZ Z).def]
      exact closure_minimal (Set.singleton_subset_iff.mpr (specializes_iff_mem_closure.mp hy'))
        isClosed_closure
    have h2 : closure {y'} ⊆ (Z.1 : Set Ts) := Z.2.2 isIrreducible_singleton.closure h1
    have h3 : IsGenericPoint y' (Z.1 : Set Ts) := isGenericPoint_def.mpr (h2.antisymm h1)
    exact congrArg Subtype.val (h3.eq (hηZ Z))
  choose U_ hηU g_ hg_ using fun Z : irreducibleComponents Ts =>
    exists_nhds_extension hw hgen hlift t uK (ηZ Z).1 (ηZ Z).2 (hgenZ Z)
  let Ugen : T.Opens := (pullback.fst t (specGenericFibreInclusion R K)).opensRange
  let ggen : SchemeHomOver (Ugen.ι ≫ t) w :=
    ⟨(Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫ uK.1 ≫
        pullback.fst w (specGenericFibreInclusion R K), by
      simp only [Category.assoc]
      rw [pullback.condition, reassoc_of% uK.2, ← pullback.condition,
        Scheme.Hom.isoOpensRange_inv_comp_assoc]⟩
  let U : ι → T.Opens := fun i => i.elim Ugen U_
  let g : ∀ i : ι, SchemeHomOver ((U i).ι ≫ t) w := fun i =>
    match i with
    | none => ggen
    | some Z => g_ Z
  let V : T.Opens := ⨆ i, U i
  have hgU : ∀ i, pullback.fst ((U i).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g i).1 =
      pullback.map ((U i).ι ≫ t) (specGenericFibreInclusion R K) t
        (specGenericFibreInclusion R K) (U i).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
        ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫
        pullback.fst w (specGenericFibreInclusion R K) := by
    intro i
    cases i with
    | none =>
      have hnone : pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫
          (Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv =
          pullback.map (Ugen.ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) Ugen.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K))]
        simp only [Category.assoc, pullback.map, pullback.lift_fst]
        rw [Scheme.Hom.isoOpensRange_inv_comp]
      show pullback.fst (Ugen.ι ≫ t) (specGenericFibreInclusion R K) ≫
          ((Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫
            uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K)) = _
      rw [reassoc_of% hnone]
      rfl
    | some Z =>
      show pullback.fst ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) ≫ (g_ Z).1 =
        pullback.map ((U_ Z).ι ≫ t) (specGenericFibreInclusion R K) t
          (specGenericFibreInclusion R K) (U_ Z).ι (𝟙 _) (𝟙 _) (Category.comp_id _)
          ((Category.comp_id _).trans (Category.id_comp _).symm) ≫ uK.1 ≫
          pullback.fst w (specGenericFibreInclusion R K)
      rw [← genericFibreRestrict_coe_comp_fst (R := R) (K := K) w ((U_ Z).ι ≫ t) (g_ Z), hg_ Z,
        Category.assoc]
  let 𝒰 := Scheme.Opens.iSupOpenCover U
  have hUι : ∀ k, 𝒰.f k ≫ (⨆ i, U i).ι = (U k).ι := fun k => Scheme.homOfLE_ι T (le_iSup U k)
  have hcompat : ∀ i j : ι, pullback.fst (𝒰.f i) (𝒰.f j) ≫ (g i).1 =
      pullback.snd (𝒰.f i) (𝒰.f j) ≫ (g j).1 := by
    intro i j
    let p : pullback (𝒰.f i) (𝒰.f j) ⟶ Spec (CommRingCat.of R) :=
      pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι ≫ t
    have h12 : pullback.fst (𝒰.f i) (𝒰.f j) ≫ (U i).ι =
        pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι := by
      rw [← hUι i, ← hUι j, pullback.condition_assoc]
    have hp₂ : pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι ≫ t = p := by
      rw [← reassoc_of% h12]
    have hsm1 : Smooth (pullback.fst (𝒰.f i) (𝒰.f j)) := inferInstance
    have hsm0 : Smooth (U i).ι := inferInstance
    have hsm2 : Smooth ((U i).ι ≫ t) := MorphismProperty.comp_mem @Smooth _ _ hsm0 ht
    have : Smooth p := MorphismProperty.comp_mem @Smooth _ _ hsm1 hsm2
    have : Flat p := inferInstance
    let a : SchemeHomOver p w := ⟨pullback.fst _ _ ≫ (g i).1, by
      rw [Category.assoc]; exact congrArg (fun h => pullback.fst (𝒰.f i) (𝒰.f j) ≫ h) (g i).2⟩
    let b : SchemeHomOver p w := ⟨pullback.snd _ _ ≫ (g j).1, by
      rw [Category.assoc]
      exact (congrArg (fun h => pullback.snd (𝒰.f i) (𝒰.f j) ≫ h) (g j).2).trans hp₂⟩
    suffices hab : a = b from congrArg Subtype.val hab
    apply NeronModelInfra.genericFibreRestrict_injective_of_flat_of_isSeparated R K w p
    apply Subtype.ext
    apply pullback.hom_ext
    · simp only [genericFibreRestrict_coe_comp_fst]
      have key : ∀ (k : ι) (q : pullback (𝒰.f i) (𝒰.f j) ⟶ (U k).toScheme)
          (hq : q ≫ (U k).ι ≫ t = p),
          pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (g k).1 =
            pullback.lift (pullback.fst p (specGenericFibreInclusion R K) ≫ q ≫ (U k).ι)
              (pullback.snd p (specGenericFibreInclusion R K))
              (by rw [Category.assoc, Category.assoc, hq, pullback.condition]) ≫ uK.1 ≫
              pullback.fst w (specGenericFibreInclusion R K) := by
        intro k q hq
        have hm : pullback.fst p (specGenericFibreInclusion R K) ≫ q =
            pullback.map p (specGenericFibreInclusion R K) ((U k).ι ≫ t)
              (specGenericFibreInclusion R K) q (𝟙 _) (𝟙 _)
              (by rw [Category.comp_id, hq]) ((Category.comp_id _).trans (Category.id_comp _).symm) ≫
              pullback.fst ((U k).ι ≫ t) (specGenericFibreInclusion R K) := by
          simp only [pullback.map, pullback.lift_fst]
        rw [← Category.assoc (pullback.fst p (specGenericFibreInclusion R K)), hm, Category.assoc,
          hgU k]
        simp only [← Category.assoc]
        congr 2
        apply pullback.hom_ext
        · simp only [Category.assoc, pullback.map, pullback.lift_fst, pullback.lift_fst_assoc]
        · simp only [Category.assoc, pullback.map, pullback.lift_snd, Category.comp_id]
      change pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫
          (g i).1 =
        pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.snd (𝒰.f i) (𝒰.f j) ≫ (g j).1
      refine (key i (pullback.fst _ _) rfl).trans ?_
      refine Eq.trans ?_ (key j (pullback.snd _ _) hp₂).symm
      have h12' : pullback.fst p (specGenericFibreInclusion R K) ≫ pullback.fst (𝒰.f i) (𝒰.f j) ≫
          (U i).ι = pullback.fst p (specGenericFibreInclusion R K) ≫
            pullback.snd (𝒰.f i) (𝒰.f j) ≫ (U j).ι := by rw [h12]
      congr 2
    · simp only [genericFibreRestrict_coe_comp_snd]
  let v : V.toScheme ⟶ W := 𝒰.glueMorphisms (fun i => (g i).1) hcompat
  have hv : ∀ i, 𝒰.f i ≫ v = (g i).1 := fun i => 𝒰.ι_glueMorphisms _ _ i
  have hvw : v ≫ w = V.ι ≫ t := by
    apply 𝒰.hom_ext
    intro i
    rw [reassoc_of% (hv i)]
    refine ((g i).2).trans ?_
    change (U i).ι ≫ t = T.homOfLE (le_iSup U i) ≫ (⨆ i, U i).ι ≫ t
    rw [Scheme.homOfLE_ι_assoc]
  refine ⟨V, ⟨v, hvw⟩, ?_, ?_, ?_⟩
  · intro x hx
    have : x ∈ U none := mem_opensRange_pullbackFst_of_ne_closedPoint t x hx
    exact TopologicalSpace.Opens.mem_iSup.mpr ⟨none, this⟩
  · intro Z hZ
    exact ⟨ηZ ⟨Z, hZ⟩, (hηZ ⟨Z, hZ⟩).mem,
      TopologicalSpace.Opens.mem_iSup.mpr ⟨some ⟨Z, hZ⟩, hηU ⟨Z, hZ⟩⟩⟩
  · apply pullback.hom_ext
    · simp only [Category.assoc, genericFibreRestrict_coe_comp_fst]
      have hrange : Set.range (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base ⊆
          Set.range (𝒰.f none).base := by
        rintro _ ⟨z, rfl⟩
        have hz : (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z ∈
            Set.range (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base :=
          ⟨z, rfl⟩
        rw [IsOpenImmersion.range_pullbackFst] at hz
        have h1 : Set.range (𝒰.f none).base = ((V.ι ⁻¹ᵁ (U none) : V.toScheme.Opens) : Set V) := by
          change Set.range (T.homOfLE (le_iSup U none)).base = _
          rw [← Scheme.Hom.coe_opensRange, Scheme.opensRange_homOfLE]
        rw [h1]
        change V.ι.base ((pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)).base z) ∈
          (pullback.fst t (specGenericFibreInclusion R K)).opensRange
        rw [Scheme.Hom.opensRange_pullbackFst]
        exact hz
      let l := IsOpenImmersion.lift (𝒰.f none)
        (pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K)) hrange
      have hl : l ≫ 𝒰.f none = pullback.fst (V.ι ≫ t) (specGenericFibreInclusion R K) :=
        IsOpenImmersion.lift_fac _ _ _
      have hkey : l ≫ (Scheme.Hom.isoOpensRange
          (pullback.fst t (specGenericFibreInclusion R K))).inv =
          pullback.map (V.ι ≫ t) (specGenericFibreInclusion R K) t
            (specGenericFibreInclusion R K) V.ι (𝟙 _) (𝟙 _) (Category.comp_id _)
            ((Category.comp_id _).trans (Category.id_comp _).symm) := by
        rw [← cancel_mono (pullback.fst t (specGenericFibreInclusion R K))]
        simp only [Category.assoc, pullback.map, pullback.lift_fst]
        rw [← hl, Category.assoc]
        congr 1
        simp only [𝒰, Scheme.Opens.iSupOpenCover, V, Scheme.homOfLE_ι]
        exact Scheme.Hom.isoOpensRange_inv_comp _
      rw [← hl, Category.assoc, hv none]
      change l ≫ ((Scheme.Hom.isoOpensRange (pullback.fst t (specGenericFibreInclusion R K))).inv ≫
        uK.1 ≫ pullback.fst w (specGenericFibreInclusion R K)) = _
      rw [reassoc_of% hkey]
    · simp only [Category.assoc, genericFibreRestrict_coe_comp_snd, pullback.map]
      rw [uK.2, pullback.lift_snd, Category.comp_id]

end Langlands.AbelianScheme.WeakNeronLifting

import Langlands.Geometry.Building.AffineRootSystemPullback
import Langlands.Geometry.Building.ActualAffineRootLocalFiniteness
import Langlands.Geometry.Building.ReflectionNormalizerWeylAction
import Langlands.Geometry.Building.NormalizerImageAffineWeylBounds
import Langlands.Geometry.Building.ValuationBuildingAxioms
import Langlands.Representation.Plancherel.RationalValuationDetection

/-! # The affine root systems of valuation building data without V 7

For every `B : ValuationBuildingData G` over a nonarchimedean local field, this module proves,
assuming neither V 7 nor AS 5:

* AS 2: `Ψ′ = B.apartment.extendedAffineRoots` is an affine root system with derivative `Φ`;
* AS 3 except the inclusion `Φ ⊆ ∇Ψ`: `Ψ = B.affineRoots` is an affine root system with
  `∇Ψ ⊆ Φ`;
* AS 4 and the first sentence of AS 5, from published results.

The inclusion `Φ ⊆ ∇Ψ` of AS 3, V 7 and the last two sentences of AS 5 are not proved here.
-/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj
open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace

namespace Langlands.Geometry.Building

namespace AffineRootSystem

variable {V A : Type*} [AddCommGroup V] [Module ℝ V] [AddTorsor V A]

/-- A derivative fibre of `Ψ` that is closed under a nonzero constant shift is infinite. -/
theorem infinite_fiber_of_add_const_mem {Ψ : Set (A →ᵃ[ℝ] ℝ)} {ψ : A →ᵃ[ℝ] ℝ} (hψ : ψ ∈ Ψ)
    {c : ℝ} (hc : c ≠ 0)
    (h : ∀ θ ∈ Ψ, θ.linear = ψ.linear → θ + AffineMap.const ℝ A c ∈ Ψ) :
    {θ | θ ∈ Ψ ∧ θ.linear = ψ.linear}.Infinite := by
  let f : ℕ → (A →ᵃ[ℝ] ℝ) := fun n => ψ + AffineMap.const ℝ A ((n : ℝ) * c)
  have hlin : ∀ n, (f n).linear = ψ.linear := fun n => by
    simp [f]
  have hmem : ∀ n, f n ∈ Ψ := by
    intro n
    induction n with
    | zero =>
      have : f 0 = ψ := by
        ext x
        simp [f]
      rw [this]
      exact hψ
    | succ n ih =>
      have hs := h (f n) ih (hlin n)
      have : f (n + 1) = f n + AffineMap.const ℝ A c := by
        ext x
        simp only [f, AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply,
          Function.const_apply, Nat.cast_succ]
        ring
      rw [this]
      exact hs
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ fun n => ⟨hmem n, hlin n⟩
  intro m n hmn
  obtain ⟨x⟩ : Nonempty A := inferInstance
  have hx := congrArg (fun g : A →ᵃ[ℝ] ℝ => g x) hmn
  simp only [f, AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply,
    Function.const_apply, add_right_inj] at hx
  exact_mod_cast mul_right_cancel₀ hc hx

end AffineRootSystem

namespace KPApartmentData

variable {k : Type u} [Field k]
    {S : CommGroupScheme (Spec (CommRingCat.of k))}
    {G : GroupScheme (Spec (CommRingCat.of k))}
    {i : S.toGrp ⟶ G} [Mono i.hom.hom.left] [IsAffineHom G.X.hom]
    {ω : kˣ → ℝ} (D : KPApartmentData i ω)

/-- Actual normalizer conjugation takes each extended affine root to an extended affine root
(KP Lemma 6.3.12 for `Ψ′`). -/
theorem conjugateAffineFunctional_mem_extendedAffineRoots (n : normalizerPoints i)
    {ψ : D.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ D.extendedAffineRoots) :
    D.conjugateAffineFunctional n ψ ∈ D.extendedAffineRoots := by
  obtain ⟨a, ha, hne⟩ := hψ
  refine ⟨⟨weylAction i n a, weylAction_mapsTo_relativeRoots i n a.property⟩,
    D.conjugateAffineFunctional_linear_eq_rootForm n ha, fun heq => hne ?_⟩
  change D.affineRootGroupPlus (weylAction i n a) (D.conjugateAffineFunctional n ψ) =
    D.affineRootGroup (weylAction i n a) (D.conjugateAffineFunctional n ψ) at heq
  rw [← D.conj_affineRootGroupPlus, ← D.conj_affineRootGroup] at heq
  exact Subgroup.map_injective (MulAut.conj (n : rationalPoints G)).injective heq

/-- Extended affine-root membership is preserved and reflected by conjugation. -/
theorem conjugateAffineFunctional_mem_extendedAffineRoots_iff (n : normalizerPoints i)
    (ψ : D.Apartment →ᵃ[ℝ] ℝ) :
    D.conjugateAffineFunctional n ψ ∈ D.extendedAffineRoots ↔ ψ ∈ D.extendedAffineRoots := by
  constructor
  · intro hψ
    simpa only [D.conjugateAffineFunctional_inv] using
      D.conjugateAffineFunctional_mem_extendedAffineRoots n⁻¹ hψ
  · exact D.conjugateAffineFunctional_mem_extendedAffineRoots n

/-- The actual apartment action preserves the extended affine roots. -/
theorem normalizerAffineEquiv_mem_rootStabilizer_extendedAffineRoots (n : normalizerPoints i) :
    D.normalizerAffineEquiv n ∈ AffineRootSystem.rootStabilizer D.extendedAffineRoots := by
  intro ψ
  simpa only [conjugateAffineFunctional, inv_inv] using
    D.conjugateAffineFunctional_mem_extendedAffineRoots_iff n⁻¹ ψ

end KPApartmentData

namespace ValuationBuildingData

variable {F : Type u} [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G)

section Coroots

variable {a : relativeRoots B.i} {g : rationalPoints G}
    {p : rationalPoints G × rationalPoints G}

/-- The coroot of an actual opposite pair is a coroot of the extended affine roots. -/
theorem isCoroot_reflectionCoroot_extendedAffineRoots
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p) :
    AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots (B.reflectionFunctional a g)
      (B.reflectionCoroot hg hg1 hp) := by
  refine ⟨B.rootForm_reflectionCoroot hg hg1 hp, fun f hf => ?_⟩
  have hm := B.apartment.normalizerAffineEquiv_mem_rootStabilizer_extendedAffineRoots
    (B.reflectionElement hp)
  rw [B.normalizerAffineEquiv_reflectionElement hg hg1 hp] at hm
  have hf' := (hm f).2 hf
  exact (AffineRootSystem.comp_affineReflection (B.reflectionFunctional a g)
    (B.rootForm_reflectionCoroot hg hg1 hp) f) ▸ hf'

/-- Every actual root takes an integral value on the coroot of an actual opposite pair. -/
theorem rootForm_reflectionCoroot_integral
    (hg : g ∈ B.rootGroup a) (hg1 : g ≠ 1)
    (hp : RelativeRoot.IsOppositeFactorPair B.i (a : characterLattice B.S) g p)
    (b : relativeRoots B.i) :
    ∃ n : ℤ, rootForm B.i b (B.reflectionCoroot hg hg1 hp) = n :=
  ⟨latticePairing B.S b.val
      (hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1), by
    simp only [reflectionCoroot, rootForm_mk, eval_tmul, one_mul]⟩

end Coroots

/-- The derivative of `Ψ′` is `Φ` (AS 2): every actual root has a nonidentity point with a
finite value. -/
theorem derivativeRoots_extendedAffineRoots :
    AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots =
      Set.range (rootForm B.i) := by
  apply Set.Subset.antisymm
  · rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
    exact ⟨a, hlin.symm⟩
  · rintro _ ⟨a, rfl⟩
    let x : B.Apartment := Classical.arbitrary B.Apartment
    obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
    obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.mp hgtop
    exact ⟨_, B.apartment.affineFunctional_mem_extendedAffineRoots hg hr.symm, rfl⟩

theorem finite_derivativeRoots_extendedAffineRoots :
    (AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots).Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  rw [B.derivativeRoots_extendedAffineRoots]
  exact Set.finite_range _

theorem span_derivativeRoots_extendedAffineRoots :
    Submodule.span ℝ (AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots) = ⊤ :=
  top_unique <| (B.span_derivativeRoots_affineRoots_of_oppositePairs
    B.hasOppositeFactorPairs).symm.le.trans <| Submodule.span_mono <|
      Set.image_mono B.apartment.affineRoots_subset_extendedAffineRoots

/-- Coroots of `Ψ′`: those of the actual opposite pairs. -/
theorem exists_isCoroot_extendedAffineRoots {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    ∃ v : TranslationSpace B.i,
      AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots ψ v := by
  rw [← B.reflectionAffineRoots_eq] at hψ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  exact ⟨_, B.isCoroot_reflectionCoroot_extendedAffineRoots hg hg1 hp⟩

/-- AR 3 for `Ψ′`: every coroot of `Ψ′` is the integral coroot of an opposite pair. -/
theorem coroot_integral_extendedAffineRoots {ψ θ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) (hθ : θ ∈ B.apartment.extendedAffineRoots)
    {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.apartment.extendedAffineRoots θ v) :
    ∃ n : ℤ, ψ.linear v = n := by
  obtain ⟨b, hb, -⟩ := hψ
  rw [← B.reflectionAffineRoots_eq] at hθ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hθ
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  have hvv := AffineRootSystem.isCoroot_unique_of_finite_of_span
    B.finite_derivativeRoots_extendedAffineRoots B.span_derivativeRoots_extendedAffineRoots
    (B.isCoroot_reflectionCoroot_extendedAffineRoots hg hg1 hp) hv
  rw [hb, ← hvv]
  exact B.rootForm_reflectionCoroot_integral hg hg1 hp b

/-- AR 3 for `Ψ`: every coroot of `Ψ` is the integral coroot of an opposite pair. -/
theorem coroot_integral_affineRoots {ψ θ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.affineRoots) (hθ : θ ∈ B.affineRoots) {v : TranslationSpace B.i}
    (hv : AffineRootSystem.IsCoroot B.affineRoots θ v) :
    ∃ n : ℤ, ψ.linear v = n := by
  obtain ⟨b, hb, -⟩ := hψ
  have hθ' := B.apartment.affineRoots_subset_extendedAffineRoots hθ
  rw [← B.reflectionAffineRoots_eq] at hθ'
  obtain ⟨a, g, hg, hg1, rfl⟩ := hθ'
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  have hvv := B.reflectionCoroot_eq_of_isCoroot_of_locallyFinite
    (B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs B.hasOppositeFactorPairs)
    hg hg1 hp hv
  rw [hb, ← hvv]
  exact B.rootForm_reflectionCoroot_integral hg hg1 hp b

/-- The uniformizer point of an integral coroot of `a`, a point of `Z(F)`, has translation
`ν(z)` with `a(ν(z)) = -2`. -/
theorem exists_centralizer_eval_translation_eq_neg_two (a : relativeRoots B.i) :
    ∃ z : rationalPoints B.centralizer.Z, eval B.S a (B.translation z).toAdd = -2 := by
  let x : B.Apartment := Classical.arbitrary B.Apartment
  obtain ⟨g, hg, hgtop⟩ := x.isValuation.exists_ne_top a.property
  have hg1 : g ≠ 1 := by
    rintro rfl
    exact hgtop (B.val_apply_one a x)
  obtain ⟨p, hp⟩ := B.hasOppositeFactorPairs a a.property g hg hg1
  let ν := hp.coroot B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1
  have hν : latticePairing B.S a.val ν = 2 :=
    (hp.coroot_spec B.i B.isMaximalSplitTorus.isSplitSubtorus.1 a.property.1 hg hg1).1
  obtain ⟨χ, hχ⟩ := B.exists_character_rootCharacterDenominator a.val
  let z := Plancherel.RationalValuationDetection.splitTorusUniformizerPoint B.centralizer.s ν
  refine ⟨z, ?_⟩
  have hval := Plancherel.RationalValuationDetection.rationalCharacterValuation_splitTorusUniformizerPoint
    B.centralizer.s ν χ
  have hχ' : rationalCharacters.equivCharacterLattice B.S
      (characterRestrict B.centralizer.s χ) = B.rootCharacterDenominator a.val • a.val := hχ
  rw [hχ', map_nsmul, LinearMap.smul_apply, hν] at hval
  have he := eval_centralizerTranslation B.centralizer.s B.centralizer.bijective z χ
  rw [hχ, hval] at he
  have hd : (0 : ℝ) < B.rootCharacterDenominator a.val := by
    exact_mod_cast B.rootCharacterDenominator_pos a.val
  have he' : (B.rootCharacterDenominator a.val : ℝ) * eval B.S a.val (B.translation z).toAdd =
      (B.rootCharacterDenominator a.val : ℝ) * (-2) := by
    simp only [eval_eq_pair, TensorProduct.tmul_smul, map_nsmul, LinearMap.smul_apply,
      nsmul_eq_mul] at he ⊢
    refine he.trans ?_
    push_cast
    ring
  exact mul_left_cancel₀ hd.ne' he'

/-- A point of `Z(F)` shifts every affine functional with derivative `a` by `2`. -/
theorem exists_conjugateAffineFunctional_eq_add_two (a : relativeRoots B.i) :
    ∃ n : normalizerPoints B.i, ∀ ψ : B.Apartment →ᵃ[ℝ] ℝ, ψ.linear = rootForm B.i a →
      B.apartment.conjugateAffineFunctional n ψ = ψ + AffineMap.const ℝ B.Apartment 2 := by
  obtain ⟨z, hz⟩ := B.exists_centralizer_eval_translation_eq_neg_two a
  refine ⟨B.centralizer.toNormalizer z, fun ψ hψ => ?_⟩
  ext x
  rw [KPApartmentData.conjugateAffineFunctional_apply, ← map_inv,
    B.isOmegaCompatible.smul_eq_vadd]
  simp only [AffineMap.map_vadd, hψ, rootForm_mk, map_inv, toAdd_inv, map_neg, hz,
    AffineMap.coe_add, AffineMap.coe_const, Pi.add_apply, Function.const_apply, vadd_eq_add]
  ring

/-- AR 4, infinitude, for `Ψ′`. -/
theorem infinite_fiber_extendedAffineRoots {ψ : B.Apartment →ᵃ[ℝ] ℝ}
    (hψ : ψ ∈ B.apartment.extendedAffineRoots) :
    {θ | θ ∈ B.apartment.extendedAffineRoots ∧ θ.linear = ψ.linear}.Infinite := by
  obtain ⟨a, ha, -⟩ := id hψ
  obtain ⟨n, hn⟩ := B.exists_conjugateAffineFunctional_eq_add_two a
  refine AffineRootSystem.infinite_fiber_of_add_const_mem hψ two_ne_zero fun θ hθ hlin => ?_
  rw [← hn θ (hlin.trans ha)]
  exact B.apartment.conjugateAffineFunctional_mem_extendedAffineRoots n hθ

/-- AR 4, infinitude, for `Ψ`. -/
theorem infinite_fiber_affineRoots {ψ : B.Apartment →ᵃ[ℝ] ℝ} (hψ : ψ ∈ B.affineRoots) :
    {θ | θ ∈ B.affineRoots ∧ θ.linear = ψ.linear}.Infinite := by
  obtain ⟨a, ha, -⟩ := id hψ
  obtain ⟨n, hn⟩ := B.exists_conjugateAffineFunctional_eq_add_two a
  refine AffineRootSystem.infinite_fiber_of_add_const_mem hψ two_ne_zero fun θ hθ hlin => ?_
  rw [← hn θ (hlin.trans ha)]
  exact B.apartment.conjugateAffineFunctional_mem_affineRoots n hθ

/-- Bounded finiteness of `Ψ′` at a point (KP Proposition 6.3.7, from V 6). -/
theorem finite_bounded_extendedAffineRoots (x : B.Apartment) (C : ℝ) :
    {ψ | ψ ∈ B.apartment.extendedAffineRoots ∧ |ψ x| ≤ C}.Finite := by
  have : Smooth G.X.hom := B.isConnectedReductive.smooth
  let := B.isMaximalSplitTorus.isSplitSubtorus.1.finite_relativeRoots B.i |>.fintype
  refine (Set.finite_univ.biUnion fun a _ =>
    B.finite_bounded_reflectionFunctionals_of_oppositePairs B.hasOppositeFactorPairs a x C).subset
      ?_
  rintro ψ ⟨hψ, hbound⟩
  rw [← B.reflectionAffineRoots_eq] at hψ
  obtain ⟨a, g, hg, hg1, rfl⟩ := hψ
  exact Set.mem_biUnion (Set.mem_univ a) ⟨g, hg, hg1, rfl, hbound⟩

/-- AS 2: `Ψ′` is an affine root system. -/
theorem isAffineRootSystemWithRankZero_extendedAffineRoots :
    AffineRootSystem.IsAffineRootSystemWithRankZero B.apartment.extendedAffineRoots where
  span_derivativeRoots_eq_top := B.span_derivativeRoots_extendedAffineRoots
  linear_ne_zero := fun ψ hψ hzero => by
    obtain ⟨v, hv⟩ := B.exists_isCoroot_extendedAffineRoots hψ
    have h := hv.1
    rw [hzero, LinearMap.zero_apply] at h
    norm_num at h
  finite_derivativeRoots := B.finite_derivativeRoots_extendedAffineRoots
  exists_isCoroot := fun _ hψ => B.exists_isCoroot_extendedAffineRoots hψ
  coroot_integral := fun _ hψ _ hθ _ hv => B.coroot_integral_extendedAffineRoots hψ hθ hv
  infinite_fiber := fun _ hψ => B.infinite_fiber_extendedAffineRoots hψ
  finite_bounded := fun ψ _ M => by
    let x : B.Apartment := Classical.arbitrary B.Apartment
    refine (B.finite_bounded_extendedAffineRoots x (M + |ψ x|)).subset ?_
    rintro θ ⟨hθ, -, hM⟩
    refine ⟨hθ, ?_⟩
    calc |θ x| = |(θ x - ψ x) + ψ x| := by ring_nf
      _ ≤ |θ x - ψ x| + |ψ x| := abs_add_le _ _
      _ ≤ M + |ψ x| := add_le_add (hM x) le_rfl

/-- AS 3 without the derivative equality: `Ψ` is an affine root system. -/
theorem isAffineRootSystemWithRankZero_affineRoots :
    AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots := by
  have hΨ :=
    B.isLocallyFiniteReflectionArrangement_of_hasOppositeFactorPairs B.hasOppositeFactorPairs
  exact
    { span_derivativeRoots_eq_top := hΨ.span_derivativeRoots_eq_top
      linear_ne_zero := hΨ.linear_ne_zero
      finite_derivativeRoots := hΨ.finite_derivativeRoots
      exists_isCoroot := hΨ.exists_isCoroot
      coroot_integral := fun _ hψ _ hθ _ hv => B.coroot_integral_affineRoots hψ hθ hv
      infinite_fiber := fun _ hψ => B.infinite_fiber_affineRoots hψ
      finite_bounded := fun ψ _ M => by
        let x : B.Apartment := Classical.arbitrary B.Apartment
        refine (hΨ.finite_bounded_at x fun _ => M + |ψ x|).subset ?_
        rintro θ ⟨hθ, -, hM⟩
        refine ⟨hθ, ?_⟩
        calc |θ x| = |(θ x - ψ x) + ψ x| := by ring_nf
          _ ≤ |θ x - ψ x| + |ψ x| := abs_add_le _ _
          _ ≤ M + |ψ x| := add_le_add (hM x) le_rfl }

end ValuationBuildingData

/-- AS 2, AS 3 apart from the inclusion `Φ ⊆ ∇Ψ`, AS 4 and the first sentence of AS 5 hold for
every `B : ValuationBuildingData G` (KP Axiom 4.1.6 and Proposition 6.3.13, here without
V 7). -/
def ValuationBuildingAffineRootSystemsStatement : Prop :=
  ∀ (F : Type u) [Field F] [ValuativeRel F] [TopologicalSpace F]
    [IsNonarchimedeanLocalField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (B : ValuationBuildingData G),
    AffineRootSystem.IsAffineRootSystemWithRankZero B.apartment.extendedAffineRoots ∧
      AffineRootSystem.derivativeRoots B.apartment.extendedAffineRoots =
        Set.range (rootForm B.i) ∧
      AffineRootSystem.IsAffineRootSystemWithRankZero B.affineRoots ∧
      AffineRootSystem.derivativeRoots B.affineRoots ⊆ Set.range (rootForm B.i) ∧
      (∀ ψ ∈ B.apartment.extendedAffineRoots,
        ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots) ∧
      AffineRootSystem.affineWeylGroup B.affineRoots ≤
        B.apartment.normalizerAffineEquiv.range ∧
      B.apartment.normalizerAffineEquiv.range ≤
        AffineRootSystem.extendedAffineWeylGroup B.affineRoots

theorem valuationBuildingAffineRootSystems :
    ValuationBuildingAffineRootSystemsStatement.{u} := by
  intro F _ _ _ _ G _ B
  have h4 : ∀ ψ ∈ B.apartment.extendedAffineRoots,
      ψ ∈ B.affineRoots ∨ (2 : ℝ) • ψ ∈ B.affineRoots := fun ψ hψ =>
    B.affineRoot_mem_or_two_smul_mem_of_oppositePairs B.hasOppositeFactorPairs ψ hψ
  refine ⟨B.isAffineRootSystemWithRankZero_extendedAffineRoots,
    B.derivativeRoots_extendedAffineRoots, B.isAffineRootSystemWithRankZero_affineRoots,
    ?_, h4, B.affineWeylGroup_le_range_of_AS3 B.isAffineRootSystemWithRankZero_affineRoots,
    B.range_le_extendedAffineWeylGroup_of_AS4 h4⟩
  rintro f ⟨ψ, ⟨a, hlin, _⟩, rfl⟩
  exact ⟨a, hlin.symm⟩

end Langlands.Geometry.Building

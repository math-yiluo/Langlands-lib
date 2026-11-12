import Langlands.Representation.Families.RenardFamilyParabolicFlatnessStatements
import Langlands.Representation.Families.RenardFamilyFixedTensorProof
import Langlands.Representation.Plancherel.UnramifiedRationalNormalizedInducedFinitenessProof
import Langlands.Representation.Induction.FixedVectorModel
import Langlands.Representation.Jacquet.LocalizationExactnessStatement
import Langlands.Representation.Exponents.LeviRadicalCompactSubgroups
import Langlands.Representation.Exponents.ArbitraryParabolicInductionAdmissibility
import Langlands.Representation.Exponents.ArbitraryParabolicFiniteSupportReduction
import Langlands.GroupScheme.Absolute.ParabolicDynamicProof
import Langlands.BruhatTits.Parabolic.QuotientCompactProof

/-!
# Renard VI.8.2–VI.8.3: flatness of induction and Jacquet modules, admissibility of induction

Proofs of `InductionFlatStatement`, `InductionAdmissibleStatement`, `JacquetFlatStatement` and
their conjunction `ParabolicFlatnessStatements`.

* Coinvariants of a smooth family on a flat module under a limit of compact subgroups are flat:
  a relation in the coinvariants lifts to a relation of one compact subgroup, where averaging
  moves it into the flat fixed module.
* For a semidirect decomposition with compact `P \ G`, normalized induction of a smooth family
  on a flat module is flat, since its compact-open fixed modules are finite products of fixed
  modules of the inducing representation, each an averaging retract of the flat module. With
  finitely generated compact-open fixed modules of the Levi family and a Noetherian coefficient
  ring, the induced compact-open fixed modules are finitely generated.
* Compactness of the actual parabolic quotient comes from the published proofs
  `GroupScheme.parabolicDynamic` and `BruhatTits.dynamicParabolicQuotientCompact`.
-/

noncomputable section

open CategoryTheory AlgebraicGeometry
open scoped CategoryTheory.MonObj

namespace Langlands.Renard.AlgebraicFamily

open Langlands.Aubert.General Langlands.Aubert.General.RepresentedParabolic GroupScheme

universe uB uG uV

section Fixed

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module B V]

/-- Compact-open fixed vectors of a smooth family on a flat module are flat: averaging makes
them a `B`-linear retract. -/
theorem flat_fixedVectors (ρ : Representation B G V) (hρ : IsSmooth ρ) [Module.Flat B V]
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Module.Flat B (fixedVectors ρ K.toSubgroup) :=
  Module.Flat.of_retract (fixedVectors ρ K.toSubgroup).subtype
    (coefficientFixedProjection ρ hρ K hK) (coefficientFixedProjection_comp ρ hρ K hK)

/-- Averaging is unchanged by first translating by an element of the compact subgroup. -/
theorem coefficientAverage_apply_rho (ρ : Representation B G V) (hρ : IsSmooth ρ)
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) (x : K) (v : V) :
    coefficientAverage ρ hρ K hK (ρ x.val v) = coefficientAverage ρ hρ K hK v := by
  let := Module.restrictScalars ℂ B V
  let := IsScalarTower.restrictScalars ℂ B V
  exact Compact.CharZero.orbitMean_apply (k := ℂ) _ x v

end Fixed

section Coinvariants

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  {V : Type uV} [AddCommGroup V] [Module B V]

open Jacquet.Localization

omit [Algebra ℂ B] [IsTopologicalGroup G] in
/-- Over any coefficient ring, a coinvariant relation for a limit of compact subgroups is a
relation for one compact subgroup. -/
theorem exists_compact_mem_relations (ρ : Representation B G V) (U : Subgroup G)
    (hU : IsLimitOfCompactSubgroups U) {v : V} (hv : v ∈ relations ρ U 1) :
    ∃ K : Subgroup U, IsCompact (K : Set U) ∧ v ∈ relations (ρ.comp U.subtype) K 1 := by
  classical
  obtain ⟨T, hT, hvT⟩ := Submodule.mem_span_finite_of_mem_span hv
  choose uv huv using hT
  let s : Finset U := T.attach.image (fun x => (uv x.property).1)
  obtain ⟨K, hK, hsK⟩ := hU s (Set.Finite.isCompact (Finset.finite_toSet s))
  refine ⟨K, hK, ?_⟩
  apply (Submodule.span_le.mpr ?_) hvT
  intro x hx
  have hu : (uv hx).1 ∈ K :=
    hsK (Finset.mem_image.mpr ⟨⟨x, hx⟩, Finset.mem_attach _ _, rfl⟩)
  rw [← huv hx]
  exact sub_mem_relations (ρ.comp U.subtype) K 1 ⟨(uv hx).1, hu⟩ (uv hx).2

/-- The coinvariants `V_U` of a smooth family on a flat module, for a subgroup `U` that is a
limit of compact subgroups, are flat. -/
theorem flat_coinvariants (ρ : Representation B G V) (hρ : IsSmooth ρ) [Module.Flat B V]
    (U : Subgroup G) (hU : IsLimitOfCompactSubgroups U) :
    Module.Flat B (Coinvariants ρ U 1) := by
  classical
  apply Module.Flat.of_forall_isTrivialRelation
  intro n f x hfx
  choose v hv using fun i => mk_surjective ρ U 1 (x i)
  have hrel : ∑ i, f i • v i ∈ relations ρ U 1 := by
    apply (mk_eq_zero ρ U 1 _).mp
    simpa only [map_sum, map_smul, hv] using hfx
  obtain ⟨K, hK, hKrel⟩ := exists_compact_mem_relations ρ U hU hrel
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let ρK : Representation B K V := (ρ.comp U.subtype).comp K.subtype
  have hρK : IsSmooth ρK :=
    isSmooth_comp K.subtype continuous_subtype_val
      (isSmooth_comp U.subtype continuous_subtype_val hρ)
  have hTop : IsCompact ((⊤ : OpenSubgroup K) : Set K) := by
    simpa only [OpenSubgroup.coe_top] using isCompact_univ
  let e := coefficientFixedProjection ρK hρK ⊤ hTop
  have := flat_fixedVectors ρK hρK ⊤ hTop
  -- averaging kills the relations of the compact subgroup
  have hker : relations (ρ.comp U.subtype) K 1 ≤ LinearMap.ker e := by
    rw [relations_le_ker_iff]
    intro k w
    simp only [MonoidHom.one_apply, Units.val_one, one_smul]
    apply Subtype.ext
    exact coefficientAverage_apply_rho ρK hρK ⊤ hTop ⟨k, Subgroup.mem_top k⟩ w
  -- averaging does not change the class in the coinvariants
  let τ : Representation B K (Coinvariants ρ U 1) := Representation.trivial B K _
  have hτ : IsSmooth τ := fun w => ⟨⊤, fun _ => rfl⟩
  have hmk (w : V) : mk ρ U 1 (e w).val = mk ρ U 1 w := by
    have hnat := coefficientAverage_natural ρK τ hρK hτ ⊤ hTop (mk ρ U 1) (fun g w => by
      change mk ρ U 1 (ρ (g.val : G) w) = mk ρ U 1 w
      rw [mk_apply_subgroup ρ U 1 g.val w]
      simp) w
    exact hnat.trans (coefficientAverage_fixed τ hτ ⊤ hTop _ (fun _ => rfl))
  have he0 : ∑ i, f i • e (v i) = 0 := by
    rw [← LinearMap.mem_ker.mp (hker hKrel), map_sum]
    simp only [map_smul]
  obtain ⟨m, a, y, hxy, ha⟩ := Module.Flat.isTrivialRelation_of_sum_smul_eq_zero he0
  refine ⟨m, a, fun j => mk ρ U 1 (y j).val, ?_, ha⟩
  intro i
  have hxi : e (v i) = ∑ j, a i j • y j := hxy i
  rw [← hv i, ← hmk (v i), hxi]
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul]

end Coinvariants

section Induction

variable {B : Type uB} [CommRing B] [Algebra ℂ B]
  {G : Type uG} [Group G] [TopologicalSpace G] [LocallyCompactSpace G]
  [NonarchimedeanGroup G] {P M U : Subgroup G}
  (h : IsSemidirectDecomposition P M U) (hU : IsClosed (U : Set G))
  {V : Type uV} [AddCommGroup V] [Module B V]

/-- The inducing representation of a smooth family is smooth. -/
theorem isSmooth_inducingRepresentation (hproj : Continuous h.projection)
    (σ : Representation B M V) (hσ : IsSmooth σ) :
    IsSmooth (inducingRepresentation h hU σ) :=
  isSmooth_comp h.projection hproj
    ((isSmooth_twist_iff _ σ (inductionCharacter B U M hU h.levi_le_normalizer).isOpen_ker).mpr
      hσ)

/-- Normalized induction of a smooth family on a flat module is flat when `P \ G` is
compact. -/
theorem flat_induced [CompactSpace (Induction.LeftQuotient P)] (hP : IsClosed (P : Set G))
    (hproj : Continuous h.projection) (σ : Representation B M V) (hσ : IsSmooth σ)
    [Module.Flat B V] : Module.Flat B (Induced h hU σ) := by
  apply Plancherel.RationalNormalized.flat_of_smooth_fixed_flat (inducedRepresentation h hU σ)
    (isSmooth_inducedRepresentation h hU σ)
  intro K hK
  obtain ⟨t, hcover, hdistinct⟩ := Induction.exists_finset_doubleCoset_representatives P K
  have hτ := isSmooth_inducingRepresentation h hU hproj σ hσ
  have (i : t) : Module.Flat B (fixedVectors (inducingRepresentation h hU σ)
      (Induction.conjOpenSubgroup P K i).toSubgroup) :=
    flat_fixedVectors _ hτ _ (Induction.isCompact_conjOpenSubgroup P hP K hK i)
  have : Module.Flat B ((i : t) → fixedVectors (inducingRepresentation h hU σ)
      (Induction.conjOpenSubgroup P K i).toSubgroup) :=
    Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := B)).symm
  exact Module.Flat.of_linearEquiv
    (Induction.fixedEvaluationEquiv P (inducingRepresentation h hU σ) K hK t hcover hdistinct)

/-- The fixed vectors of the inducing representation under a compact open subgroup `Q` of
`P` lie in the fixed vectors of the Levi family under a compact open subgroup of `M`. -/
theorem exists_inducing_fixedVectors_le (hM : IsClosed (M : Set G))
    (σ : Representation B M V) (Q : OpenSubgroup P) (hQ : IsCompact (Q : Set P)) :
    ∃ N : OpenSubgroup M, IsCompact (N : Set M) ∧
      fixedVectors (inducingRepresentation h hU σ) Q.toSubgroup ≤
        fixedVectors σ N.toSubgroup := by
  let χ := inductionCharacter B U M hU h.levi_le_normalizer
  let N₀ : OpenSubgroup M :=
    Q.comap (Subgroup.inclusion h.levi_le) (continuous_inclusion h.levi_le)
  let N : OpenSubgroup M := N₀ ⊓ ⟨χ.toMonoidHom.ker, χ.isOpen_ker⟩
  have hN₀ : (N₀ : Set M) =
      (Subtype.val : M → G) ⁻¹' ((Subtype.val : P → G) '' (Q : Set P)) := by
    ext n
    constructor
    · intro hn
      exact ⟨Subgroup.inclusion h.levi_le n, hn, rfl⟩
    · rintro ⟨q, hq, hqn⟩
      have : q = Subgroup.inclusion h.levi_le n := Subtype.ext hqn
      change Subgroup.inclusion h.levi_le n ∈ Q
      rw [← this]
      exact hq
  have hN₀c : IsCompact (N₀ : Set M) := by
    rw [hN₀]
    exact hM.isClosedEmbedding_subtypeVal.isCompact_preimage
      (hQ.image continuous_subtype_val)
  refine ⟨N, ?_, ?_⟩
  · rw [OpenSubgroup.coe_inf]
    exact hN₀c.inter_right (OpenSubgroup.isClosed ⟨χ.toMonoidHom.ker, χ.isOpen_ker⟩)
  · intro v hv n
    obtain ⟨hn₀, hnχ⟩ := OpenSubgroup.mem_inf.mp n.property
    have hfix := hv ⟨Subgroup.inclusion h.levi_le n.val, hn₀⟩
    have hχn : χ.toMonoidHom n.val = 1 := hnχ
    change (χ.toMonoidHom (h.projection (Subgroup.inclusion h.levi_le n.val)) : B) •
        σ (h.projection (Subgroup.inclusion h.levi_le n.val)) v = v at hfix
    have hp : h.projection (Subgroup.inclusion h.levi_le n.val) = n.val :=
      h.projection_levi n.val
    rw [hp, hχn, Units.val_one, one_smul] at hfix
    exact hfix

/-- Normalized induction from a subgroup with compact coset space sends Levi families with
finite compact-open fixed modules to families with finite compact-open fixed modules. -/
theorem finite_fixedVectors_induced [IsNoetherianRing B]
    [CompactSpace (Induction.LeftQuotient P)] (hP : IsClosed (P : Set G))
    (hM : IsClosed (M : Set G)) (σ : Representation B M V)
    (hfin : ∀ N : OpenSubgroup M, IsCompact (N : Set M) →
      Module.Finite B (fixedVectors σ N.toSubgroup))
    (K : OpenSubgroup G) (hK : IsCompact (K : Set G)) :
    Module.Finite B (fixedVectors (inducedRepresentation h hU σ) K.toSubgroup) := by
  obtain ⟨t, ht⟩ := Induction.exists_finset_doubleCoset_cover P K
  have (i : t) : Module.Finite B (fixedVectors (inducingRepresentation h hU σ)
      (Induction.conjOpenSubgroup P K i).toSubgroup) := by
    obtain ⟨N, hN, hle⟩ := exists_inducing_fixedVectors_le h hU hM σ _
      (Induction.isCompact_conjOpenSubgroup P hP K hK i)
    have := hfin N hN
    exact Module.Finite.of_injective (Submodule.inclusion hle)
      (Submodule.inclusion_injective hle)
  exact Module.Finite.of_injective
    (Induction.fixedEvaluation P (inducingRepresentation h hU σ) K t)
    (Induction.fixedEvaluation_injective P (inducingRepresentation h hU σ) K t ht)

end Induction

section Targets

universe u' uB' uE' uV'

/-- Renard VI.8.2, before the Lemma: normalized parabolic induction of an `(M(F), B)`-module is
`B`-flat. -/
theorem inductionFlat : InductionFlatStatement.{u', uB', uE'} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  let := leviPointTopology l hl
  intro B _ _ _ _ _ E _ _ σ hσ hE
  have := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  exact flat_induced (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup)
    (continuous_projection_pointImage p l r hp hl hr hmul)
    (leviImageRepresentation p l hp hl σ)
    (isSmooth_comp _ (leviPointsEquiv p l hp hl).symm.continuous hσ)

/-- Renard VI.8.2 Lemma: normalized parabolic induction preserves finiteness of the
compact-open fixed modules. -/
theorem inductionAdmissible : InductionAdmissibleStatement.{u', uB', uE'} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P M U p l r hp hl hr hmul
  let := leviPointTopology l hl
  intro B _ _ _ _ _ E _ _ σ _ _ hfin K hK
  have := compactSpace_leftQuotient_pointImage_of_dynamic parabolicDynamic
    BruhatTits.dynamicParabolicQuotientCompact hG p hp
  let e := leviPointsEquiv p l hp hl
  refine finite_fixedVectors_induced
    (isSemidirectDecomposition_pointImage p l r hp.isClosedSubgroup hr hmul)
    (isClosed_pointImage_comp p r hp.isClosedSubgroup hr.1.isClosedSubgroup)
    (isClosed_pointImage p hp.isClosedSubgroup) (isClosed_leviPoints p l hp hl)
    (leviImageRepresentation p l hp hl σ) (fun N hN => ?_) K hK
  let N' : OpenSubgroup (rationalPoints M) := N.comap e.toMonoidHom e.continuous
  have hN' : IsCompact (N' : Set (rationalPoints M)) :=
    e.toHomeomorph.isCompact_preimage.mpr hN
  have heq : fixedVectors (leviImageRepresentation p l hp hl σ) N.toSubgroup =
      fixedVectors σ N'.toSubgroup := by
    ext v
    constructor
    · intro hv m
      have := hv ⟨e m.val, m.property⟩
      change σ (e.symm (e m.val)) v = v at this
      rw [e.symm_apply_apply] at this
      exact this
    · intro hv n
      have hn : e.symm n.val ∈ N' := by
        change e (e.symm n.val) ∈ N
        rw [e.apply_symm_apply]
        exact n.property
      exact hv ⟨e.symm n.val, hn⟩
  rw [heq]
  exact hfin N' hN'

/-- Renard VI.8.3, before the Proposition: the Jacquet module of a `(G(F), B)`-module is
`B`-flat. -/
theorem jacquetFlat : JacquetFlatStatement.{u', uB', uV'} := by
  intro k _ _ _ _ _ G hG
  have := hG.isAffineHom
  let : TopologicalSpace (rationalPoints G) := RationalPointFamily.pointTopology
  intro _ _ P U p r hp hr B _ _ _ _ _ V _ _ ρ hρ hV
  exact flat_coinvariants ρ hρ (pointImage (r ≫ p))
    (isLimitOfCompactSubgroups_pointImage_radical p r hp.isClosedSubgroup hr.1)

/-- Renard VI.8.2–VI.8.3: the three statements together. -/
theorem parabolicFlatness : ParabolicFlatnessStatements.{u', uB', uE', uV'} :=
  ⟨inductionFlat, inductionAdmissible, jacquetFlat⟩

end Targets

end Langlands.Renard.AlgebraicFamily

import Langlands.Global.EisensteinConstantTerm.UnfoldingAbstract
import Langlands.Global.EisensteinConstantTerm.GeometricLemmaUnfoldingStatement
import Langlands.Global.EisensteinConstantTerm.Points
import Langlands.Global.AdelicIntertwiningStabilizer
import Langlands.Global.AdelicIntertwiningConvergenceReduction

/-! # The unfolding identity of the geometric lemma on adelic points -/

noncomputable section

universe u v

open CategoryTheory AlgebraicGeometry MeasureTheory Set Topology
open scoped ENNReal NNReal

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme LeftCosetSpace

attribute [local instance] locallyCompactSpace_of_isClosed_subgroup
  secondCountableTopology_subgroup isClosed_conjStab

section Quotient

variable {X : Type u} [Group X] [TopologicalSpace X] [IsTopologicalGroup X]
  [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
  (Γ : Subgroup X) (hΓ : IsDiscrete (Γ : Set X)) (μ : Measure X)

omit [TopologicalSpace X] [IsTopologicalGroup X] [SecondCountableTopology X]
  [MeasurableSpace X] [BorelSpace X] in
theorem out_mk_eq_mul (x : X) : ∃ γ ∈ Γ, Quotient.out (mk Γ x) = γ * x := by
  have h : mk Γ (Quotient.out (mk Γ x)) = mk Γ x := Quotient.out_eq _
  refine ⟨Quotient.out (mk Γ x) * x⁻¹, ?_, by group⟩
  have := (mk_eq_mk_iff Γ x (Quotient.out (mk Γ x))).mp h.symm
  simpa using this

omit [TopologicalSpace X] [IsTopologicalGroup X] [SecondCountableTopology X] [BorelSpace X] in
theorem measurable_comp_out {Y : Type v} [MeasurableSpace Y] (g : X → Y) (hg : Measurable g)
    (hgΓ : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x) :
    Measurable (fun q : LeftCosetSpace Γ => g (Quotient.out q)) := by
  refine measurable_from_quotient.mpr ?_
  have : (fun x : X => g (Quotient.out (Quotient.mk'' x : LeftCosetSpace Γ))) = g := by
    funext x
    obtain ⟨γ, hγ, he⟩ := out_mk_eq_mul Γ x
    change g (Quotient.out (mk Γ x)) = g x
    rw [he, hgΓ γ hγ]
  simpa [Function.comp_def, this] using hg

/-- Integrals of left `Γ`-invariant functions over the discrete quotient, evaluated at the chosen
representatives, are integrals over the chosen fundamental domain. -/
theorem integral_discreteQuotientMeasure_out {E : Type v} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (g : X → E) (hg : Measurable g) (hgΓ : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x) :
    ∫ q, g (Quotient.out q) ∂discreteQuotientMeasure Γ hΓ μ =
      ∫ x in fundamentalDomain Γ hΓ, g x ∂μ := by
  rw [discreteQuotientMeasure, quotientMeasure, integral_map (measurable_mk Γ).aemeasurable
    (measurable_comp_out Γ g hg hgΓ).aestronglyMeasurable]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  obtain ⟨γ, hγ, he⟩ := out_mk_eq_mul Γ x
  change g (Quotient.out (mk Γ x)) = g x
  rw [he, hgΓ γ hγ]

theorem lintegral_discreteQuotientMeasure_out (g : X → ℝ≥0∞) (hg : Measurable g)
    (hgΓ : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x) :
    ∫⁻ q, g (Quotient.out q) ∂discreteQuotientMeasure Γ hΓ μ =
      ∫⁻ x in fundamentalDomain Γ hΓ, g x ∂μ := by
  rw [discreteQuotientMeasure, quotientMeasure,
    lintegral_map (measurable_comp_out Γ g hg hgΓ) (measurable_mk Γ)]
  refine lintegral_congr fun x => ?_
  obtain ⟨γ, hγ, he⟩ := out_mk_eq_mul Γ x
  rw [he, hgΓ γ hγ]

theorem integrable_discreteQuotientMeasure_out_iff {E : Type v} [NormedAddCommGroup E]
    [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    (g : X → E) (hg : Measurable g) (hgΓ : ∀ γ ∈ Γ, ∀ x, g (γ * x) = g x) :
    Integrable (fun q => g (Quotient.out q)) (discreteQuotientMeasure Γ hΓ μ) ↔
      IntegrableOn g (fundamentalDomain Γ hΓ) μ := by
  rw [discreteQuotientMeasure, quotientMeasure, integrable_map_measure
    (measurable_comp_out Γ g hg hgΓ).aestronglyMeasurable (measurable_mk Γ).aemeasurable]
  have : ((fun q : LeftCosetSpace Γ => g (Quotient.out q)) ∘ mk Γ) = g := by
    funext x
    obtain ⟨γ, hγ, he⟩ := out_mk_eq_mul Γ x
    change g (Quotient.out (mk Γ x)) = g x
    rw [he, hgΓ γ hγ]
  rw [this]
  rfl

end Quotient

theorem fundamentalDomain_congr {X : Type u} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [SecondCountableTopology X] [MeasurableSpace X] [BorelSpace X]
    {Γ₁ Γ₂ : Subgroup X} (h : Γ₁ = Γ₂) (h₁ : IsDiscrete (Γ₁ : Set X))
    (h₂ : IsDiscrete (Γ₂ : Set X)) : fundamentalDomain Γ₁ h₁ = fundamentalDomain Γ₂ h₂ := by
  subst h; rfl

theorem normalizedHaar_congr {X : Type u} [Group X] [TopologicalSpace X]
    [IsTopologicalGroup X] [LocallyCompactSpace X] [SecondCountableTopology X]
    [MeasurableSpace X] [BorelSpace X]
    {Γ₁ Γ₂ : Subgroup X} (h : Γ₁ = Γ₂) (h₁ : IsDiscrete (Γ₁ : Set X))
    (h₂ : IsDiscrete (Γ₂ : Set X)) : normalizedHaar Γ₁ h₁ = normalizedHaar Γ₂ h₂ := by
  subst h; rfl

section Adelic

open scoped CategoryTheory.MonObj

variable {F : Type u} [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- The principal image in the adelic points of a subgroup functor consists of rational points. -/
theorem rationalSubgroup_le_latticeOf (W : SubgroupFunctor G) :
    AdelicSubgroupPoints.rationalSubgroup F G W ≤
      latticeOf (AdelicGroupPoints.rationalSubgroup F G) (AdelicSubgroupPoints.adelicPoints F G W) := by
  rintro _ ⟨q, rfl⟩
  exact ⟨q.val, rfl⟩

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- For a closed subgroup, the principal image in its adelic points is the intersection of these
adelic points with the rational points of the ambient group. -/
theorem rationalSubgroup_range_eq_latticeOf (j : H ⟶ G) (hj : IsClosedSubgroup j) :
    AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range j) =
      latticeOf (AdelicGroupPoints.rationalSubgroup F G)
        (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)) := by
  refine le_antisymm (rationalSubgroup_le_latticeOf _) ?_
  rintro v ⟨x, hx⟩
  have hmem : AdelicGroupPoints.rational F G x ∈
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) := by
    rw [hx]; exact v.property
  have hR := (AdelicGroupPoints.rational_mem_adelicPoints_range_iff hj x).mp hmem
  exact ⟨⟨x, hR⟩, Subtype.ext hx⟩

theorem isDiscrete_rationalSubgroupAdelic :
    IsDiscrete (AdelicGroupPoints.rationalSubgroup F G : Set (AdelicGroupPoints F G)) :=
  AdelicGroupPoints.isDiscrete_rationalSubgroup F G

/-- The Library's normalized Haar measure of a closed adelic subgroup is the Haar measure
normalized by the intersection with the rational points. -/
theorem normalizedHaarMeasure_eq_normalizedHaar (j : H ⟶ G) (hj : IsClosedSubgroup j)
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G))] :
    AdelicSubgroupPoints.normalizedHaarMeasure F G (SubgroupFunctor.range j) =
      normalizedHaar (latticeOf (AdelicGroupPoints.rationalSubgroup F G)
          (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)))
        (isDiscrete_latticeOf _ isDiscrete_rationalSubgroupAdelic _) := by
  rw [← normalizedHaar_congr (rationalSubgroup_range_eq_latticeOf j hj)
    (AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G _)]
  unfold AdelicSubgroupPoints.normalizedHaarMeasure AdelicSubgroupPoints.quotientMassNormalizer
    AdelicSubgroupPoints.rationalQuotientHaarMeasure haarQuotientMeasure discreteQuotientMeasure
    normalizedHaar
  rw [quotientMeasure_univ]

/-- The normalized subgroup constant term along a closed subgroup is the average over the chosen
fundamental domain of the rational points, for the normalized Haar measure. -/
theorem subgroupConstantTerm_eq_setIntegral (j : H ⟶ G) [IsAffine H.X.left]
    [IsClosedImmersion j.hom.hom.left]
    [IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j) :
      Set (AdelicGroupPoints F G))]
    (φ : AdelicGroupPoints F G → ℂ) (hφ : Measurable φ)
    (hφR : ∀ z ∈ AdelicGroupPoints.rationalImage F j, ∀ x, φ (z * x) = φ x)
    (x : AdelicGroupPoints F G) :
    AdelicGroupPoints.subgroupConstantTerm F j φ x =
      ∫ u in fundamentalDomain (latticeOf (AdelicGroupPoints.rationalSubgroup F G)
          (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)))
          (isDiscrete_latticeOf _ isDiscrete_rationalSubgroupAdelic _), φ (u.val * x)
        ∂normalizedHaar (latticeOf (AdelicGroupPoints.rationalSubgroup F G)
          (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)))
          (isDiscrete_latticeOf _ isDiscrete_rationalSubgroupAdelic _) := by
  have hj : IsClosedSubgroup j := (inferInstance : IsClosedImmersion j.hom.hom.left)
  set W := SubgroupFunctor.range j
  have hΓd := AdelicSubgroupPoints.isDiscrete_rationalSubgroup F G W
  have hmeas : AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G W =
      discreteQuotientMeasure (AdelicSubgroupPoints.rationalSubgroup F G W) hΓd
        (AdelicSubgroupPoints.normalizedHaarMeasure F G W) := by
    unfold AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure
      AdelicSubgroupPoints.normalizedHaarMeasure AdelicSubgroupPoints.rationalQuotientHaarMeasure
      haarQuotientMeasure discreteQuotientMeasure
    rw [quotientMeasure_smul]
  have hg : Measurable (fun u : AdelicSubgroupPoints.adelicPoints F G W => φ (u.val * x)) :=
    hφ.comp (continuous_subtype_val.mul continuous_const).measurable
  have hgΓ : ∀ g ∈ AdelicSubgroupPoints.rationalSubgroup F G W, ∀ u,
      φ ((g * u).val * x) = φ (u.val * x) := by
    intro g hg u
    have := (AdelicGroupPoints.mem_rationalSubgroup_range_iff j g).mp hg
    rw [Subgroup.coe_mul, mul_assoc]
    exact hφR _ this _
  change ∫ q, φ ((Quotient.out q : AdelicSubgroupPoints.adelicPoints F G W).val * x)
    ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G W = _
  rw [hmeas, integral_discreteQuotientMeasure_out _ hΓd _ (fun u => φ (u.val * x)) hg hgΓ,
    normalizedHaarMeasure_eq_normalizedHaar j hj,
    fundamentalDomain_congr (rationalSubgroup_range_eq_latticeOf j hj) hΓd
      (isDiscrete_latticeOf _ isDiscrete_rationalSubgroupAdelic _)]

omit [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] in
/-- One compact set meets every orbit of the rational points in the adelic points of a smooth
connected unipotent subgroup. -/
theorem exists_cover_latticeOf_range (j : H ⟶ G) [IsAffine H.X.left] (hs : Smooth H.X.hom)
    (hc : ConnectedSpace H.X.left) (hu : IsUnipotent H) :
    ∃ C : Set (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)), IsCompact C ∧
      ∀ k, ∃ g ∈ latticeOf (AdelicGroupPoints.rationalSubgroup F G)
        (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)), g * k ∈ C := by
  obtain ⟨Ω, hΩ, hcov⟩ := AdelicSubgroupPoints.exists_isCompact_rational_mul_mem_range F j hs hc hu
  exact ⟨Ω, hΩ, fun k => (hcov k).imp fun g hg => ⟨rationalSubgroup_le_latticeOf _ hg.1, hg.2⟩⟩


/-- One compact set meets every orbit of the rational lattice in the adelic stabilizer
`V(𝔸) ∩ w U(𝔸) w⁻¹`, for closed `V` unipotent and `U` closed. -/
theorem exists_cover_conjStab {P U V : GroupScheme (Spec (CommRingCat.of F))}
    (p : P ⟶ G) (iU : U ⟶ P) (j : V ⟶ G) (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    [IsAffine V.X.left] [IsAffineHom V.X.hom] [LocallyOfFiniteType V.X.hom]
    [IsClosedImmersion j.hom.hom.left] (hi : IsClosedSubgroup (iU ≫ p)) (hVu : IsUnipotent V) :
    ∃ C : Set (conjStab (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))
        (AdelicGroupPoints.parabolicUnipotentImage F p iU)
        (Langlands.Automorphic.GroupSchemeFunctions.innerAdelicPoint F G w)),
      IsCompact C ∧ ∀ k, ∃ g ∈ conjStabLattice (AdelicGroupPoints.rationalSubgroup F G)
        (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j))
        (Langlands.Automorphic.GroupSchemeFunctions.innerAdelicPoint F G w)
        (AdelicGroupPoints.parabolicUnipotentImage F p iU), g * k ∈ C := by
  have hj : IsClosedSubgroup j := (inferInstance : IsClosedImmersion j.hom.hom.left)
  obtain ⟨-, ⟨hComp⟩, -⟩ := AdelicGroupPoints.intertwiningStabilizer p iU j w hj hi hVu
  obtain ⟨hk, -, -, -⟩ := AdelicGroupPoints.intertwiningStabilizer_geometry p iU j w hj hi hVu
  set k := AdelicGroupPoints.intertwiningStabilizerHom p iU j w
  have : IsClosedImmersion k.hom.hom.left := hk
  have : IsAffine (AdelicGroupPoints.IntertwiningStabilizer p iU j w).X.left :=
    isAffine_of_isAffineHom k.hom.hom.left
  have : IsClosed (AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range k) :
      Set (AdelicGroupPoints F G)) := AdelicSubgroupPoints.isClosed_adelicPoints_range F G k
  have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range k)) :=
    hComp
  obtain ⟨C₀, hC₀, hcov⟩ := LeftCosetSpace.exists_isCompact_cover
    (AdelicSubgroupPoints.rationalSubgroup F G (SubgroupFunctor.range k))
  set e := AdelicGroupPoints.intertwiningStabilizerEquiv p iU j w
  set wA := Langlands.Automorphic.GroupSchemeFunctions.innerAdelicPoint F G w
  set Va := AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range j)
  have hmem : ∀ v : Va, v ∈ AdelicGroupPoints.intertwiningAdelicStabilizer p iU j w ↔
      v ∈ conjStab Va (AdelicGroupPoints.parabolicUnipotentImage F p iU) wA := fun v =>
    (AdelicGroupPoints.mem_intertwiningAdelicStabilizer_iff p iU j w v).trans
      (mem_conjStab v).symm
  let qh : AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range k) →*
      conjStab Va (AdelicGroupPoints.parabolicUnipotentImage F p iU) wA :=
    ((AdelicGroupPoints.intertwiningAdelicStabilizer p iU j w).subtype.comp
      e.toMulEquiv.toMonoidHom).codRestrict _ (fun x => (hmem _).mp (e x).property)
  have hqc : Continuous qh :=
    (continuous_subtype_val.comp e.continuous).subtype_mk _
  have hqs : Function.Surjective qh := by
    intro n
    refine ⟨e.symm ⟨n.val, (hmem _).mpr n.property⟩, ?_⟩
    apply Subtype.ext
    change (e (e.symm ⟨n.val, _⟩)).val = n.val
    rw [e.apply_symm_apply]
  exact exists_cover_of_map _ hC₀ hcov qh hqc hqs _ (fun g hg =>
    ⟨show ((qh g : Va) : AdelicGroupPoints F G) ∈ AdelicGroupPoints.rationalSubgroup F G from
      rationalSubgroup_le_latticeOf (SubgroupFunctor.range k) hg, (qh g).property⟩)


end Adelic

section Structure

open scoped CategoryTheory.MonObj
open AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions

variable (F : Type u) [Field F] [NumberField F]
  {G P U Q V P' U' Q' V' : GroupScheme (Spec (CommRingCat.of F))}
  (p : P ⟶ G) (iU : U ⟶ P) (q : Q ⟶ G) (iV : V ⟶ Q)
  (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (f : P' ⟶ P) (iU' : U' ⟶ P') (g' : Q' ⟶ Q) (iV' : V' ⟶ Q')

/-- The subgroup facts in `G(𝔸)` from which the unfolding identity of the geometric lemma
follows. Write `V = V(𝔸)`, `V' = V'(𝔸)`, `U = U(𝔸)`, `U' = U'(𝔸)` for the adelic points of the
four radicals in `G(𝔸)`, `w` for the rational point and `G(F)` for the rational points:

1. `V(F) ∩ w P(F) w⁻¹ ⊆ w U' w⁻¹`;
2. a closed subgroup `A ≤ U'` with `w A w⁻¹ ⊆ V` complements the normal subgroup `U ≤ U'`
   (`U' = U A`, `U ∩ A = 1`), and the `A`-component of a rational point of `U'` is rational;
3. a closed subgroup `B ≤ V'` with `w⁻¹ B w ⊆ U` complements the normal subgroup `V ≤ V'`, and
   the `B`-component of a rational point of `V'` is rational. -/
def UnfoldingSubgroupStructure : Prop :=
  (∀ v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
    v ∈ AdelicGroupPoints.rationalSubgroup F G →
    (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈ rationalImage F p →
    (innerAdelicPoint F G w)⁻¹ * v * innerAdelicPoint F G w ∈
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p))) ∧
  (∃ A : Subgroup (AdelicGroupPoints F G), IsClosed (A : Set (AdelicGroupPoints F G)) ∧
    A ≤ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p)) ∧
    (∀ a ∈ A, innerAdelicPoint F G w * a * (innerAdelicPoint F G w)⁻¹ ∈
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) ∧
    parabolicUnipotentImage F p iU ≤
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p)) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p)),
      ∀ u ∈ parabolicUnipotentImage F p iU, x * u * x⁻¹ ∈ parabolicUnipotentImage F p iU) ∧
    (∀ a ∈ A, a ∈ parabolicUnipotentImage F p iU → a = 1) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p)),
      ∃ u ∈ parabolicUnipotentImage F p iU, ∃ a ∈ A, u * a = x) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iU' ≫ f ≫ p)),
      x ∈ AdelicGroupPoints.rationalSubgroup F G → ∀ u ∈ parabolicUnipotentImage F p iU,
        ∀ a ∈ A, u * a = x → a ∈ AdelicGroupPoints.rationalSubgroup F G)) ∧
  (∃ B : Subgroup (AdelicGroupPoints F G), IsClosed (B : Set (AdelicGroupPoints F G)) ∧
    B ≤ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)) ∧
    (∀ b ∈ B, (innerAdelicPoint F G w)⁻¹ * b * innerAdelicPoint F G w ∈
      parabolicUnipotentImage F p iU) ∧
    AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) ≤
      AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)),
      ∀ v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
        x * v * x⁻¹ ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q))) ∧
    (∀ b ∈ B, b ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)) →
      b = 1) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)),
      ∃ v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
        ∃ b ∈ B, v * b = x) ∧
    (∀ x ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV' ≫ g' ≫ q)),
      x ∈ AdelicGroupPoints.rationalSubgroup F G →
      ∀ v ∈ AdelicSubgroupPoints.adelicPoints F G (SubgroupFunctor.range (iV ≫ q)),
        ∀ b ∈ B, v * b = x → b ∈ AdelicGroupPoints.rationalSubgroup F G))

end Structure

end Langlands.Global

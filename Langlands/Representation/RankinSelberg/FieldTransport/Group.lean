import Langlands.Analysis.Local.QuotientMeasure
import Langlands.Representation.Whittaker.Algebraic

/-!
# Quotient measures and Whittaker models along a group isomorphism

For a topological group isomorphism `Θ : G ≃ₜ* G'` carrying a subgroup `H` onto
`H'`, the left coset spaces are homeomorphic, and pushforward along `Θ` carries
compatible quotient measures to compatible quotient measures. For a group
isomorphism carrying `N` onto `N'` and a character `θ` to `θ'`, the equivariant
functionals of a pulled-back representation are those of the original one, and
the coefficient models correspond by composition with `Θ⁻¹`.
-/

noncomputable section

open MeasureTheory MeasureTheory.Measure

universe uG uG' uR uV uα uβ uγ uδ

namespace Langlands.QuotientIntegration

section ProdMap

variable {α : Type uα} {β : Type uβ} {γ : Type uγ} {δ : Type uδ}
  [MeasurableSpace α] [MeasurableSpace β] [MeasurableSpace γ] [MeasurableSpace δ]

/-- Product measures commute with pushforward along measurable equivalences.
Only the second factor needs to be s-finite. -/
theorem map_prod_map_measurableEquiv (eα : α ≃ᵐ β) (eγ : γ ≃ᵐ δ) (μ : Measure α)
    (ν : Measure γ) [SFinite ν] :
    (μ.map eα).prod (ν.map eγ) = (μ.prod ν).map (Prod.map eα eγ) := by
  ext s hs
  rw [Measure.prod_apply hs, lintegral_map_equiv,
    Measure.map_apply (eα.measurable.prodMap eγ.measurable) hs,
    Measure.prod_apply ((eα.measurable.prodMap eγ.measurable) hs)]
  apply lintegral_congr
  intro x
  rw [MeasurableEquiv.map_apply]
  rfl

/-- Integrability on a pushed-forward product measure. -/
theorem integrable_map_prod_map_iff {E : Type*} [NormedAddCommGroup E]
    (eα : α ≃ᵐ β) (eγ : γ ≃ᵐ δ) (μ : Measure α) (ν : Measure γ) [SFinite ν]
    (f : β × δ → E) :
    Integrable f ((μ.map eα).prod (ν.map eγ)) ↔
      Integrable (fun x : α × γ => f (eα x.1, eγ x.2)) (μ.prod ν) := by
  rw [map_prod_map_measurableEquiv]
  exact integrable_map_equiv (eα.prodCongr eγ) f

end ProdMap

section Invariance

variable {G : Type uG} {G' : Type uG'} [Group G] [Group G']
  [MeasurableSpace G] [MeasurableSpace G'] [MeasurableMul G] [MeasurableMul G']

/-- Pushforward along a measurable group isomorphism preserves right invariance. -/
theorem isMulRightInvariant_map_mulEquiv (μ : Measure G) [IsMulRightInvariant μ]
    (e : G ≃* G') (he : Measurable e) : IsMulRightInvariant (μ.map e) := by
  refine ⟨fun h => ?_⟩
  rw [map_map (measurable_mul_const _) he]
  obtain ⟨g, rfl⟩ := e.surjective h
  conv_rhs => rw [← map_mul_right_eq_self μ g]
  rw [map_map he (measurable_mul_const _)]
  congr 2
  ext y
  simp

end Invariance

section InvarianceTopological

variable {G : Type uG} {G' : Type uG'} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G'] [MeasurableSpace G] [MeasurableSpace G']
  [BorelSpace G] [BorelSpace G'] [MeasurableMul G] [MeasurableMul G']

/-- Right invariance is preserved and reflected by pushforward along a
topological group isomorphism. -/
theorem isMulRightInvariant_map_iff (Θ : G ≃ₜ* G') (μ : Measure G) :
    IsMulRightInvariant (μ.map Θ) ↔ IsMulRightInvariant μ := by
  constructor
  · intro h
    have hμ : μ = (μ.map Θ).map Θ.symm :=
      (MeasurableEquiv.map_symm_map Θ.toHomeomorph.toMeasurableEquiv).symm
    rw [hμ]
    exact isMulRightInvariant_map_mulEquiv _ Θ.symm.toMulEquiv Θ.symm.continuous.measurable
  · intro h
    exact isMulRightInvariant_map_mulEquiv μ Θ.toMulEquiv Θ.continuous.measurable

end InvarianceTopological

section Quotient

variable {G : Type uG} {G' : Type uG'} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G']
  (Θ : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'} (hH : ∀ g, Θ g ∈ H' ↔ g ∈ H)

/-- The homeomorphism of left coset spaces `H \ G ≃ H' \ G'` induced by `Θ`. -/
def cosetHomeomorph : LeftQuotient H ≃ₜ LeftQuotient H' :=
  Homeomorph.Quotient.congr Θ.toHomeomorph (by
    intro x y
    change QuotientGroup.rightRel H x y ↔ QuotientGroup.rightRel H' (Θ x) (Θ y)
    rw [QuotientGroup.rightRel_apply, QuotientGroup.rightRel_apply, ← map_inv, ← map_mul,
      hH])

@[simp] theorem cosetHomeomorph_mk (g : G) :
    cosetHomeomorph Θ hH (Quotient.mk _ g) = Quotient.mk _ (Θ g) := rfl

/-- The restriction of `Θ` to the subgroups, as a topological group isomorphism. -/
def subgroupEquiv : H ≃ₜ* H' where
  toFun h := ⟨Θ (h : G), (hH (h : G)).2 h.2⟩
  invFun h := ⟨Θ.symm h, (hH _).1 (by simpa only [ContinuousMulEquiv.apply_symm_apply] using h.2)⟩
  left_inv h := Subtype.ext (Θ.symm_apply_apply h)
  right_inv h := Subtype.ext (Θ.apply_symm_apply h)
  map_mul' a b := Subtype.ext (map_mul Θ (a : G) (b : G))
  continuous_toFun := (Θ.continuous.comp continuous_subtype_val).subtype_mk _
  continuous_invFun := (Θ.symm.continuous.comp continuous_subtype_val).subtype_mk _

@[simp] theorem subgroupEquiv_apply_coe (h : H) :
    ((subgroupEquiv Θ hH h : H') : G') = Θ (h : G) := rfl

/-- Right translation commutes with the induced quotient homeomorphism. -/
theorem rightTranslate_cosetHomeomorph [IsTopologicalGroup G] [IsTopologicalGroup G']
    (g : G) (q : LeftQuotient H) :
    rightTranslate H' (Θ g) (cosetHomeomorph Θ hH q) =
      cosetHomeomorph Θ hH (rightTranslate H g q) := by
  induction q using Quotient.inductionOn with
  | h x => simp only [cosetHomeomorph_mk, rightTranslate_mk, map_mul]

end Quotient

section Compatible

variable {G : Type uG} {G' : Type uG'} [Group G] [Group G']
  [TopologicalSpace G] [TopologicalSpace G'] [IsTopologicalGroup G] [IsTopologicalGroup G']
  [MeasurableSpace G] [BorelSpace G] [MeasurableSpace G'] [BorelSpace G']
  (Θ : G ≃ₜ* G') {H : Subgroup G} {H' : Subgroup G'} (hH : ∀ g, Θ g ∈ H' ↔ g ∈ H)
  [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
  [MeasurableSpace H'] [BorelSpace H'] [MeasurableMul H']
  [MeasurableSpace (LeftQuotient H)] [BorelSpace (LeftQuotient H)]
  [MeasurableSpace (LeftQuotient H')] [BorelSpace (LeftQuotient H')]

/-- The quotient homeomorphism as a measurable equivalence of the Borel quotients. -/
abbrev leftQuotientMeasurableEquiv : LeftQuotient H ≃ᵐ LeftQuotient H' :=
  (cosetHomeomorph Θ hH).toMeasurableEquiv

/-- The group isomorphism as a measurable equivalence. -/
abbrev groupMeasurableEquiv : G ≃ᵐ G' := Θ.toHomeomorph.toMeasurableEquiv

/-- The subgroup isomorphism as a measurable equivalence. -/
abbrev subgroupMeasurableEquiv : H ≃ᵐ H' := (subgroupEquiv Θ hH).toHomeomorph.toMeasurableEquiv

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace G'] [BorelSpace G'] [MeasurableSpace (LeftQuotient H)]
  [BorelSpace (LeftQuotient H)] [MeasurableSpace (LeftQuotient H')]
  [BorelSpace (LeftQuotient H')] in
/-- Orbital integrals correspond: averaging `f'` over `H'` at the image of `q`
is averaging `f' ∘ Θ` over `H` at `q`, for the pushed-forward subgroup measure. -/
theorem quotientAverage_cosetHomeomorph (μH : Measure H) [IsMulRightInvariant μH]
    (μH' : Measure H') [IsMulRightInvariant μH']
    (hμ : μH' = μH.map (subgroupEquiv Θ hH)) (f' : G' → ℂ) (q : LeftQuotient H) :
    quotientAverage H' μH' f' (cosetHomeomorph Θ hH q) =
      quotientAverage H μH (f' ∘ Θ) q := by
  subst hμ
  induction q using Quotient.inductionOn with
  | h x =>
    rw [cosetHomeomorph_mk, quotientAverage_mk, quotientAverage_mk]
    rw [show (Measure.map (subgroupEquiv Θ hH) μH) =
        Measure.map (subgroupMeasurableEquiv Θ hH) μH from rfl, integral_map_equiv]
    simp only [Function.comp_apply, map_mul]
    rfl

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace G'] [BorelSpace G'] [MeasurableSpace (LeftQuotient H)]
  [BorelSpace (LeftQuotient H)] [MeasurableSpace (LeftQuotient H')]
  [BorelSpace (LeftQuotient H')] in
theorem quotientAverage_comp_cosetHomeomorph (μH : Measure H) [IsMulRightInvariant μH]
    (μH' : Measure H') [IsMulRightInvariant μH']
    (hμ : μH' = μH.map (subgroupEquiv Θ hH)) (f' : G' → ℂ) :
    quotientAverage H' μH' f' ∘ cosetHomeomorph Θ hH =
      quotientAverage H μH (f' ∘ Θ) :=
  funext (quotientAverage_cosetHomeomorph Θ hH μH μH' hμ f')

/-- Pushforward along the quotient homeomorphism preserves and reflects
compatibility of quotient measures, for the pushed-forward group and subgroup
measures. -/
theorem isCompatible_map_iff (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]
    (μG' : Measure G') (μH' : Measure H') [IsMulRightInvariant μH']
    (hG : μG' = μG.map Θ) (hμ : μH' = μH.map (subgroupEquiv Θ hH))
    (ν : Measure (LeftQuotient H)) :
    IsCompatible H' μG' μH' (ν.map (cosetHomeomorph Θ hH)) ↔
      IsCompatible H μG μH ν := by
  have hQ : (ν.map (cosetHomeomorph Θ hH)) =
      ν.map (leftQuotientMeasurableEquiv Θ hH) := rfl
  have hGm : μG.map Θ = μG.map (groupMeasurableEquiv Θ) := rfl
  -- integral of a test function on `G'`
  have hint : ∀ f' : G' → ℂ, ∫ g, f' g ∂μG' = ∫ g, (f' ∘ Θ) g ∂μG := by
    intro f'
    rw [hG, hGm, integral_map_equiv]
    rfl
  -- test functions correspond
  have htest : ∀ f' : G' → ℂ, (Continuous f' ∧ HasCompactSupport f') ↔
      (Continuous (f' ∘ Θ) ∧ HasCompactSupport (f' ∘ Θ)) := by
    intro f'
    constructor
    · rintro ⟨hc, hs⟩
      exact ⟨hc.comp Θ.continuous, hs.comp_homeomorph Θ.toHomeomorph⟩
    · rintro ⟨hc, hs⟩
      have h1 : f' = (f' ∘ Θ) ∘ Θ.symm := by
        funext x
        simp
      rw [h1]
      exact ⟨hc.comp Θ.symm.continuous, hs.comp_homeomorph Θ.symm.toHomeomorph⟩
  have hsurj : ∀ f : G → ℂ, f = (f ∘ Θ.symm) ∘ Θ := by
    intro f
    funext x
    simp
  constructor
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · intro h0
      apply h.nonzero
      rw [h0, Measure.map_zero]
    · rw [hQ] at h
      have := h.regular
      have h2 := Measure.Regular.map (μ := ν.map (leftQuotientMeasurableEquiv Θ hH))
        (cosetHomeomorph Θ hH).symm
      rwa [show ((ν.map (leftQuotientMeasurableEquiv Θ hH)).map
          (cosetHomeomorph Θ hH).symm) = ν from
        MeasurableEquiv.map_symm_map (leftQuotientMeasurableEquiv Θ hH)] at h2
    · intro g
      have hp := h.right_invariant (Θ g)
      refine ⟨(rightTranslate H g).continuous.measurable, ?_⟩
      have h1 := hp.map_eq
      rw [hQ, map_map hp.measurable (leftQuotientMeasurableEquiv Θ hH).measurable] at h1
      have hc : (rightTranslate H' (Θ g)) ∘ (leftQuotientMeasurableEquiv Θ hH) =
          (leftQuotientMeasurableEquiv Θ hH) ∘ (rightTranslate H g) := by
        funext q
        exact rightTranslate_cosetHomeomorph Θ hH g q
      rw [hc, ← map_map (leftQuotientMeasurableEquiv Θ hH).measurable
        (rightTranslate H g).continuous.measurable] at h1
      exact MeasurableEquiv.map_measurableEquiv_injective _ h1
    · intro f hc hs
      have := h.averaging_integrable (f ∘ Θ.symm) (hc.comp Θ.symm.continuous)
        (hs.comp_homeomorph Θ.symm.toHomeomorph)
      rw [hQ, integrable_map_equiv] at this
      have he : quotientAverage H' μH' (f ∘ Θ.symm) ∘ (leftQuotientMeasurableEquiv Θ hH) =
          quotientAverage H μH f := by
        rw [show (⇑(leftQuotientMeasurableEquiv Θ hH)) = cosetHomeomorph Θ hH from rfl,
          quotientAverage_comp_cosetHomeomorph Θ hH μH μH' hμ, ← hsurj f]
      rwa [he] at this
    · intro f hc hs
      have := h.integral_formula (f ∘ Θ.symm) (hc.comp Θ.symm.continuous)
        (hs.comp_homeomorph Θ.symm.toHomeomorph)
      rw [hQ, integral_map_equiv, hint, ← hsurj f] at this
      have he : ∀ q, quotientAverage H' μH' (f ∘ Θ.symm)
          ((leftQuotientMeasurableEquiv Θ hH) q) = quotientAverage H μH f q := by
        intro q
        rw [show (⇑(leftQuotientMeasurableEquiv Θ hH)) = cosetHomeomorph Θ hH from rfl,
          quotientAverage_cosetHomeomorph Θ hH μH μH' hμ, ← hsurj f]
      simp only [he] at this
      exact this
  · intro h
    refine ⟨?_, ?_, ?_, ?_, ?_⟩
    · rw [hQ, Ne, Measure.map_eq_zero_iff
        (leftQuotientMeasurableEquiv Θ hH).measurable.aemeasurable]
      exact h.nonzero
    · have := h.regular
      exact Measure.Regular.map (cosetHomeomorph Θ hH)
    · intro g'
      obtain ⟨g, rfl⟩ := Θ.surjective g'
      have hp := h.right_invariant g
      refine ⟨(rightTranslate H' (Θ g)).continuous.measurable, ?_⟩
      rw [hQ, map_map (rightTranslate H' (Θ g)).continuous.measurable
        (leftQuotientMeasurableEquiv Θ hH).measurable]
      have hc : (rightTranslate H' (Θ g)) ∘ (leftQuotientMeasurableEquiv Θ hH) =
          (leftQuotientMeasurableEquiv Θ hH) ∘ (rightTranslate H g) := by
        funext q
        exact rightTranslate_cosetHomeomorph Θ hH g q
      rw [hc, ← map_map (leftQuotientMeasurableEquiv Θ hH).measurable
        (rightTranslate H g).continuous.measurable, hp.map_eq]
    · intro f' hc hs
      rw [hQ, integrable_map_equiv]
      have he : quotientAverage H' μH' f' ∘ (leftQuotientMeasurableEquiv Θ hH) =
          quotientAverage H μH (f' ∘ Θ) :=
        quotientAverage_comp_cosetHomeomorph Θ hH μH μH' hμ f'
      rw [he]
      exact h.averaging_integrable _ ((htest f').1 ⟨hc, hs⟩).1 ((htest f').1 ⟨hc, hs⟩).2
    · intro f' hc hs
      rw [hQ, integral_map_equiv, hint]
      have he : ∀ q, quotientAverage H' μH' f' ((leftQuotientMeasurableEquiv Θ hH) q) =
          quotientAverage H μH (f' ∘ Θ) q := by
        intro q
        exact quotientAverage_cosetHomeomorph Θ hH μH μH' hμ f' q
      simp only [he]
      exact h.integral_formula _ ((htest f').1 ⟨hc, hs⟩).1 ((htest f').1 ⟨hc, hs⟩).2

/-- Existence of compatible quotient measures is preserved and reflected. -/
theorem compatibleMeasureExists_iff (μG : Measure G) (μH : Measure H) [IsMulRightInvariant μH]
    (μG' : Measure G') (μH' : Measure H') [IsMulRightInvariant μH']
    (hG : μG' = μG.map Θ) (hμ : μH' = μH.map (subgroupEquiv Θ hH)) :
    CompatibleMeasureExists H' μG' μH' ↔ CompatibleMeasureExists H μG μH := by
  constructor
  · rintro ⟨ν', hν'⟩
    refine ⟨ν'.map (cosetHomeomorph Θ hH).symm, ?_⟩
    rw [← isCompatible_map_iff Θ hH μG μH μG' μH' hG hμ]
    rwa [show (ν'.map (cosetHomeomorph Θ hH).symm).map (cosetHomeomorph Θ hH) =
        ν' from MeasurableEquiv.map_symm_map (leftQuotientMeasurableEquiv Θ hH).symm]
  · rintro ⟨ν, hν⟩
    exact ⟨_, (isCompatible_map_iff Θ hH μG μH μG' μH' hG hμ ν).2 hν⟩

omit [IsTopologicalGroup G] [IsTopologicalGroup G'] [MeasurableSpace G] [BorelSpace G]
  [MeasurableSpace G'] [BorelSpace G'] [MeasurableSpace H] [BorelSpace H] [MeasurableMul H]
  [MeasurableSpace H'] [BorelSpace H'] [MeasurableMul H'] in
/-- Every measure on the target quotient is the pushforward of a measure on the
source quotient. -/
theorem exists_map_eq (ν' : Measure (LeftQuotient H')) :
    ∃ ν : Measure (LeftQuotient H), ν.map (cosetHomeomorph Θ hH) = ν' :=
  ⟨ν'.map (cosetHomeomorph Θ hH).symm,
    MeasurableEquiv.map_symm_map (leftQuotientMeasurableEquiv Θ hH).symm⟩

end Compatible

end Langlands.QuotientIntegration

namespace Langlands.Whittaker

section GroupTransport

variable {R : Type uR} {G : Type uG} {G' : Type uG'} {V : Type uV}
  [CommRing R] [Group G] [Group G'] [AddCommGroup V] [Module R V]
  (Θ : G ≃* G') {N : Subgroup G} {N' : Subgroup G'} (hN : ∀ g, Θ g ∈ N' ↔ g ∈ N)
  {θ : N →* Rˣ} {θ' : N' →* Rˣ} (hθ : ∀ n : N, θ' ⟨Θ n, (hN n).2 n.2⟩ = θ n)

include hθ in
/-- The equivariant functionals of a pulled-back representation are those of the
original representation. -/
theorem functionals_comp (ρ : Representation R G' V) :
    functionals N θ (ρ.comp Θ.toMonoidHom) = functionals N' θ' ρ := by
  ext ℓ
  constructor
  · intro h n' v
    have hn : Θ.symm n' ∈ N := (hN _).1 (by simp)
    have := h ⟨Θ.symm n', hn⟩ v
    have hθn := hθ ⟨Θ.symm n', hn⟩
    simp only [MulEquiv.apply_symm_apply] at hθn
    change ℓ (ρ (Θ (Θ.symm n')) v) = _ at this
    simp only [MulEquiv.apply_symm_apply] at this
    rw [this, ← hθn]
  · intro h n v
    have := h ⟨Θ n, (hN n).2 n.2⟩ v
    change ℓ (ρ (Θ n) v) = (θ n : R) * ℓ v
    rw [this, hθ]

include hθ in
/-- Character-equivariant functions correspond by composition with `Θ⁻¹`. -/
theorem comp_symm_mem_equivariantFunctions {f : G → R}
    (hf : f ∈ (equivariantFunctions N θ).toSubmodule) :
    f ∘ Θ.symm ∈ (equivariantFunctions N' θ').toSubmodule := by
  intro n' g'
  have hn : Θ.symm n' ∈ N := (hN _).1 (by simp)
  have hθn := hθ ⟨Θ.symm n', hn⟩
  simp only [MulEquiv.apply_symm_apply] at hθn
  change f (Θ.symm ((n' : G') * g')) = (θ' n' : R) * f (Θ.symm g')
  rw [map_mul, show θ' n' = θ ⟨Θ.symm n', hn⟩ from hθn]
  exact hf ⟨Θ.symm n', hn⟩ (Θ.symm g')

include hθ in
theorem comp_mem_equivariantFunctions {f : G' → R}
    (hf : f ∈ (equivariantFunctions N' θ').toSubmodule) :
    f ∘ Θ ∈ (equivariantFunctions N θ).toSubmodule := by
  intro n g
  change f (Θ ((n : G) * g)) = (θ n : R) * f (Θ g)
  rw [map_mul, ← hθ n]
  exact hf ⟨Θ n, (hN n).2 n.2⟩ (Θ g)

/-- The linear equivalence of equivariant function spaces, `f ↦ f ∘ Θ⁻¹`. -/
def equivariantEquiv :
    (equivariantFunctions N θ).toSubmodule ≃ₗ[R] (equivariantFunctions N' θ').toSubmodule where
  toFun f := ⟨f.val ∘ Θ.symm, comp_symm_mem_equivariantFunctions Θ hN hθ f.2⟩
  invFun f := ⟨f.val ∘ Θ, comp_mem_equivariantFunctions Θ hN hθ f.2⟩
  left_inv f := Subtype.ext (funext fun g => by simp)
  right_inv f := Subtype.ext (funext fun g => by simp)
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp] theorem equivariantEquiv_apply (f : (equivariantFunctions N θ).toSubmodule) (g : G') :
    (equivariantEquiv Θ hN hθ f).val g = f.val (Θ.symm g) := rfl

@[simp] theorem equivariantEquiv_symm_apply (f : (equivariantFunctions N' θ').toSubmodule)
    (g : G) : ((equivariantEquiv Θ hN hθ).symm f).val g = f.val (Θ g) := rfl

/-- The functional of the original representation underlying a functional of the
pulled-back one. -/
def functionalTransport (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom)) : functionals N' θ' ρ :=
  ⟨ℓ.val, functionals_comp Θ hN hθ ρ ▸ ℓ.2⟩

@[simp] theorem functionalTransport_val (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom)) :
    (functionalTransport Θ hN hθ ρ ℓ).val = ℓ.val := rfl

/-- The inverse correspondence of functionals. -/
def functionalTransportSymm (ρ : Representation R G' V) (ℓ : functionals N' θ' ρ) :
    functionals N θ (ρ.comp Θ.toMonoidHom) :=
  ⟨ℓ.val, (functionals_comp Θ hN hθ ρ).symm ▸ ℓ.2⟩

@[simp] theorem functionalTransportSymm_val (ρ : Representation R G' V)
    (ℓ : functionals N' θ' ρ) : (functionalTransportSymm Θ hN hθ ρ ℓ).val = ℓ.val := rfl

/-- The equivalence of functional spaces. -/
def functionalTransportEquiv (ρ : Representation R G' V) :
    functionals N θ (ρ.comp Θ.toMonoidHom) ≃ functionals N' θ' ρ where
  toFun := functionalTransport Θ hN hθ ρ
  invFun := functionalTransportSymm Θ hN hθ ρ
  left_inv _ := rfl
  right_inv _ := rfl

/-- Coefficient functions correspond under `equivariantEquiv`. -/
theorem equivariantEquiv_coefficientMap (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom)) (v : V) :
    equivariantEquiv Θ hN hθ (coefficientMap (ρ.comp Θ.toMonoidHom) ℓ v) =
      coefficientMap ρ (functionalTransport Θ hN hθ ρ ℓ) v := by
  apply Subtype.ext
  funext g
  change ℓ.val (ρ (Θ (Θ.symm g)) v) = ℓ.val (ρ g v)
  rw [MulEquiv.apply_symm_apply]

/-- Coefficient models correspond under `equivariantEquiv`. -/
theorem mem_coefficientModel_comp_iff (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom)) (f : (equivariantFunctions N θ).toSubmodule) :
    f ∈ (coefficientModel (ρ.comp Θ.toMonoidHom) ℓ).toSubmodule ↔
      equivariantEquiv Θ hN hθ f ∈
        (coefficientModel ρ (functionalTransport Θ hN hθ ρ ℓ)).toSubmodule := by
  constructor
  · rintro ⟨v, rfl⟩
    exact ⟨v, (equivariantEquiv_coefficientMap Θ hN hθ ρ ℓ v).symm⟩
  · rintro ⟨v, hv⟩
    refine ⟨v, ?_⟩
    apply (equivariantEquiv Θ hN hθ).injective
    exact (equivariantEquiv_coefficientMap Θ hN hθ ρ ℓ v).trans hv

/-- The coefficient model of the pulled-back representation is carried onto the
coefficient model of the original representation by `f ↦ f ∘ Θ⁻¹`. -/
def compModelEquiv (ρ : Representation R G' V) (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom)) :
    (coefficientModel (ρ.comp Θ.toMonoidHom) ℓ).toSubmodule ≃
      (coefficientModel ρ (functionalTransport Θ hN hθ ρ ℓ)).toSubmodule where
  toFun f := ⟨equivariantEquiv Θ hN hθ f.val,
    (mem_coefficientModel_comp_iff Θ hN hθ ρ ℓ f.val).1 f.property⟩
  invFun f := ⟨(equivariantEquiv Θ hN hθ).symm f.val,
    (mem_coefficientModel_comp_iff Θ hN hθ ρ ℓ _).2 (by
      rw [LinearEquiv.apply_symm_apply]
      exact f.property)⟩
  left_inv f := Subtype.ext ((equivariantEquiv Θ hN hθ).symm_apply_apply f.val)
  right_inv f := Subtype.ext ((equivariantEquiv Θ hN hθ).apply_symm_apply f.val)

@[simp] theorem compModelEquiv_apply_val (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom))
    (f : (coefficientModel (ρ.comp Θ.toMonoidHom) ℓ).toSubmodule) :
    (compModelEquiv Θ hN hθ ρ ℓ f).val = equivariantEquiv Θ hN hθ f.val := rfl

/-- Values of the transported model function at `Θ g`. -/
theorem compModelEquiv_apply_apply (ρ : Representation R G' V)
    (ℓ : functionals N θ (ρ.comp Θ.toMonoidHom))
    (f : (coefficientModel (ρ.comp Θ.toMonoidHom) ℓ).toSubmodule) (g : G) :
    (compModelEquiv Θ hN hθ ρ ℓ f).val.val (Θ g) = f.val.val g := by
  change f.val.val (Θ.symm (Θ g)) = f.val.val g
  rw [MulEquiv.symm_apply_apply]

end GroupTransport

end Langlands.Whittaker

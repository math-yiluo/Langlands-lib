import Langlands.Global.AdelicRootHyperplaneContinuationStatement
import Langlands.Global.AdelicPositiveChamberStatement
import Langlands.Analysis.Meromorphic.IdentityTheorem
import Langlands.GroupScheme.Rational.RootSupportFiniteness

/-! # Root-hyperplane singularities from one continuation with root-hyperplane singularities

Bernstein–Lapid, Theorem 2.3 (6), number field case, for arbitrary continuation data, from
two premises: the positive chamber is nonempty (`PositiveChamberNonemptyStatement`), and
one continuation of `M(w, λ)φ` and one of `E(φ, λ)` have their singularities along root
hyperplanes (`RootHyperplaneContinuationStatement`).

The proof transfers the cleared form `h = (∏ β, B(λ - λ₀, β))^m · f₂` from the premise's
continuation `f₂` to the given continuation `f₁`. Both agree with `M(w, λ)φ` (resp.
`E(φ, λ)`) on the regular region, which in linear coordinates contains a nonempty open set
because the positive chamber is nonempty and there are finitely many roots. By the identity
theorem for meromorphic functions `f₁ = f₂` where both are holomorphic, and by continuity
`h = (∏ β, B(λ - λ₀, β))^m · f₁` on the whole domain of `f₁`. -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct Filter Set
open scoped CategoryTheory.MonObj TensorProduct Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

/-! ### Transfer of cleared forms -/

section Transfer

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]

/-- A finite linear combination `s ↦ ∑ i, f i s * c i` of meromorphic functions with one
domain `U` is meromorphic with domain `U`, or is zero (when there are no terms). -/
theorem isMeromorphicOn_sum_mul_or_eq_zero {k : ℕ} {f : Fin k → E → ℂ} {U : Set E}
    (hf : ∀ i, IsMeromorphicOn 𝓘(ℂ, E) (f i) U) (c : Fin k → ℂ) :
    IsMeromorphicOn 𝓘(ℂ, E) (fun s => ∑ i, f i s * c i) U ∨
      (fun s => ∑ i, f i s * c i) = 0 := by
  rcases isEmpty_or_nonempty (Fin k) with hk | ⟨⟨i₀⟩⟩
  · right
    funext s
    simp
  · left
    obtain ⟨hUo, hUd, -⟩ := isMeromorphicOn_iff.1 (hf i₀)
    exact isMeromorphicOn_sum Finset.univ hUo hUd (fun i _ => (hf i).mul_const (c i))

/-- **Transfer of a cleared form.** Let each of `f₁` and `f₂` be meromorphic (domains `U₁`
and `U₂`) or zero, and let them agree on a nonempty open set. If `h` is complex
differentiable on an open set `W` and `h = p · f₂` on `W ∩ U₂` for a continuous `p`, then
some function complex differentiable on `W` equals `p · f₁` on `W ∩ U₁`. -/
theorem exists_eq_mul_of_eqOn_isOpen {f₁ f₂ : E → ℂ} {U₁ U₂ : Set E}
    (h₁ : IsMeromorphicOn 𝓘(ℂ, E) f₁ U₁ ∨ f₁ = 0) (h₂ : IsMeromorphicOn 𝓘(ℂ, E) f₂ U₂ ∨ f₂ = 0)
    {V : Set E} (hVo : IsOpen V) (hVne : V.Nonempty) (heq : ∀ s ∈ V, f₁ s = f₂ s)
    {W : Set E} (hWo : IsOpen W) {p h : E → ℂ} (hp : Continuous p)
    (hh : DifferentiableOn ℂ h W) (hph : ∀ s ∈ W, s ∈ U₂ → h s = p s * f₂ s) :
    ∃ h' : E → ℂ, DifferentiableOn ℂ h' W ∧ ∀ s ∈ W, s ∈ U₁ → h' s = p s * f₁ s := by
  rcases h₁ with h₁ | h₁
  · rcases h₂ with h₂ | h₂
    · exact ⟨h, hh, h₁.eq_mul_of_eqOn_isOpen h₂ hVo hVne (fun s hs _ _ => heq s hs) hWo hp
        hh.continuousOn hph⟩
    · have h0 := h₁.eq_of_eqOn_isOpen (isMeromorphicOn_zero_of_isOpen_dense isOpen_univ dense_univ) hVo hVne
        (fun s hs _ _ => by rw [heq s hs, h₂])
      refine ⟨fun _ => 0, differentiableOn_const 0, fun s _ hs => ?_⟩
      rw [h0 s hs (mem_univ s)]
      simp
  · refine ⟨fun _ => 0, differentiableOn_const 0, fun s _ _ => ?_⟩
    simp [h₁]

end Transfer

/-! ### The regular region -/

section Regular

variable {F : Type u} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))} {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M}
  (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [NumberField F] in
/-- Regularity is monotone in the bound. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.IsRegularParameter.mono
    {R R' : ℝ} (hRR : R ≤ R') {lam : ComplexCharacterParameter F P}
    (h : r.IsRegularParameter hA hT R' lam) : r.IsRegularParameter hA hT R lam :=
  fun α hα => hRR.trans_lt (h α hα)

omit [NumberField F] [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left] in
include hT in
/-- There are finitely many roots of `A` in the unipotent radical. -/
theorem _root_.Langlands.GroupScheme.ParabolicRootPresentation.finite_unipotentRoots
    [LocallyOfFiniteType G.X.hom] : r.unipotentRoots.Finite :=
  ((hT.finite_positiveRelativeRoots r.data.i r.data.ν).image
    (fun χ => r.data.f ≫ χ)).subset (by
      rintro α ⟨-, χ, hχ, rfl⟩
      exact ⟨χ, hχ, rfl⟩)

omit [NumberField F] in
/-- If some parameter is `0`-regular, then for every bound `R` and every linear coordinate
system `e` the `R`-regular parameters contain the image under `e` of a nonempty open set. -/
theorem exists_isOpen_isRegularParameter [LocallyOfFiniteType G.X.hom]
    {lam₀ : ComplexCharacterParameter F P} (h₀ : r.IsRegularParameter hA hT 0 lam₀) (R : ℝ)
    {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P) :
    ∃ O : Set (Fin n → ℂ), IsOpen O ∧ O.Nonempty ∧
      ∀ s ∈ O, r.IsRegularParameter hA hT R (e s) := by
  classical
  have hfin := r.finite_unipotentRoots hT
  let L : characterLattice A → (Fin n → ℂ) →ₗ[ℝ] ℝ := fun α =>
    (r.realRootFunctional hA hT α).comp
      ((parameterRealPart F P).comp (e.toLinearMap.restrictScalars ℝ))
  have hL : ∀ α, Continuous (L α) := fun α => LinearMap.continuous_of_finiteDimensional _
  have hLe : ∀ α s, L α s = r.realRootFunctional hA hT α (parameterRealPart F P (e s)) :=
    fun _ _ => rfl
  refine ⟨⋂ α ∈ hfin.toFinset, {s | R < L α s}, ?_, ?_, ?_⟩
  · exact isOpen_biInter_finset (fun α _ => isOpen_lt continuous_const (hL α))
  · have hpos : ∀ α ∈ hfin.toFinset, 0 < L α (e.symm lam₀) := by
      intro α hα
      rw [hLe, e.apply_symm_apply]
      exact h₀ α (hfin.mem_toFinset.1 hα)
    have hev : ∀ᶠ t : ℝ in atTop, ∀ α ∈ hfin.toFinset, R < L α (t • e.symm lam₀) := by
      rw [Filter.eventually_all_finset]
      intro α hα
      have ht : Tendsto (fun t : ℝ => t * L α (e.symm lam₀)) atTop atTop :=
        tendsto_id.atTop_mul_const (hpos α hα)
      filter_upwards [ht.eventually_gt_atTop R] with t htR
      rw [map_smul, smul_eq_mul]
      exact htR
    obtain ⟨t, ht⟩ := hev.exists
    exact ⟨t • e.symm lam₀, mem_iInter₂.2 ht⟩
  · intro s hs α hα
    have := mem_iInter₂.1 hs α (hfin.mem_toFinset.2 hα)
    exact this

end Regular

/-! ### The reduction -/

/-- **Intertwining operators.** `IntertwiningRootHyperplaneStatement` follows from the
nonemptiness of the positive chamber and the existence of one continuation of `M(w, λ)φ`
with singularities along root hyperplanes. -/
theorem intertwiningRootHyperplane_of_continuation
    (hpos : PositiveChamberNonemptyStatement.{u})
    (hI : IntertwiningRootHyperplaneContinuationStatement.{u}) :
    IntertwiningRootHyperplaneStatement.{u} := by
  intro F _ _ G P M U Q M' V A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT q _ iV l' _ π' w c
    hG hU hq hV hl' hiso hπ' hw K hK hK' N d rho hsmooth hcalc φ hKmax hrho hφ
    k ψ coeff D hmero hagree n e s₀
  obtain ⟨k', ψ', coeff', D', hmero', ⟨R', hR'⟩, hroot⟩ :=
    hI F G P M U Q M' V A p iU l a r hA hT q iV l' π' w c hG hU hq hV hl' hiso hπ' hw
      K hK hK' rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R, hR⟩ := hagree
  obtain ⟨lam₀, h₀⟩ := hpos F G P M A p l a r hA hT hG
  obtain ⟨O, hOo, hOne, hOreg⟩ := exists_isOpen_isRegularParameter r hA hT h₀ (max R R') e
  obtain ⟨S, m, W, hS, hWo, hs₀, hW⟩ := hroot n e s₀
  refine ⟨S, m, W, hS, hWo, hs₀, fun g => ?_⟩
  obtain ⟨h, hh, hph⟩ := hW g
  have hp : Continuous
      (fun s : Fin n → ℂ => (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m) := by
    refine (continuous_finsetProd S fun β _ => ?_).pow m
    have hc : Continuous ((r.rootFunctional hA hT β).comp e.toLinearMap) :=
      LinearMap.continuous_of_finiteDimensional _
    have := hc.sub (continuous_const (y := r.rootFunctional hA hT β (e s₀)))
    convert this using 2 with s
    simp [map_sub]
  exact exists_eq_mul_of_eqOn_isOpen
    (isMeromorphicOn_sum_mul_or_eq_zero (fun i => (hmero i).2 n e) (fun i => ψ i g))
    (isMeromorphicOn_sum_mul_or_eq_zero (fun i => (hmero' i).2 n e) (fun i => ψ' i g))
    hOo hOne (fun s hs => by
      have h1 := hR (e s) ((hOreg s hs).mono r hA hT (le_max_left R R')) g
      have h2 := hR' (e s) ((hOreg s hs).mono r hA hT (le_max_right R R')) g
      simp only [Function.comp_apply]
      rw [← h1, ← h2])
    hWo hp hh (fun s hs hs' => hph s hs hs')

/-- **Eisenstein series.** `EisensteinRootHyperplaneStatement` follows from the nonemptiness
of the positive chamber and the existence of one continuation of `E(φ, λ)` with singularities
along root hyperplanes. -/
theorem eisensteinRootHyperplane_of_continuation
    (hpos : PositiveChamberNonemptyStatement.{u})
    (hE : EisensteinRootHyperplaneContinuationStatement.{u}) :
    EisensteinRootHyperplaneStatement.{u} := by
  intro F _ _ G P M U A _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc φ
    hKmax hrho hφ EP DP hmero hagree n e s₀
  obtain ⟨EP', DP', hmero', ⟨R', hR'⟩, hroot⟩ :=
    hE F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ
  obtain ⟨R, hR⟩ := hagree
  obtain ⟨lam₀, h₀⟩ := hpos F G P M A p l a r hA hT hG
  have := hG.smooth
  obtain ⟨O, hOo, hOne, hOreg⟩ := exists_isOpen_isRegularParameter r hA hT h₀ (max R R') e
  obtain ⟨S, m, W, hS, hWo, hs₀, hW⟩ := hroot n e s₀
  refine ⟨S, m, W, hS, hWo, hs₀, fun g => ?_⟩
  obtain ⟨h, hh, hph⟩ := hW g
  have hp : Continuous
      (fun s : Fin n → ℂ => (∏ β ∈ S, r.rootFunctional hA hT β (e s - e s₀)) ^ m) := by
    refine (continuous_finsetProd S fun β _ => ?_).pow m
    have hc : Continuous ((r.rootFunctional hA hT β).comp e.toLinearMap) :=
      LinearMap.continuous_of_finiteDimensional _
    have := hc.sub (continuous_const (y := r.rootFunctional hA hT β (e s₀)))
    convert this using 2 with s
    simp [map_sub]
  exact exists_eq_mul_of_eqOn_isOpen (f₁ := fun s => EP (e s) g) (f₂ := fun s => EP' (e s) g)
    (Or.inl ((hmero g).2 n e)) (Or.inl ((hmero' g).2 n e))
    hOo hOne (fun s hs => by
      have h1 := hR (e s) ((hOreg s hs).mono r hA hT (le_max_left R R'))
      have h2 := hR' (e s) ((hOreg s hs).mono r hA hT (le_max_right R R'))
      rw [h1, h2])
    hWo hp hh (fun s hs hs' => hph s hs hs')

/-- **Reduction of Bernstein–Lapid, Theorem 2.3 (6).** If the positive chamber is nonempty and
one continuation of `M(w, λ)φ` and one of `E(φ, λ)` have their singularities along root
hyperplanes, then every continuation does: `RootHyperplaneSingularitiesStatement`. -/
def RootHyperplaneReductionStatement : Prop :=
  PositiveChamberNonemptyStatement.{u} → RootHyperplaneContinuationStatement.{u} →
    RootHyperplaneSingularitiesStatement.{u}

/-- The reduction holds. -/
theorem rootHyperplaneReduction : RootHyperplaneReductionStatement.{u} :=
  fun hpos hcont => ⟨intertwiningRootHyperplane_of_continuation hpos hcont.1,
    eisensteinRootHyperplane_of_continuation hpos hcont.2⟩

end Langlands.Global

import Langlands.Global.AdelicIntertwiningImaginaryIsometryStatement
import Langlands.Global.AdelicIntertwiningAdjunctionStatement
import Langlands.Global.AdelicIntertwiningCocycleStatement
import Langlands.Global.AdelicIntertwiningIdentity
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.Analysis.Meromorphic.CoordinateGluing
import Langlands.Representation.Plancherel.UnramifiedRationalJacquetGeometryFiniteness

/-! # Reduction of the isometry at imaginary points of holomorphy

Mœglin–Waldspurger IV.3.12, first step: the adjunction of continued intertwining operators,
the functional equation `M(w⁻¹, wλ) M(w, λ) = 1` (from the cocycle relation and `M(1, λ) = 1`)
and the meromorphic continuation of intertwining operators imply
`(M(w, λ)φ, M(w, λ)φ')_{P'} = (φ, φ')_P` at every imaginary point of holomorphy. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set Filter
open scoped CategoryTheory.MonObj TensorProduct Topology

set_option autoImplicit false

/-! ## Finite families of meromorphic functions and the conjugation `s ↦ -s̄` -/

namespace Langlands.Analysis.Meromorphic

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- A family indexed by `Fin k` of functions meromorphic with domain `D` is meromorphic with
domain `⋂ _ : Fin k, D`, which is open and dense in coordinates; for `k = 0` it is the whole
space. -/
theorem isMeromorphicInCoordinatesOn_iInter_fin [FiniteDimensional ℂ X] {k : ℕ} {D : Set X}
    {f : Fin k → X → ℂ} (hf : ∀ i, IsMeromorphicInCoordinatesOn (f i) D) :
    IsOpenDenseInCoordinates (⋂ _ : Fin k, D) ∧
      ∀ i, IsMeromorphicInCoordinatesOn (f i) (⋂ _ : Fin k, D) := by
  rcases k with _ | k
  · rw [iInter_of_empty]
    exact ⟨fun n e => by simp only [preimage_univ]; exact ⟨isOpen_univ, dense_univ⟩,
      fun i => i.elim0⟩
  · rw [iInter_const]
    exact ⟨(hf 0).isOpenDenseInCoordinates, hf⟩

/-- The zero function is meromorphic with any domain that is open and dense in coordinates. -/
theorem isMeromorphicInCoordinatesOn_zero [FiniteDimensional ℂ X] {D : Set X}
    (hD : IsOpenDenseInCoordinates D) :
    IsMeromorphicInCoordinatesOn (fun _ : X => (0 : ℂ)) D :=
  (isMeromorphicInCoordinatesOn_univ (f := fun _ : X => (0 : ℂ))
    fun _ _ => differentiable_const 0).congr_mono hD (subset_univ _) fun _ _ => rfl

/-- The map `s ↦ -s̄` of `ℂⁿ`, as a homeomorphism. -/
def negConjHomeomorph (n : ℕ) : (Fin n → ℂ) ≃ₜ (Fin n → ℂ) where
  toFun s t := -(starRingEnd ℂ) (s t)
  invFun s t := -(starRingEnd ℂ) (s t)
  left_inv s := by funext t; simp
  right_inv s := by funext t; simp
  continuous_toFun := continuous_pi fun t => (Complex.continuous_conj.comp (continuous_apply t)).neg
  continuous_invFun := continuous_pi fun t =>
    (Complex.continuous_conj.comp (continuous_apply t)).neg

theorem negConjHomeomorph_apply {n : ℕ} (s : Fin n → ℂ) :
    negConjHomeomorph n s = fun t => -(starRingEnd ℂ) (s t) := rfl

/-- A continuous function that is constant on a dense set takes that value at every point of
continuity. -/
theorem eq_of_continuousAt_of_dense {n : ℕ} {f : (Fin n → ℂ) → ℂ} {S : Set (Fin n → ℂ)}
    {x : Fin n → ℂ} {c : ℂ} (hS : Dense S) (hf : ContinuousAt f x) (hc : ∀ s ∈ S, f s = c) :
    f x = c := by
  have hx : x ∈ closure S := hS.closure_eq ▸ mem_univ x
  have : (𝓝[S] x).NeBot := mem_closure_iff_nhdsWithin_neBot.mp hx
  have h1 : Tendsto f (𝓝[S] x) (𝓝 (f x)) := hf.tendsto.mono_left nhdsWithin_le_nhds
  have h2 : Tendsto f (𝓝[S] x) (𝓝 c) :=
    tendsto_const_nhds.congr' (eventually_nhdsWithin_of_forall fun s hs => (hc s hs).symm)
  exact tendsto_nhds_unique h1 h2

/-- A function meromorphic in coordinates is continuous, in every chart, at every point of its
domain of holomorphy. -/
theorem IsMeromorphicInCoordinatesOn.continuousAt_comp {f : X → ℂ} {D : Set X}
    (hf : IsMeromorphicInCoordinatesOn f D) {n : ℕ} (e : (Fin n → ℂ) ≃ₗ[ℂ] X)
    {s : Fin n → ℂ} (hs : e s ∈ D) : ContinuousAt (f ∘ e) s := by
  obtain ⟨hUo, -, hhol, -⟩ := hf.2 n e
  exact (differentiableOn_of_isHolomorphicOn hhol).continuousOn.continuousAt (hUo.mem_nhds hs)

end Langlands.Analysis.Meromorphic

/-! ## Combining finitely many finite expansions into one -/

namespace Langlands.Global

open Langlands.Analysis.Meromorphic

section Combine

variable {α Y : Type*} {m : ℕ} (k : Fin m → ℕ) (χ : ∀ i, Fin (k i) → α → ℂ)
  (b : ∀ i, Fin (k i) → Y → ℂ)

/-- The concatenation `Fin (∑ i, k i)` of the families `χ i`. -/
def combinedFamily : Fin (∑ i, k i) → α → ℂ := fun x =>
  χ (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2

/-- The coefficients of the family `i` in the concatenation, padded with zeros. -/
def combinedCoeff : Fin m → Fin (∑ i, k i) → Y → ℂ := fun i x y =>
  if (finSigmaFinEquiv.symm x).1 = i then
    b (finSigmaFinEquiv.symm x).1 (finSigmaFinEquiv.symm x).2 y else 0

theorem sum_combinedCoeff_mul (i : Fin m) (y : Y) (g : α) :
    ∑ x, combinedCoeff k b i x y * combinedFamily k χ x g = ∑ t, b i t y * χ i t g := by
  classical
  rw [← finSigmaFinEquiv.sum_comp, Fintype.sum_sigma, Finset.sum_eq_single i]
  · refine Finset.sum_congr rfl fun t _ => ?_
    simp only [combinedCoeff, combinedFamily]
    rw [Equiv.symm_apply_apply]
    simp
  · intro i' _ hi'
    simp [combinedCoeff, hi']
  · intro h
    exact absurd (Finset.mem_univ i) h

end Combine

/-! ## Finite sesquilinear expansion of `(·,·)_P` -/

section Sesquilinear

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]

private theorem mul_sum_mul_conj_sum {a b : ℕ} (C : ℂ) (x u : Fin a → ℂ) (y v : Fin b → ℂ) :
    C * (∑ i, x i * u i) * (starRingEnd ℂ) (∑ j, y j * v j) =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (y j) * (C * u i * (starRingEnd ℂ) (v j)) := by
  have h1 : C * (∑ i, x i * u i) = ∑ i, C * (x i * u i) := Finset.mul_sum _ _ _
  rw [h1, map_sum, Finset.sum_mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul]
  ring

omit [LocallyOfFiniteType G.X.hom] in
/-- `(·,·)_P` is sesquilinear on finite combinations whose pairwise integrands are integrable. -/
theorem inducedInnerProduct_sum_sum (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) (p : P ⟶ G) (l : M ⟶ P)
    (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure] {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ) {a b : ℕ}
    (f : Fin a → AdelicGroupPoints F G → ℂ) (h : Fin b → AdelicGroupPoints F G → ℂ)
    (x : Fin a → ℂ) (y : Fin b → ℂ)
    (hint : ∀ i j, Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (f i) (h j))
      ((compactHaarProbability F G K hKc).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
          (isDiscrete_rationalSubgroup F M) μM))) :
    inducedInnerProduct K hKc p l μM e β (fun g => ∑ i, x i * f i g)
        (fun g => ∑ j, y j * h j g) =
      ∑ i, ∑ j, x i * (starRingEnd ℂ) (y j) * inducedInnerProduct K hKc p l μM e β (f i) (h j) := by
  set κ := compactHaarProbability F G K hKc
  set ν := LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
    (isDiscrete_rationalSubgroup F M) μM with hν
  have : SFinite ν := by
    rw [hν, LeftCosetSpace.discreteQuotientMeasure, LeftCosetSpace.quotientMeasure]
    infer_instance
  have hpt : ∀ z : K × RationalQuotient F M,
      AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (fun g => ∑ i, x i * f i g)
      (fun g => ∑ j, y j * h j g) z = ∑ i, ∑ j, x i * (starRingEnd ℂ) (y j) *
        AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (f i) (h j) z := by
    intro z
    exact mul_sum_mul_conj_sum _ _ _ _ _
  have hterm : ∀ i j, Integrable (fun z => x i * (starRingEnd ℂ) (y j) *
      AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (f i) (h j) z) (κ.prod ν) :=
    fun i j => (hint i j).const_mul _
  have hcomb : Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (fun g => ∑ i, x i * f i g)
      (fun g => ∑ j, y j * h j g)) (κ.prod ν) :=
    (integrable_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j).congr
      (Eventually.of_forall fun z => (hpt z).symm)
  have hII : ∀ φ ψ : AdelicGroupPoints F G → ℂ,
      Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ) (κ.prod ν) →
        inducedInnerProduct K hKc p l μM e β φ ψ =
          ∫ z, AdelicGroupPoints.inducedInnerProductIntegrand K p l e β φ ψ z ∂(κ.prod ν) := by
    intro φ ψ hi
    rw [integral_prod _ hi]
    rfl
  rw [hII _ _ hcomb, integral_congr_ae (Eventually.of_forall hpt),
    integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hterm i j]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [integral_finsetSum _ fun j _ => hterm i j]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [integral_const_mul, hII _ _ (hint i j)]

end Sesquilinear

/-! ## The inverse Weyl conjugation -/

section WeylInverse

open Langlands.GroupScheme

variable {F : Type} [Field F] {G P M Q M' : GroupScheme (Spec (CommRingCat.of F))}

/-- If `(w, c)` presents an element of `W(P, Q)`, then `(w⁻¹, c⁻¹)` presents its inverse in
`W(Q, P)`. -/
theorem AdelicGroupPoints.IsWeylConjugation.inv {p : P ⟶ G} {l : M ⟶ P} {q : Q ⟶ G} {l' : M' ⟶ Q}
    {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {c : M' ⟶ M}
    (hw : AdelicGroupPoints.IsWeylConjugation p l q l' w c) [IsIso c] :
    AdelicGroupPoints.IsWeylConjugation q l' p l w⁻¹ (inv c) := by
  refine ⟨inferInstance, ?_⟩
  have h1 : (G.innerIso w⁻¹).inv = (G.innerIso w).hom :=
    Iso.inv_ext (by rw [innerIso_inv_hom, Iso.inv_hom_id])
  rw [h1, IsIso.inv_comp_eq, reassoc_of% hw.comp_eq, Iso.inv_hom_id, Category.comp_id]

end WeylInverse

/-! ## The reduction -/

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints

/-- The reduction of the isometry at imaginary points of holomorphy (Mœglin–Waldspurger IV.3.12,
first step) as a proposition: the adjunction of continued intertwining operators, the cocycle
relation and the meromorphic continuation of intertwining operators imply it. -/
def IntertwiningImaginaryIsometryReductionStatement : Prop :=
  IntertwiningContinuedAdjunctionStatement → IntertwiningCocycleStatement.{0} →
    IntertwiningMeromorphicContinuationStatement.{0} → IntertwiningImaginaryIsometryStatement

/-- **Isometry of `M(w, λ)` at imaginary points of holomorphy from the adjunction, the cocycle
relation and the meromorphic continuation** (Mœglin–Waldspurger IV.3.12). -/
theorem intertwiningImaginaryIsometry_of_inputs
    (hAdj : IntertwiningContinuedAdjunctionStatement)
    (hCoc : IntertwiningCocycleStatement.{0})
    (hCont : IntertwiningMeromorphicContinuationStatement.{0}) :
    IntertwiningImaginaryIsometryStatement := by
  intro F _ _ G P M U P' M' U' A _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT p' _ iU' l' _
    π' w cw hGred hiU hp' hiU' hl' hmul hπ' hW K hK hK' N d rho hsmooth hcalc hKmax hrho
    μM _ μM' _ hμM hμM' n e e' hee' β β' hβc hβs hβ1 hβ'c hβ's hβ'1 k m v ψ coeff DM hv hψ
    hcoeff hexp coeff' DM' hcoeff' hagree mu j j' hmu
  classical
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  -- The parabolic `P`: Levi decomposition for the given radical and a Levi retraction.
  have : Smooth G.X.hom := hGred.smooth
  have hl : IsRationalLeviSubgroup l := r.isCompatible.levi
  have hp : IsParabolicSubgroup p := r.isCompatible.parabolic
  have hmulP : IsIso (subgroupMultiplication l iU) := r.isIso_subgroupMultiplication_of_radical hiU
  set π : P ⟶ M := leviRetraction l iU hiU.1.isNormal with hπdef
  have hπ : l ≫ π = 𝟙 M := levi_comp_leviRetraction l iU hiU.1.isNormal
  -- The inverse Weyl element.
  have : IsIso cw := hW.isIso
  have hW' : IsWeylConjugation p' l' p l w⁻¹ (inv cw) := hW.inv
  -- A root presentation of `P'` with split component `A`.
  obtain ⟨a₁, ha₁⟩ : ∃ a₁ : A.toGrp ⟶ M', IsSplitComponent a₁ :=
    ⟨_, r.isCompatible.splitComponent.comp_iso (asIso cw).symm⟩
  obtain ⟨r₁⟩ := parabolicRootPresentationExistence F G hGred P' M' A p' l' a₁ hp' hl' ha₁
  have : Mono r₁.data.i.hom.hom.left := r₁.isCompatible.maximalSplit.isSplitSubtorus.mono
  have : Fintype (relativeWeylGroup r₁.data.i) :=
    @Fintype.ofFinite _ (hGred.finite_relativeWeylGroup r₁.data.i r₁.isCompatible.maximalSplit)
  have : Mono (CommGroupScheme.groupHom r₁.data.f).hom.hom.left := by
    have := r₁.isCompatible.splitComponent.1.isSplitSubtorus.mono
    have := r₁.isCompatible.levi.isClosedSubgroup.mono
    have := r₁.isCompatible.parabolic.isClosedSubgroup.mono
    have : Mono (a₁ ≫ l' ≫ p').hom.hom.left := by
      change Mono (a₁.hom.hom.left ≫ l'.hom.hom.left ≫ p'.hom.hom.left)
      infer_instance
    exact mono_of_mono_fac (congrArg (fun z => z.hom.hom.left) r₁.isCompatible.factor_comp)
  have hT₁ : IsSplitTorus r₁.data.T.toGrp := r₁.isCompatible.maximalSplit.isSplitSubtorus.1
  -- Linear coordinates.
  obtain ⟨We, hWe⟩ := AdelicGroupPoints.exists_weylParameter_linearEquiv l l' hl hl' cw π' hπ'
  have hWapp : ∀ x, We x = weylParameter l cw π' x := fun x => LinearMap.congr_fun hWe x
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    LinearEquiv.finiteDimensional (realChart e)
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P') :=
    LinearEquiv.finiteDimensional We
  -- Reverse expansions `M(w⁻¹, ν)(ψ j' i) = ∑ t, b i t ν • χ i t`, combined into one family.
  have hrevex : ∀ i : Fin m, ∃ (kk : ℕ) (χ : Fin kk → AdelicGroupPoints F G → ℂ)
      (b : Fin kk → ComplexCharacterParameter F P' → ℂ)
      (E : Set (ComplexCharacterParameter F P')),
      (∀ t, IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
        (K.comap (ofInfinite F G).toMonoidHom) rho (χ t)) ∧
      (∀ t, IsMeromorphicInCoordinatesOn (b t) E) ∧
      ∃ R₀ : ℝ, ∀ nu, r₁.IsRegularParameter hA hT₁ R₀ nu → ∀ g,
        hK'.intertwiningOperator hK iU' l' iU (inv cw) π w⁻¹ (ψ j' i) nu g =
          ∑ t, b t nu * χ t g :=
    fun i => hCont F G P' M' U' P M U A p' iU' l' a₁ r₁ hA hT₁ p iU l π w⁻¹ (inv cw) hGred
      hiU' hp hiU hl hmulP hπ hW' K hK' hK rho hsmooth hcalc (ψ j' i) hKmax hrho (hψ j' i).1
  choose kk χ b E hχ hb hR using hrevex
  set Ec : Set (ComplexCharacterParameter F P') := ⋂ i, ⋂ _ : Fin (kk i), E i with hEc
  have hEc_od : IsOpenDenseInCoordinates Ec :=
    isOpenDenseInCoordinates_iInter fun i => (isMeromorphicInCoordinatesOn_iInter_fin (hb i)).1
  set χc := combinedFamily kk χ with hχc
  set bc := combinedCoeff kk b with hbc
  have hχc_aut : ∀ x, IsAutomorphicFunctionOn F G hsmooth hcalc
      (parabolicQuotientSubgroup F p iU l) (K.comap (ofInfinite F G).toMonoidHom) rho (χc x) :=
    fun x => hχ _ _
  have hbc_mero : ∀ i x, IsMeromorphicInCoordinatesOn (bc i x) Ec := by
    intro i x
    by_cases hc : (finSigmaFinEquiv.symm x).1 = i
    · have h := ((isMeromorphicInCoordinatesOn_iInter_fin
        (hb (finSigmaFinEquiv.symm x).1)).2 (finSigmaFinEquiv.symm x).2).congr_mono hEc_od
        (iInter_subset (fun i => ⋂ _ : Fin (kk i), E i) _) (fun _ _ => rfl)
      convert h using 1
      funext y
      simp [hbc, combinedCoeff, hc]
    · convert isMeromorphicInCoordinatesOn_zero hEc_od using 1
      funext y
      simp [hbc, combinedCoeff, hc]
  have hrevc : ∀ i, ∃ R : ℝ, ∀ nu, r₁.IsRegularParameter hA hT₁ R nu → ∀ g,
      hK'.intertwiningOperator hK iU' l' iU (inv cw) π w⁻¹ (ψ j' i) nu g =
        ∑ x, bc i x nu * χc x g := by
    intro i
    obtain ⟨R₀, hR₀⟩ := hR i
    exact ⟨R₀, fun nu hnu g => by rw [hR₀ nu hnu g, hbc, hχc, sum_combinedCoeff_mul]⟩
  -- Forward domains, with empty families allowed.
  set DMt : Set (ComplexCharacterParameter F P) := ⋂ _ : Fin m, DM with hDMt
  set DMt' : Set (ComplexCharacterParameter F P) := ⋂ _ : Fin m, DM' with hDMt'
  have hDMtm := fun j₀ => isMeromorphicInCoordinatesOn_iInter_fin (hcoeff j₀)
  have hDMtm' := fun j₀ => isMeromorphicInCoordinatesOn_iInter_fin (hcoeff' j₀)
  have hagree' : ∀ j₀, ∀ lam ∈ DMt ∩ DMt', ∀ g,
      ∑ i, coeff' j₀ i lam * ψ j₀ i g = ∑ i, coeff j₀ i lam * ψ j₀ i g := by
    intro j₀ lam hlam g
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simp
    · have : Nonempty (Fin m) := ⟨⟨0, hm⟩⟩
      rw [hDMt, hDMt', iInter_const, iInter_const] at hlam
      exact hagree j₀ lam hlam g
  -- The functional equation `M(w⁻¹, wμ) M(w, μ)(v j') = v j'`, from the cocycle relation.
  have hinvU : IsLeftInvariantUnder F G (parabolicUnipotentImage F p iU) (v j') :=
    fun x hx g => (hv j').1.1 x (Subgroup.mem_sup_left hx) g
  have hconst1 : IsMeromorphicInCoordinatesOn
      (fun _ : ComplexCharacterParameter F P => (1 : ℂ)) univ :=
    isMeromorphicInCoordinatesOn_univ fun _ _ => differentiable_const 1
  have hid : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK iU l iU (inv cw ≫ cw) π (w⁻¹ * w) (v j') lam g =
        ∑ t : Fin 1, (fun (_ : Fin 1) (_ : ComplexCharacterParameter F P) => (1 : ℂ)) t lam *
          (fun _ : Fin 1 => v j') t g := by
    refine ⟨0, fun lam _ g => ?_⟩
    rw [inv_mul_cancel, IsIso.inv_hom_id,
      hK.intertwiningOperator_one_self iU r π hπ hiU (v j') hinvU lam g]
    simp
  have hFE : ∀ lam ∈ DMt, weylParameter l cw π' lam ∈ Ec → ∀ g,
      ∑ i, coeff j' i lam * ∑ x, bc i x (weylParameter l cw π' lam) * χc x g = v j' g := by
    intro lam hlam hWlam g
    have h := hCoc F G P M U P' M' U' P M U A A p iU l a r hA hT p' iU' l' a₁ r₁ hA hT₁ π'
      p iU l π w w⁻¹ cw (inv cw) hGred hiU hiU' hp hiU hl hmulP hπ' hπ hW hW' K hK hK' hK rho
      hsmooth hcalc (v j') hKmax hrho (hv j').1 m (ψ j') (coeff j') DMt
      (fun i => (hψ j' i).1) (hDMtm j').2 (hexp j') (∑ i, kk i) χc bc Ec hbc_mero hrevc
      1 (fun _ => v j') (fun _ _ => 1) univ (fun _ => hconst1) hid lam ⟨hlam, mem_univ _⟩
      hWlam g
    simpa using h.symm
  -- The adjunction.
  obtain ⟨S₀, hS₀o, hS₀d, hS₀⟩ := hAdj F G P M U P' M' U' A A p iU l a r hA hT π p' iU' l' a₁
    r₁ hA hT₁ π' w cw (inv cw) hGred hiU hiU' hπ hπ' hW hW' K hK hK' rho hsmooth hcalc hKmax
    hrho μM μM' hμM hμM' e e' hee' β β' hβc hβs hβ1 hβ'c hβ's hβ'1 (v j) m (ψ j) (coeff j) DMt
    (hv j) (hψ j) (hDMtm j).2 (hexp j) m (ψ j') (∑ i, kk i) χc bc Ec (hψ j') hχc_aut hbc_mero
    hrevc
  -- An open dense set of parameters where every identity holds.
  have hinter : ∀ {T T' : Set (Fin n → ℂ)}, IsOpen T ∧ Dense T → IsOpen T' ∧ Dense T' →
      IsOpen (T ∩ T') ∧ Dense (T ∩ T') :=
    fun h h' => ⟨h.1.inter h'.1, h.2.inter_of_isOpen_left h'.2 h.1⟩
  have hρod : ∀ {T : Set (Fin n → ℂ)}, IsOpen T ∧ Dense T →
      IsOpen (negConjHomeomorph n ⁻¹' T) ∧ Dense (negConjHomeomorph n ⁻¹' T) :=
    fun h => ⟨h.1.preimage (negConjHomeomorph n).continuous,
      h.2.preimage (negConjHomeomorph n).isOpenMap⟩
  have hA1 : IsOpen (realChart e ⁻¹' (DMt ∩ DMt')) ∧ Dense (realChart e ⁻¹' (DMt ∩ DMt')) :=
    ((hDMtm j).1.inter (hDMtm' j).1) n (realChart e)
  have hA3 : IsOpen ((realChart e).trans We ⁻¹' Ec) ∧ Dense ((realChart e).trans We ⁻¹' Ec) :=
    hEc_od n ((realChart e).trans We)
  set S : Set (Fin n → ℂ) := realChart e ⁻¹' (DMt ∩ DMt') ∩
    negConjHomeomorph n ⁻¹' (realChart e ⁻¹' (DMt ∩ DMt')) ∩
    negConjHomeomorph n ⁻¹' ((realChart e).trans We ⁻¹' Ec) ∩ S₀ with hS
  have hSd : Dense S := (hinter (hinter (hinter hA1 (hρod hA1)) (hρod hA3)) ⟨hS₀o, hS₀d⟩).2
  -- The Gram function `s ↦ (M(w, λ)(v j), M(w, -λ̄)(v j'))_{P'}` in the chart, `λ = realChart e s`.
  set Gf : (Fin n → ℂ) → ℂ := fun s => ∑ i, ∑ i', coeff' j i (realChart e s) *
    (starRingEnd ℂ) (coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) *
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ j i) (ψ j' i') with hGf
  have hint' : ∀ i i', Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p' l' e' β' (ψ j i) (ψ j' i'))
      ((compactHaarProbability F G K hK'.isCompact).prod
        (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M')
          (isDiscrete_rationalSubgroup F M') μM')) :=
    fun i i' => InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand e'
      hl'.isConnectedReductive ha₁ hA hπ' μM' hβ'c hβ's (hψ j i) (hψ j' i')
  have hval : ∀ s ∈ S, Gf s = inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') := by
    rintro s ⟨⟨⟨hs1, hs2⟩, hs3⟩, hs0⟩
    have hν : weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))) ∈ Ec := by
      rw [← hWapp]
      exact hs3
    have hF : (fun g => ∑ i, coeff' j i (realChart e s) * ψ j i g) =
        fun g => ∑ i, coeff j i (realChart e s) * ψ j i g :=
      funext fun g => hagree' j _ hs1 g
    have hF' : (fun g => ∑ i', coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
        ψ j' i' g) = fun g => ∑ i', coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
          ψ j' i' g :=
      funext fun g => hagree' j' _ hs2 g
    have hV : (fun g => ∑ x, (∑ i', coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
        bc i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
          χc x g) = v j' := by
      funext g
      rw [← hFE (realChart e (fun t => -(starRingEnd ℂ) (s t))) hs2.1 hν g]
      simp only [Finset.sum_mul, Finset.mul_sum, mul_assoc]
      exact Finset.sum_comm
    have hintR : Integrable (AdelicGroupPoints.inducedInnerProductIntegrand K p l e β (v j)
        (fun g => ∑ x, (∑ i', coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
          bc i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
            χc x g))
        ((compactHaarProbability F G K hK.isCompact).prod
          (LeftCosetSpace.discreteQuotientMeasure (rationalSubgroup F M)
            (isDiscrete_rationalSubgroup F M) μM)) := by
      rw [hV]
      exact InducedInnerProductIntegrable.integrable_inducedInnerProduct_integrand e
        hl.isConnectedReductive r.isCompatible.splitComponent hA hπ μM hβc hβs (hv j) (hv j')
    calc Gf s = ∑ i, ∑ i', coeff' j i (realChart e s) *
          (starRingEnd ℂ) (coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) *
            inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ j i) (ψ j' i') := rfl
      _ = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
            (fun g => ∑ i, coeff' j i (realChart e s) * ψ j i g)
            (fun g => ∑ i', coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
              ψ j' i' g) :=
          (inducedInnerProduct_sum_sum K hK'.isCompact p' l' μM' e' β' (ψ j) (ψ j')
            (fun i => coeff' j i (realChart e s))
            (fun i' => coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) hint').symm
      _ = inducedInnerProduct K hK'.isCompact p' l' μM' e' β'
            (fun g => ∑ i, coeff j i (realChart e s) * ψ j i g)
            (fun g => ∑ i', coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
              ψ j' i' g) := by rw [hF, hF']
      _ = inducedInnerProduct K hK.isCompact p l μM e β (v j)
            (fun g => ∑ x, (∑ i', coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t))) *
              bc i' x (weylParameter l cw π' (realChart e (fun t => -(starRingEnd ℂ) (s t))))) *
                χc x g) :=
          hS₀ s hs0 hs1.1 hν (fun i' => coeff j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) hintR
      _ = inducedInnerProduct K hK.isCompact p l μM e β (v j) (v j') := by rw [hV]
  -- Continuity at the imaginary point and conclusion.
  set s₀ : Fin n → ℂ := (realChart e).symm (imaginaryParameter F P mu) with hs₀
  have hlam₀ : realChart e s₀ = imaginaryParameter F P mu := LinearEquiv.apply_symm_apply _ _
  have hρs₀ : (fun t => -(starRingEnd ℂ) (s₀ t)) = s₀ := by
    funext t
    have hre := realChart_symm_imaginary_re e mu t
    rw [← hs₀] at hre
    apply Complex.ext <;> simp [hre]
  have hc1 : ∀ i, ContinuousAt (fun s => coeff' j i (realChart e s)) s₀ := fun i =>
    (hcoeff' j i).continuousAt_comp (realChart e) (by rw [hlam₀]; exact hmu)
  have hc2 : ∀ i', ContinuousAt
      (fun s => coeff' j' i' (realChart e (fun t => -(starRingEnd ℂ) (s t)))) s₀ := fun i' =>
    ((hcoeff' j' i').continuousAt_comp (realChart e) (by rw [hlam₀]; exact hmu)).comp_of_eq
      (negConjHomeomorph n).continuous.continuousAt hρs₀
  have hcont : ContinuousAt Gf s₀ :=
    tendsto_finsetSum _ fun i _ => tendsto_finsetSum _ fun i' _ =>
      ((hc1 i).mul (Complex.continuous_conj.continuousAt.comp (hc2 i'))).mul continuousAt_const
  have hfinal := eq_of_continuousAt_of_dense hSd hcont hval
  simp only [hGf, hρs₀, hlam₀] at hfinal
  exact hfinal

/-- The reduction, in the form of the proposition
`IntertwiningImaginaryIsometryReductionStatement`. -/
theorem intertwiningImaginaryIsometryReduction : IntertwiningImaginaryIsometryReductionStatement :=
  fun hAdj hCoc hCont => intertwiningImaginaryIsometry_of_inputs hAdj hCoc hCont

end Langlands.Global

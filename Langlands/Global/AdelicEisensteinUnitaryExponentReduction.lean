import Langlands.Global.AdelicEisensteinConstantTermExponentLabelsStatement
import Langlands.Global.AdelicEisensteinImaginaryJointContinuityReduction
import Langlands.Global.AdelicWavePacketRationalInvariance
import Langlands.Analysis.SeveralComplex.ParametricIntegral
import Langlands.Analysis.Meromorphic.IdentityTheorem

/-! # Subunitary exponents at unitary parameters from the regular exponent labels

`EisensteinUnitaryExponentStatement` follows from the root-hyperplane form of the continued
Eisenstein series (`EisensteinJointRootHyperplaneStatement`) and the exponent labels of the
constant terms at regular parameters (`EisensteinConstantTermExponentLabelsStatement`). -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Polynomial Set Filter Topology
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

namespace UnitaryExponent

/-! ### Meromorphy in coordinates -/

section Coordinates

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- The product of an entire function and a function meromorphic in coordinates is meromorphic
in coordinates with the same domain. -/
theorem isMeromorphicInCoordinatesOn_mul_entire {c f : X → ℂ} {D : Set X}
    (hc : ∀ (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] X), Differentiable ℂ (c ∘ e))
    (hf : IsMeromorphicInCoordinatesOn f D) :
    IsMeromorphicInCoordinatesOn (fun x => c x * f x) D := by
  refine ⟨hf.1, fun n e => ?_⟩
  have h := hf.2 n e
  rw [isMeromorphicOn_iff] at h ⊢
  obtain ⟨hUo, hUd, hd, hloc⟩ := h
  refine ⟨hUo, hUd, (hc n e).differentiableOn.mul hd, fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hs, g, k, hg, hne, hk, he⟩ := hloc s₀
  refine ⟨W, hWo, hWc, hs, g, fun s => c (e s) * k s, hg, hne,
    (hc n e).differentiableOn.mul hk, fun s hs' => ?_⟩
  change g s * (c (e s) * f (e s)) = c (e s) * k s
  rw [← he s hs']
  change g s * (c (e s) * f (e s)) = c (e s) * (g s * f (e s))
  ring

/-- A finite sum of functions meromorphic in coordinates with one domain is meromorphic in
coordinates with that domain. -/
theorem isMeromorphicInCoordinatesOn_finsetSum [FiniteDimensional ℂ X] {Idx : Type*}
    (t : Finset Idx) {f : Idx → X → ℂ} {D : Set X} (hD : IsOpenDenseInCoordinates D)
    (hf : ∀ i ∈ t, IsMeromorphicInCoordinatesOn (f i) D) :
    IsMeromorphicInCoordinatesOn (fun x => ∑ i ∈ t, f i x) D :=
  ⟨inferInstance, fun n e =>
    isMeromorphicOn_sum (E := Fin n → ℂ) t (hD n e).1 (hD n e).2
      fun i hi => (hf i hi).2 n e⟩

/-- The zero function is meromorphic in coordinates with any domain that is open and dense in
coordinates. -/
theorem isMeromorphicInCoordinatesOn_const_zero [FiniteDimensional ℂ X] {D : Set X}
    (hD : IsOpenDenseInCoordinates D) :
    IsMeromorphicInCoordinatesOn (fun _ : X => (0 : ℂ)) D :=
  (isMeromorphicInCoordinatesOn_univ (f := fun _ : X => (0 : ℂ))
    fun _ _ => differentiable_const 0).congr_mono hD (subset_univ _) fun _ _ => rfl

end Coordinates

/-! ### Coefficients of root polynomials -/

/-- The coefficients of `∏_{i ∈ I} (X - r_i(s))` are entire in `s` when the roots are. -/
theorem differentiable_translationRootPolynomial_coeff {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] {Idx : Type*} (I : Finset Idx) (r : Idx → E → ℂ)
    (hr : ∀ i ∈ I, Differentiable ℂ (r i)) (k : ℕ) :
    Differentiable ℂ fun s => (translationRootPolynomial I fun i => r i s).coeff k := by
  classical
  induction I using Finset.induction_on generalizing k with
  | empty =>
    simp only [translationRootPolynomial, Finset.prod_empty]
    exact differentiable_const _
  | @insert b I hb ih =>
    have hb' := hr b (Finset.mem_insert_self b I)
    have hI := ih fun i hi => hr i (Finset.mem_insert_of_mem hi)
    simp only [translationRootPolynomial, Finset.prod_insert hb, mul_comm (X - C (r b _))]
    cases k with
    | zero =>
      simp only [mul_coeff_zero, coeff_sub, coeff_X_zero, coeff_C_zero, zero_sub]
      exact (hI 0).mul hb'.neg
    | succ k =>
      simp only [coeff_mul_X_sub_C]
      exact (hI k).sub ((hI (k + 1)).mul hb')

/-- A finite product of entire functions is entire. -/
theorem differentiable_finsetProd_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {Idx : Type*} (S : Finset Idx) (f : Idx → E → ℂ) (hf : ∀ i ∈ S, Differentiable ℂ (f i)) :
    Differentiable ℂ fun s => ∏ i ∈ S, f i s := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    simp only [Finset.prod_empty]
    exact differentiable_const _
  | @insert b S hb ih =>
    simp only [Finset.prod_insert hb]
    exact (hf b (Finset.mem_insert_self b S)).mul
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/-- A multiple of an annihilating polynomial annihilates. -/
theorem isTranslationPolynomialSolution_mul_right {F : Type} [Field F] [NumberField F]
    {G : GroupScheme (Spec (CommRingCat.of F))} {x : AdelicGroupPoints F G} {Q : Polynomial ℂ}
    {φ : AdelicGroupPoints F G → ℂ} (h : IsTranslationPolynomialSolution x Q φ)
    (Q' : Polynomial ℂ) : IsTranslationPolynomialSolution x (Q * Q') φ := by
  rw [isTranslationPolynomialSolution_iff_aeval] at h ⊢
  rw [mul_comm, map_mul, Module.End.mul_apply, h, map_zero]

/-! ### Continuation of difference equations -/

section Continuation

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom]
  {p : P ⟶ G} {l : M ⟶ P} {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- **Continuation of a difference equation.** Let `Ψ λ` be functions on `G(𝔸)` whose values
`λ ↦ Ψ λ g` are meromorphic in coordinates with one domain `D`, and let `ρ_k` be entire
functions of `λ`. If `∏_k (L_x - ρ_k(λ))` annihilates `Ψ λ` for every sufficiently regular `λ`,
it annihilates `Ψ λ` for every `λ ∈ D`. -/
theorem isTranslationPolynomialSolution_of_regular (hG : IsConnectedReductive G) {m : ℕ}
    (Ψ : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ)
    {D : Set (ComplexCharacterParameter F P)}
    (hΨ : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => Ψ lam g) D)
    (ρ : Fin m → ComplexCharacterParameter F P → ℂ)
    (hρ : ∀ k (n : ℕ) (e : (Fin n → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
      Differentiable ℂ (ρ k ∘ e))
    (x : AdelicGroupPoints F G) (R : ℝ)
    (hreg : ∀ lam, r.IsRegularParameter hA hT R lam →
      IsTranslationPolynomialSolution x (∏ k, (X - C (ρ k lam))) (Ψ lam))
    {lam : ComplexCharacterParameter F P} (hlam : lam ∈ D) :
    IsTranslationPolynomialSolution x (∏ k, (X - C (ρ k lam))) (Ψ lam) := by
  have hdeg : ∀ lam' : ComplexCharacterParameter F P,
      (∏ k, (X - C (ρ k lam'))).natDegree = m := fun lam' => by
    have h := translationRootPolynomial_natDegree (Finset.univ : Finset (Fin m))
      fun k => ρ k lam'
    rw [Finset.card_univ, Fintype.card_fin] at h
    exact h
  intro g
  have hD := (hΨ g).isOpenDenseInCoordinates
  have : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hΨ g).1
  let Φ : ComplexCharacterParameter F P → ℂ := fun lam' =>
    ∑ k ∈ Finset.range (m + 1), (∏ j, (X - C (ρ j lam'))).coeff k * Ψ lam' (x ^ k * g)
  have hΦ : IsMeromorphicInCoordinatesOn Φ D := by
    refine isMeromorphicInCoordinatesOn_finsetSum _ hD fun k _ => ?_
    refine isMeromorphicInCoordinatesOn_mul_entire (fun n e => ?_) (hΨ (x ^ k * g))
    exact differentiable_translationRootPolynomial_coeff Finset.univ (fun j => ρ j ∘ e)
      (fun j _ => hρ j n e) k
  have hEq := r.eqOn_of_regularParameter hA hT hG hΦ (isMeromorphicInCoordinatesOn_const_zero hD) R
    fun lam' hlam' => by
      have h := hreg lam' hlam' g
      rw [hdeg] at h
      exact h
  rw [hdeg]
  exact hEq ⟨hlam, hlam⟩

end Continuation

/-! ### Holomorphy of constant terms -/

section ConstantTerm

variable {F : Type} [Field F] [NumberField F] {G H : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine H.X.left]

/-- **Holomorphy of constant terms of holomorphic families.** Let `j : H → G` be a closed
subgroup with compact quotient `H(F) \ H(𝔸)`, and let `f s` be left `G(F)`-invariant functions
on `G(𝔸)` such that `(s, g) ↦ f s g` is continuous on `W × G(𝔸)` and `s ↦ f s g` is holomorphic
on the open set `W ⊆ ℂⁿ` for every `g`. Then `s ↦ ∫_{H(F) \ H(𝔸)} f s (h g₀) dh` is holomorphic
on `W`. -/
theorem differentiableOn_subgroupConstantTerm (j : H ⟶ G) [IsClosedImmersion j.hom.hom.left]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    {n : ℕ} (f : (Fin n → ℂ) → AdelicGroupPoints F G → ℂ) {W : Set (Fin n → ℂ)}
    (hW : IsOpen W)
    (hcont : ContinuousOn (fun q : (Fin n → ℂ) × AdelicGroupPoints F G => f q.1 q.2)
      (W ×ˢ univ))
    (hdiff : ∀ g, DifferentiableOn ℂ (fun s => f s g) W)
    (hinv : ∀ s ∈ W, ∀ c ∈ rationalSubgroup F G, ∀ g, f s (c * g) = f s g)
    (g₀ : AdelicGroupPoints F G) :
    DifferentiableOn ℂ (fun s => subgroupConstantTerm F j (f s) g₀) W := by
  let U := SubgroupFunctor.range j
  let Γ := AdelicSubgroupPoints.rationalSubgroup F G U
  have hcl : IsClosed (AdelicSubgroupPoints.adelicPoints F G U : Set (AdelicGroupPoints F G)) :=
    AdelicSubgroupPoints.isClosed_adelicPoints_range F G j
  let := AdelicSubgroupPoints.rationalQuotientBorelSpace F G U
  have := AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure_isProbabilityMeasure F G U
  have hΓ : ∀ c0 : Γ, ((c0 : AdelicSubgroupPoints.adelicPoints F G U) : AdelicGroupPoints F G) ∈
      rationalSubgroup F G := by
    rintro ⟨_, q, rfl⟩
    exact ⟨q.val, rfl⟩
  -- the integrand does not depend on the representative
  have hrep : ∀ s ∈ W, ∀ u v : AdelicSubgroupPoints.adelicPoints F G U,
      LeftCosetSpace.mk Γ u = LeftCosetSpace.mk Γ v →
        f s ((u : AdelicGroupPoints F G) * g₀) = f s ((v : AdelicGroupPoints F G) * g₀) := by
    intro s hs u v huv
    have hw : v * u⁻¹ ∈ Γ := (LeftCosetSpace.mk_eq_mk_iff Γ u v).mp huv
    have hv : (v : AdelicGroupPoints F G) =
        ((⟨v * u⁻¹, hw⟩ : Γ) : AdelicSubgroupPoints.adelicPoints F G U) * u := by
      simp
    rw [hv, mul_assoc, hinv s hs _ (hΓ ⟨v * u⁻¹, hw⟩)]
  let Φ : (Fin n → ℂ) → AdelicSubgroupPoints.RationalQuotient F G U → ℂ := fun s x =>
    f s (((Quotient.out x : AdelicSubgroupPoints.adelicPoints F G U) :
      AdelicGroupPoints F G) * g₀)
  have hΦmk : ∀ s ∈ W, ∀ u : AdelicSubgroupPoints.adelicPoints F G U,
      Φ s (LeftCosetSpace.mk Γ u) = f s ((u : AdelicGroupPoints F G) * g₀) := fun s hs u =>
    hrep s hs _ _ (Quotient.out_eq _)
  -- joint continuity of the integrand on `W × H(F) \ H(𝔸)`
  have hπ : IsOpenQuotientMap (Prod.map (id : (Fin n → ℂ) → (Fin n → ℂ))
      (LeftCosetSpace.mk Γ)) :=
    IsOpenQuotientMap.id.prodMap (LeftCosetSpace.isOpenQuotientMap_mk Γ)
  have hΦc : ∀ s ∈ W, ∀ x, ContinuousAt (fun q => Φ q.1 q.2) (s, x) := by
    intro s hs x
    obtain ⟨u, rfl⟩ := LeftCosetSpace.mk_surjective Γ x
    have hcomp : ContinuousAt ((fun q => Φ q.1 q.2) ∘
        Prod.map (id : (Fin n → ℂ) → (Fin n → ℂ)) (LeftCosetSpace.mk Γ)) (s, u) := by
      have hlin : ContinuousAt (fun q : (Fin n → ℂ) × AdelicSubgroupPoints.adelicPoints F G U =>
          f q.1 ((q.2 : AdelicGroupPoints F G) * g₀)) (s, u) := by
        have hat : ContinuousAt (fun q : (Fin n → ℂ) × AdelicGroupPoints F G => f q.1 q.2)
            (s, (u : AdelicGroupPoints F G) * g₀) :=
          hcont.continuousAt (prod_mem_nhds (hW.mem_nhds hs) univ_mem)
        have hmap : ContinuousAt
            (fun q : (Fin n → ℂ) × AdelicSubgroupPoints.adelicPoints F G U =>
              ((q.1, (q.2 : AdelicGroupPoints F G) * g₀) : (Fin n → ℂ) × AdelicGroupPoints F G))
            (s, u) :=
          (continuous_fst.prodMk ((continuous_subtype_val.comp continuous_snd).mul
            continuous_const)).continuousAt
        exact ContinuousAt.comp_of_eq hat hmap rfl
      refine hlin.congr ?_
      filter_upwards [prod_mem_nhds (hW.mem_nhds hs) (univ_mem :
        (univ : Set (AdelicSubgroupPoints.adelicPoints F G U)) ∈ 𝓝 u)] with q hq
      exact (hΦmk q.1 hq.1 q.2).symm
    exact (hπ.continuousAt_comp_iff).mp hcomp
  have hint : ∀ s, subgroupConstantTerm F j (f s) g₀ =
      ∫ x, Φ s x ∂AdelicSubgroupPoints.normalizedRationalQuotientHaarMeasure F G U := fun s => rfl
  simp only [hint]
  refine Langlands.Analysis.SeveralComplex.differentiableOn_integral_of_bounded _ Φ hW
    (fun x => hdiff _) (fun s hs => ?_) (fun K hKW hK => ?_)
  · -- measurability: the integrand is continuous on the quotient
    have hc : Continuous (Φ s) := by
      refine continuous_iff_continuousAt.2 fun x => ?_
      exact (hΦc s hs x).comp (f := fun y => (s, y)) (continuous_const.prodMk continuous_id).continuousAt
    exact hc.aestronglyMeasurable
  · -- boundedness on compact sets of parameters
    have hKc : IsCompact (K ×ˢ (univ : Set (AdelicSubgroupPoints.RationalQuotient F G U))) :=
      hK.prod isCompact_univ
    have hcon : ContinuousOn (fun q => Φ q.1 q.2)
        (K ×ˢ (univ : Set (AdelicSubgroupPoints.RationalQuotient F G U))) :=
      fun q hq => (hΦc q.1 (hKW hq.1) q.2).continuousWithinAt
    obtain ⟨C, hC⟩ := hKc.exists_bound_of_continuousOn hcon
    exact ⟨C, fun s hs x => hC (s, x) ⟨hs, mem_univ x⟩⟩

end ConstantTerm

/-! ### Constant terms of the continued Eisenstein series -/

section Continued

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

/-- **Constant terms of a continued Eisenstein series are meromorphic.** Let `E` be a pointwise
meromorphic continuation of `E(φ, λ)` with domain of holomorphy `D`, for `φ` automorphic on
`U(𝔸) M(F) \ G(𝔸)`. Granting the root-hyperplane form `EisensteinJointRootHyperplaneStatement`,
for every closed subgroup `j : H → G` with compact quotient `H(F) \ H(𝔸)` and every `g₀`, the
constant term `λ ↦ ∫_{H(F) \ H(𝔸)} E(λ)(h g₀) dh` is meromorphic in coordinates with domain
of holomorphy `D`. -/
theorem isMeromorphicInCoordinatesOn_subgroupConstantTerm
    (hJ : EisensteinJointRootHyperplaneStatement.{0})
    (hG : IsConnectedReductive G) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) {N d : ℕ}
    (rho : MatrixRepresentation G (Fin N)) (hsmooth : SmoothOfRelativeDimension d G.X.hom)
    (hcalc : AdelicDifferentialCommutator F G hsmooth) {φ : AdelicGroupPoints F G → ℂ}
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hφ : IsAutomorphicFunctionOn F G hsmooth hcalc (parabolicQuotientSubgroup F p iU l)
      (K.comap (ofInfinite F G).toMonoidHom) rho φ)
    {E : ComplexCharacterParameter F P → AdelicGroupPoints F G → ℂ}
    {D : Set (ComplexCharacterParameter F P)}
    (hmero : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      E lam = hK.eisensteinSeries φ lam)
    {H : GroupScheme (Spec (CommRingCat.of F))} [IsAffine H.X.left] (j : H ⟶ G)
    [IsClosedImmersion j.hom.hom.left]
    [CompactSpace (AdelicSubgroupPoints.RationalQuotient F G (SubgroupFunctor.range j))]
    (g₀ : AdelicGroupPoints F G) :
    IsMeromorphicInCoordinatesOn (fun lam => subgroupConstantTerm F j (E lam) g₀) D := by
  refine ⟨(hmero g₀).1, fun n e => ?_⟩
  have hDo : IsOpen (e ⁻¹' D) := ((hmero g₀).2 n e).1
  have hDd : Dense (e ⁻¹' D) := ((hmero g₀).2 n e).2.1
  have hdiffE : ∀ g, DifferentiableOn ℂ (fun s => E (e s) g) (e ⁻¹' D) := fun g =>
    differentiableOn_of_isHolomorphicOn ((hmero g).2 n e).2.2.1
  have hinvE : ∀ s ∈ e ⁻¹' D, ∀ c ∈ rationalSubgroup F G, ∀ g, E (e s) (c * g) = E (e s) g :=
    fun s hs c hc g =>
      eisensteinContinuation_leftRationalInvariant hK hφ.1 hU r hA hT hG hmero hreg hs c hc g
  -- the root forms, in the coordinates `e`
  let Lf : characterLattice A → (Fin n → ℂ) →ₗ[ℂ] ℂ := fun β =>
    (r.rootFunctional hA hT β).comp e.toLinearMap
  have hLf : ∀ β, r.realRootFunctional hA hT β ≠ 0 → ∃ w, Lf β w ≠ 0 := fun β hβ => by
    obtain ⟨χ, hχ⟩ := r.exists_rootFunctional_ne_zero hA hT hβ
    exact ⟨e.symm ((1 : ℂ) ⊗ₜ[ℤ] χ), by simpa [Lf] using hχ⟩
  have hLfsub : ∀ β (s s₀ : Fin n → ℂ),
      r.rootFunctional hA hT β (e s - e s₀) = Lf β (s - s₀) := fun β s s₀ => by
    simp [Lf, map_sub]
  -- joint continuity on `D × G(𝔸)`
  have hjc : ContinuousOn (fun q : (Fin n → ℂ) × AdelicGroupPoints F G => E (e q.1) q.2)
      ((e ⁻¹' D) ×ˢ univ) := by
    intro q hq
    refine ContinuousAt.continuousWithinAt ?_
    obtain ⟨S, k, W, h, -, hSne, hWo, hs₀W, hhc, -, -, hhE⟩ :=
      hJ F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hmero
        hreg n e q.1
    refine continuousAt_of_rootHyperplane_cleared (E' := fun s g => E (e s) g) hDo hdiffE S Lf
      (fun β hβ => hLf β (hSne β hβ)) k hWo hs₀W hq.1 hhc ?_ q.2
    intro g s hsW hsD
    rw [hhE g s hsW hsD]
    simp only [hLfsub]
  have hct : DifferentiableOn ℂ (fun s => subgroupConstantTerm F j (E (e s)) g₀) (e ⁻¹' D) :=
    differentiableOn_subgroupConstantTerm j (fun s g => E (e s) g) hDo hjc hdiffE hinvE g₀
  rw [isMeromorphicOn_iff]
  refine ⟨hDo, hDd, hct, fun s₀ => ?_⟩
  obtain ⟨S, k, W, h, -, hSne, hWo, hs₀W, hhc, hhd, hhinv, hhE⟩ :=
    hJ F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ E D hmero
      hreg n e s₀
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 hWo s₀ hs₀W
  let g₁ : (Fin n → ℂ) → ℂ := fun s => (∏ β ∈ S, Lf β (s - s₀)) ^ k
  have hg₁ : Differentiable ℂ g₁ := by
    have hprod : Differentiable ℂ fun s : Fin n → ℂ => ∏ β ∈ S, Lf β (s - s₀) :=
      differentiable_finsetProd_apply S (fun β (s : Fin n → ℂ) => Lf β (s - s₀))
        fun β _ => by
          change Differentiable ℂ ((LinearMap.toContinuousLinearMap (Lf β)) ∘ fun s => s - s₀)
          exact (LinearMap.toContinuousLinearMap (Lf β)).differentiable.comp
            (differentiable_id.sub_const s₀)
    exact hprod.pow k
  -- a point of the ball off all root hyperplanes through `s₀`
  have hg₁ne : ∃ s ∈ Metric.ball s₀ ε, g₁ s ≠ 0 := by
    obtain ⟨v, hv⟩ := Module.Dual.exists_forall_ne_zero_of_forall_exists
      (fun β : S => Lf β) (fun β => hLf β (hSne β β.2))
    set t : ℝ := ε / (2 * (‖v‖ + 1)) with ht
    have htpos : 0 < t := div_pos hε (by positivity)
    have htv : t * ‖v‖ < ε := by
      rw [ht, div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
      nlinarith [norm_nonneg v]
    refine ⟨s₀ + (t : ℂ) • v, ?_, ?_⟩
    · rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_smul, Complex.norm_real,
        Real.norm_of_nonneg htpos.le]
      exact htv
    · refine pow_ne_zero k (Finset.prod_ne_zero_iff.2 fun β hβ => ?_)
      rw [add_sub_cancel_left, map_smul, smul_eq_mul]
      exact mul_ne_zero (Complex.ofReal_ne_zero.2 htpos.ne') (hv ⟨β, hβ⟩)
  have hh₁ : DifferentiableOn ℂ (fun s => subgroupConstantTerm F j (h s) g₀) W :=
    differentiableOn_subgroupConstantTerm j h hWo hhc hhd hhinv g₀
  refine ⟨Metric.ball s₀ ε, Metric.isOpen_ball,
    (convex_ball s₀ ε).isConnected (Metric.nonempty_ball.2 hε), Metric.mem_ball_self hε, g₁,
    fun s => subgroupConstantTerm F j (h s) g₀, hg₁.differentiableOn, hg₁ne, hh₁.mono hball,
    fun s hs => ?_⟩
  have hsW : s ∈ W := hball hs.2
  have hfun : h s = fun g => g₁ s * E (e s) g := by
    funext g
    rw [hhE g s hsW hs.1]
    simp only [g₁, hLfsub]
  change g₁ s * subgroupConstantTerm F j (E (e s)) g₀ = subgroupConstantTerm F j (h s) g₀
  rw [hfun]
  unfold subgroupConstantTerm
  rw [integral_const_mul]

end Continued

end UnitaryExponent

open UnitaryExponent in
/-- **Subunitary exponents at unitary parameters from the regular exponent labels.** The
root-hyperplane form of continued Eisenstein series and the exponent labels of their constant
terms at regular parameters imply `EisensteinUnitaryExponentStatement`. With `b` labels of degree
at most `n` the order is `m = b (n + 1)`: the label `ν_j(λ) = L_j λ + c_j` contributes the root
`a^{ν_j(λ)}` with multiplicity `n + 1`, and the remaining roots are `0`. -/
theorem eisensteinUnitaryExponent_of_exponentLabels
    (hJ : EisensteinJointRootHyperplaneStatement.{0})
    (hL : EisensteinConstantTermExponentLabelsStatement) :
    EisensteinUnitaryExponentStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc
    φ hKmax hrho hφ E D hD hmero hreg n e Cpt hCpt
  obtain ⟨b, deg, hlab⟩ :=
    hL F G P M U A p iU l a r hA hT hG hU K hK rho hsmooth hcalc φ hKmax hrho hφ
  refine ⟨b * (deg + 1), fun 𝓕 J x _ s hs => ?_⟩
  obtain ⟨R₁, k, Lab, c, hkb, hsub, hexp⟩ := hlab 𝓕 J
  obtain ⟨R₀, hR₀⟩ := hreg
  set aP := PositiveRealTorus.positivePointMap F (𝓕.P J) (𝓕.A J) (𝓕.a J ≫ 𝓕.l J) s with haP
  have haA : aP ∈ 𝓕.positiveSplitComponent J := ⟨s.1, s.2, rfl⟩
  -- the roots: each label with multiplicity `deg + 1`, padded with zeros
  set pad := b * (deg + 1) - k * (deg + 1) with hpad
  have hm : k * (deg + 1) + pad = b * (deg + 1) :=
    Nat.add_sub_cancel' (Nat.mul_le_mul_right _ hkb)
  let σ : (Fin k × Fin (deg + 1)) ⊕ Fin pad ≃ Fin (b * (deg + 1)) :=
    ((Equiv.sumCongr finProdFinEquiv (Equiv.refl _)).trans finSumFinEquiv).trans (finCongr hm)
  let root : Fin k → ComplexCharacterParameter F P → ℂ := fun j lam =>
    parameterPower F (𝓕.P J) (Lab j lam + c j) aP
  let ρ : Fin (b * (deg + 1)) → ComplexCharacterParameter F P → ℂ := fun q lam =>
    Sum.elim (fun jt : Fin k × Fin (deg + 1) => root jt.1 lam) (fun _ => 0) (σ.symm q)
  have hprod : ∀ lam, ∏ q, (X - C (ρ q lam)) =
      (∏ j, (X - C (root j lam)) ^ (deg + 1)) * X ^ pad := by
    intro lam
    rw [← σ.prod_comp, Fintype.prod_sum_type, Fintype.prod_prod_type]
    simp only [ρ, Equiv.symm_apply_apply, Sum.elim_inl, Sum.elim_inr, map_zero, sub_zero,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  refine ⟨fun q => ρ q (imaginaryParameter F P (e x)), fun q => ?_, ?_⟩
  · -- the bound on the roots
    change ‖Sum.elim (fun jt : Fin k × Fin (deg + 1) => root jt.1 _) (fun _ => (0 : ℂ))
      (σ.symm q)‖ ≤ _
    rcases σ.symm q with jt | t
    · exact hsub jt.1 (e x) s hs
    · simp only [Sum.elim_inr, norm_zero]
      exact norm_nonneg _
  · -- the difference equation, continued from the regular parameters
    have hVr := (𝓕.isUnipotentRadical J).1
    have : IsAffineHom (𝓕.U J).X.hom := IsClosedSubgroup.isAffineHom hVr.isClosedSubgroup
    have : CompactSpace (AdelicSubgroupPoints.RationalQuotient F G
        (SubgroupFunctor.range (𝓕.iU J ≫ 𝓕.p J))) :=
      AdelicSubgroupPoints.compactSpace_rationalQuotient_range_unipotent F (𝓕.iU J ≫ 𝓕.p J)
        hVr.smooth hVr.connectedSpace hVr.isUnipotent
    have hΨ : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => 𝓕.constantTerm J (E lam) g) D :=
      fun g => isMeromorphicInCoordinatesOn_subgroupConstantTerm r hA hT hJ hG hU hK rho hsmooth
        hcalc hKmax hrho hφ.1 hmero ⟨R₀, hR₀⟩ (𝓕.iU J ≫ 𝓕.p J) g
    have hρ : ∀ q (n' : ℕ) (e' : (Fin n' → ℂ) ≃ₗ[ℂ] ComplexCharacterParameter F P),
        Differentiable ℂ (ρ q ∘ e') := by
      intro q n' e'
      rcases hq : σ.symm q with jt | t
      · have h := differentiable_parameterPower_affine ((Lab jt.1).comp e'.toLinearMap) (c jt.1) aP
        convert h using 1
        funext t'
        simp only [Function.comp_apply, ρ, hq, Sum.elim_inl, root, LinearMap.comp_apply,
          LinearEquiv.coe_coe]
      · convert differentiable_const (c := (0 : ℂ)) using 1
        funext t'
        simp only [Function.comp_apply, ρ, hq, Sum.elim_inr]
    refine isTranslationPolynomialSolution_of_regular r hA hT hG
      (fun lam => 𝓕.constantTerm J (E lam)) hΨ ρ hρ _ (max R₀ R₁) (fun lam hlam => ?_)
      (hD ⟨e x, rfl⟩)
    have hlam₀ : r.IsRegularParameter hA hT R₀ lam := fun α hα =>
      (le_max_left R₀ R₁).trans_lt (hlam α hα)
    have hlam₁ : r.IsRegularParameter hA hT R₁ lam := fun α hα =>
      (le_max_right R₀ R₁).trans_lt (hlam α hα)
    obtain ⟨f, hf, hsum⟩ := hexp lam hlam₁
    rw [hprod lam]
    change IsTranslationPolynomialSolution _ _ (𝓕.constantTerm J (E lam))
    rw [hR₀ lam hlam₀, hsum]
    refine isTranslationPolynomialSolution_mul_right ?_ _
    exact isTranslationPolynomialSolution_sum_prod Finset.univ _ _ f fun j _ =>
      𝓕.isTranslationPolynomialSolution_pow_of_polynomialOrbit J (hf j) ⟨aP, haA⟩

/-- **Reduction of the subunitary exponents at unitary parameters**: the root-hyperplane form of
continued Eisenstein series (`EisensteinJointRootHyperplaneStatement`, at universe `0`) and the
exponent labels of their constant terms at regular parameters
(`EisensteinConstantTermExponentLabelsStatement`) imply `EisensteinUnitaryExponentStatement`. -/
def EisensteinUnitaryExponentReductionStatement : Prop :=
  EisensteinJointRootHyperplaneStatement.{0} → EisensteinConstantTermExponentLabelsStatement →
    EisensteinUnitaryExponentStatement

theorem eisensteinUnitaryExponentReduction : EisensteinUnitaryExponentReductionStatement :=
  eisensteinUnitaryExponent_of_exponentLabels

end Langlands.Global

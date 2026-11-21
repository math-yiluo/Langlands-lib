import Langlands.Global.AdelicImaginaryIntertwiningExistence
import Langlands.Global.AdelicIntertwiningSquareIntegrableExpansionStatement
import Langlands.Analysis.HilbertDensityCriteria
import Langlands.Global.AdelicIntertwiningCocycleStatement
import Langlands.Global.AdelicIntertwiningRepresentativeStatement
import Langlands.Global.AdelicSymmetricFamilyGram

/-! # Properties of the operators `M(w, λ) : H_P → H_{P'}` on the imaginary axis

For a family `Mop x : H_P → H_{P'}` with `IsImaginaryIntertwiningOperator`:

* `inner_map_map_of_isImaginaryIntertwiningOperator`: each `Mop x` preserves inner products,
  given the unitarity statement, the square integrability of restrictions and the finite
  expansions of `M(w, λ)` on `A^2_P` in `A^2_{P'}`;
* `map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator`: `Mop x` sends the class of `v ∈ A^2_P`
  to `∑ q, coeff q (i e(x)) • [ψ q]` for any qualifying expansion of `M(w, λ) v`;
* `map_comp_of_isImaginaryIntertwiningOperator`: the cocycle relation on those classes for
  enumerated Weyl maps, using the representative-independence premise. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct InnerProductSpace

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Pair

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' : GroupScheme (Spec (CommRingCat.of F))}
  {A A' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  [LocallyOfFiniteType P.X.hom] [LocallyOfFiniteType P'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left]
  {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation p' l' a'}
  [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
  [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
  {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : P' ⟶ M'}
  {K : Subgroup (AdelicGroupPoints F G)} {hK : IsIwasawaCompact p K}
  {hK' : IsIwasawaCompact p' K} {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom} {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : Measure (AdelicGroupPoints F M)} [μM.IsHaarMeasure]
  {μM' : Measure (AdelicGroupPoints F M')} [μM'.IsHaarMeasure]
  {n n' : ℕ} {e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P}
  {e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P'}
  {β : (Fin n → ℝ) → ℝ} {β' : (Fin n' → ℝ) → ℝ}
  {w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X} {cw : M' ⟶ M}

include hA' hT' in
set_option maxHeartbeats 4000000 in
/-- Two expansions `M(w, λ) v_s = ∑ q, cs q λ • ψs q` and `M(w, λ) v_t = ∑ q, ct q λ • ψt q` in
`A^2_{P'}`, with coefficients meromorphic on domains containing the imaginary axis, give pairs
`([v_s], [∑ q, cs q (i e x) • ψs q])`, `([v_t], [∑ q, ct q (i e x) • ψt q])` of classes in
`H_P × H_{P'}` with `⟪s₂, t₂⟫ = ⟪s₁, t₁⟫` (the Gram identity of the unitarity statement at
`λ = i e(x)`). This is the argument of `imaginaryIntertwiningExistenceBridge`. -/
theorem inner_eq_of_expansions (hU : IntertwiningImaginaryUnitarityStatement)
    (hL : InducedRestrictionMemLpStatement) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hUR' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hMul' : IsIso (subgroupMultiplication l' iU')) (hπ' : l' ≫ π' = 𝟙 M')
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hμM : IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM)
    (hμM' : IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM')
    (hβ : Continuous β ∧ HasCompactSupport β ∧ (∀ y, 0 ≤ β y) ∧ ∫ y, β y = 1)
    (hβ' : Continuous β' ∧ HasCompactSupport β' ∧ (∀ y, 0 ≤ β' y) ∧ ∫ y, β' y = 1)
    (hw : IsWeylConjugation p l p' l' w cw)
    (hmp : MeasurePreserving (fun x => e'.symm (realWeylParameter l cw π' (e x))) volume volume)
    (x : Fin n → ℝ) {vs vt : AdelicGroupPoints F G → ℂ}
    (hvs : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l vs)
    (hvt : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l vt)
    {ms mt : ℕ} {ψs : Fin ms → AdelicGroupPoints F G → ℂ} {ψt : Fin mt → AdelicGroupPoints F G → ℂ}
    {cs : Fin ms → ComplexCharacterParameter F P → ℂ}
    {ct : Fin mt → ComplexCharacterParameter F P → ℂ} {DMs DMt : Set (ComplexCharacterParameter F P)}
    (hψs : ∀ q, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψs q))
    (hψt : ∀ q, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψt q))
    (hDMs : Set.range (imaginaryParameter F P) ⊆ DMs)
    (hDMt : Set.range (imaginaryParameter F P) ⊆ DMt)
    (hcs : ∀ q, IsMeromorphicInCoordinatesOn (cs q) DMs)
    (hct : ∀ q, IsMeromorphicInCoordinatesOn (ct q) DMt)
    (hRs : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iU' cw π' w vs lam g = ∑ q, cs q lam * ψs q g)
    (hRt : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iU' cw π' w vt lam g = ∑ q, ct q lam * ψt q g)
    (s₁ t₁ : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β)
    (s₂ t₂ : inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β')
    (hs1 : ⇑(s₁ : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β))
      =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l vs)
    (ht1 : ⇑(t₁ : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β))
      =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l vt)
    (hs2 : ⇑(s₂ : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β'))
      =ᵐ[inducedL2Measure K hK'.isCompact l' μM' e' β']
      inducedRestriction K p' l' fun g => ∑ q, cs q (imaginaryParameter F P (e x)) * ψs q g)
    (ht2 : ⇑(t₂ : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β'))
      =ᵐ[inducedL2Measure K hK'.isCompact l' μM' e' β']
      inducedRestriction K p' l' fun g => ∑ q, ct q (imaginaryParameter F P (e x)) * ψt q g) :
    ⟪s₂, t₂⟫_ℂ = ⟪s₁, t₁⟫_ℂ := by
  obtain rfl : n = n' := Langlands.Analysis.eq_of_measurePreserving_linearMap
    (e'.symm.toLinearMap ∘ₗ realWeylParameter l cw π' ∘ₗ e.toLinearMap) hmp
  obtain ⟨e'', β'', he'', hβ''c, hβ''cs, -, hβ''i, hβ''⟩ :=
    exists_transported_coordinates e e' (realWeylParameter l cw π') β' hβ' hmp
  have hIP' : ∀ φ ψ : AdelicGroupPoints F G → ℂ,
      inducedInnerProduct K hK'.isCompact p' l' μM' e'' β'' φ ψ =
        inducedInnerProduct K hK'.isCompact p' l' μM' e' β' φ ψ := by
    intro φ ψ
    unfold inducedInnerProduct
    simp only [hβ'']
  have hL' : ∀ φ, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' φ →
      MemLp (inducedRestriction K p' l' φ) 2 (inducedL2Measure K hK'.isCompact l' μM' e' β') :=
    fun φ hφ => hL F G P' M' U' A' p' iU' l' a' r' hA' hT' π' hG hUR' hMul' hπ' K hK' rho hsmooth
      hcalc hKmax hrho μM' hμM' e' β' hβ'.1 hβ'.2.1 hβ'.2.2.1 φ hφ
  obtain ⟨Ds, hDs, hcsD, hDsg⟩ := exists_domain_of_isMeromorphicInCoordinatesOn hcs
  obtain ⟨Dt, hDt, hctD, hDtg⟩ := exists_domain_of_isMeromorphicInCoordinatesOn hct
  let ψ2 : Fin (ms + mt) → AdelicGroupPoints F G → ℂ := Fin.append ψs ψt
  let co : Fin 2 → Fin (ms + mt) → ComplexCharacterParameter F P → ℂ :=
    ![Fin.append cs (fun _ _ => 0), Fin.append (fun _ _ => 0) ct]
  have hψ2 : ∀ i,
      IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ2 i) := by
    intro i
    refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · simp only [ψ2, Fin.append_left]
      exact hψs q
    · simp only [ψ2, Fin.append_right]
      exact hψt q
  have hcs' : ∀ q, IsMeromorphicInCoordinatesOn (cs q) (Ds ∩ Dt) :=
    fun q => hDtg _ _ (hcsD q)
  have hct' : ∀ q, IsMeromorphicInCoordinatesOn (ct q) (Ds ∩ Dt) := fun q => by
    rw [Set.inter_comm]
    exact hDsg _ _ (hctD q)
  have hco : ∀ j i, IsMeromorphicInCoordinatesOn (co j i) (Ds ∩ Dt) := by
    refine Fin.forall_fin_two.2 ⟨fun i => ?_, fun i => ?_⟩ <;>
      refine Fin.addCases (fun q => ?_) (fun q => ?_) i
    · simp only [co, Matrix.cons_val_zero, Fin.append_left]
      exact hcs' q
    · simp only [co, Matrix.cons_val_zero, Fin.append_right]
      exact isMeromorphicInCoordinatesOn_zero_of (hct' q)
    · simp only [co, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.append_left]
      exact isMeromorphicInCoordinatesOn_zero_of (hcs' q)
    · simp only [co, Matrix.cons_val_one, Matrix.cons_val_zero, Fin.append_right]
      exact hct' q
  have hcoR : ∀ j : Fin 2, ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iU' cw π' w (![vs, vt] j) lam g =
        ∑ i, co j i lam * ψ2 i g := by
    refine Fin.forall_fin_two.2 ⟨?_, ?_⟩
    · obtain ⟨R, hR⟩ := hRs
      refine ⟨R, fun lam hlam g => ?_⟩
      simp only [Matrix.cons_val_zero]
      rw [hR lam hlam g, Fin.sum_univ_add]
      simp [co, ψ2]
    · obtain ⟨R, hR⟩ := hRt
      refine ⟨R, fun lam hlam g => ?_⟩
      simp only [Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [hR lam hlam g, Fin.sum_univ_add]
      simp [co, ψ2]
  have hv2 : ∀ j : Fin 2,
      IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l (![vs, vt] j) :=
    Fin.forall_fin_two.2 ⟨hvs, hvt⟩
  obtain ⟨co', DM', hDM', -, hagree, hgram⟩ := hU F G P M U P' M' U' A p iU l a r hA hT p'
    iU' l' π' w cw hG hUR r'.isCompatible.parabolic hUR' r'.isCompatible.levi hMul' hπ' hw K hK
    hK' rho hsmooth hcalc hKmax hrho μM μM' hμM hμM' e e'' he'' β β'' hβ.1 hβ.2.1 hβ.2.2.2
    hβ''c hβ''cs hβ''i 2 (ms + mt) ![vs, vt] (fun _ => ψ2) co (Ds ∩ Dt) hv2 (fun _ => hψ2)
    hco hcoR
  set lam0 := imaginaryParameter F P (e x) with hlam0
  have hlam0D : lam0 ∈ (Ds ∩ Dt) ∩ DM' :=
    ⟨⟨hDs (hDMs ⟨e x, rfl⟩), hDt (hDMt ⟨e x, rfl⟩)⟩, hDM' ⟨e x, rfl⟩⟩
  have hm2 : ∀ i, MemLp (inducedRestriction K p' l' (ψ2 i)) 2
      (inducedL2Measure K hK'.isCompact l' μM' e' β') := fun i => hL' _ (hψ2 i)
  have hZ : ∀ j : Fin 2, ∀ (h' : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')),
      ⇑h' =ᵐ[inducedL2Measure K hK'.isCompact l' μM' e' β']
        inducedRestriction K p' l' (fun g => ∑ i, co j i lam0 * ψ2 i g) →
      h' = ∑ i, co' j i lam0 • (hm2 i).toLp _ := by
    intro j h' hh'
    refine Lp.ext (hh'.trans ?_)
    have hfun : (fun g => ∑ i, co j i lam0 * ψ2 i g) = fun g => ∑ i, co' j i lam0 * ψ2 i g :=
      funext fun g => (hagree j lam0 hlam0D g).symm
    rw [hfun]
    exact ((sum_smul_toLp_mem_inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l'
      μM' e' β' hψ2 hm2 (fun i => co' j i lam0)).2).symm
  have hs2' : (s₂ : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =
      ∑ i, co' 0 i lam0 • (hm2 i).toLp _ := by
    refine hZ 0 _ (hs2.trans (Filter.Eventually.of_forall fun y => ?_))
    simp only [inducedRestriction]
    rw [Fin.sum_univ_add]
    simp [co, ψ2]
  have ht2' : (t₂ : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =
      ∑ i, co' 1 i lam0 • (hm2 i).toLp _ := by
    refine hZ 1 _ (ht2.trans (Filter.Eventually.of_forall fun y => ?_))
    simp only [inducedRestriction]
    rw [Fin.sum_univ_add]
    simp [co, ψ2]
  have hY : ∀ i i', ⟪(hm2 i).toLp _, (hm2 i').toLp _⟫_ℂ =
      inducedInnerProduct K hK'.isCompact p' l' μM' e' β' (ψ2 i') (ψ2 i) := fun i i' =>
    inner_eq_inducedInnerProduct K hK'.isCompact p' l' μM' e' β' hβ'.1 hβ'.2.2.1 _ _ _ _
      (hm2 i).coeFn_toLp (hm2 i').coeFn_toLp
  rw [Submodule.coe_inner, Submodule.coe_inner, hs2', ht2',
    inner_eq_inducedInnerProduct K hK.isCompact p l μM e β hβ.1 hβ.2.2.1 _ _ vs vt hs1 ht1]
  have hg := hgram (e x) 1 0
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, hIP'] at hg
  rw [← hg, sum_inner]
  simp only [inner_sum, inner_smul_left, inner_smul_right, hY]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun i' _ => ?_
  ring

include hA' hT' in
set_option maxHeartbeats 4000000 in
/-- Each `Mop x` of a family with `IsImaginaryIntertwiningOperator` preserves inner products. On
classes of elements of `A^2_P` this is `inner_eq_of_expansions`, applied to the finite expansions
of `IntertwiningSquareIntegrableExpansionStatement`; these classes span a dense subspace of
`H_P`. -/
theorem inner_map_map_of_isImaginaryIntertwiningOperator
    (hU : IntertwiningImaginaryUnitarityStatement) (hL : InducedRestrictionMemLpStatement)
    (hE : IntertwiningSquareIntegrableExpansionStatement) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hUR' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hMul' : IsIso (subgroupMultiplication l' iU')) (hπ' : l' ≫ π' = 𝟙 M')
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hμM : IsIwasawaCompatibleMeasure K hK.isCompact p iU l μM)
    (hμM' : IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM')
    (hβ : Continuous β ∧ HasCompactSupport β ∧ (∀ y, 0 ≤ β y) ∧ ∫ y, β y = 1)
    (hβ' : Continuous β' ∧ HasCompactSupport β' ∧ (∀ y, 0 ≤ β' y) ∧ ∫ y, β' y = 1)
    (hw : IsWeylConjugation p l p' l' w cw)
    (hmp : MeasurePreserving (fun x => e'.symm (realWeylParameter l cw π' (e x))) volume volume)
    (Mop : (Fin n → ℝ) →
      inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
        inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β')
    (hMop : IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT iU' l' π' w cw
      μM μM' e e' β β' Mop)
    (x : Fin n → ℝ) (f g : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β) :
    ⟪Mop x f, Mop x g⟫_ℂ = ⟪f, g⟫_ℂ := by
  refine Langlands.Analysis.inner_map_map_eq_of_dense (Mop x)
    {h : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β |
      (h : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β)) ∈
        {f : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β) |
          ∃ φ, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l φ ∧
            f =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l φ}}
    (Langlands.Analysis.Submodule.topologicalClosure_span_subtype_eq_top _) ?_ f g
  rintro s ⟨vs, hvs, hs⟩ t ⟨vt, hvt, ht⟩
  obtain ⟨ms, ψs, cs, DMs, hψs, hDMs, hcs, Rs, hRs⟩ := hE F G P M U P' M' U' A A' p iU l a r hA
    hT p' iU' l' a' r' π' w cw hG hUR hUR' hMul' hπ' hw K hK hK' rho hsmooth hcalc vs hKmax hrho
    hvs
  obtain ⟨mt, ψt, ct, DMt, hψt, hDMt, hct, Rt, hRt⟩ := hE F G P M U P' M' U' A A' p iU l a r hA
    hT p' iU' l' a' r' π' w cw hG hUR hUR' hMul' hπ' hw K hK hK' rho hsmooth hcalc vt hKmax hrho
    hvt
  exact inner_eq_of_expansions (r' := r') (hA' := hA') (hT' := hT') hU hL hG hUR hUR' hMul' hπ' hKmax hrho hμM hμM' hβ hβ' hw hmp x
    hvs hvt hψs hψt hDMs hDMt hcs hct ⟨Rs, hRs⟩ ⟨Rt, hRt⟩ s t (Mop x s) (Mop x t) hs ht
    (hMop vs hvs ms ψs cs DMs hψs hDMs hcs ⟨Rs, hRs⟩ s hs x)
    (hMop vt hvt mt ψt ct DMt hψt hDMt hct ⟨Rt, hRt⟩ t ht x)

omit [IsAffine U.X.left] [IsClosedImmersion p.hom.hom.left] [μM.IsHaarMeasure] [μM'.IsHaarMeasure] in
/-- For an expansion `M(w, λ) v = ∑ q, coeff q λ • ψ q` in `A^2_{P'}` with coefficients
meromorphic on a domain containing the imaginary axis, `Mop x` sends any class of `v` to
`∑ q, coeff q (i e(x)) • [ψ q]`. -/
theorem map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator
    (Mop : (Fin n → ℝ) →
      inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
        inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β')
    (hMop : IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT iU' l' π' w cw
      μM μM' e e' β β' Mop)
    {v : AdelicGroupPoints F G → ℂ}
    (hv : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v)
    {m : ℕ} {ψ : Fin m → AdelicGroupPoints F G → ℂ}
    {coeff : Fin m → ComplexCharacterParameter F P → ℂ} {DM : Set (ComplexCharacterParameter F P)}
    (hψ : ∀ q, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ q))
    (hDM : Set.range (imaginaryParameter F P) ⊆ DM)
    (hcoeff : ∀ q, IsMeromorphicInCoordinatesOn (coeff q) DM)
    (hR : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iU' cw π' w v lam g = ∑ q, coeff q lam * ψ q g)
    (hm : ∀ q, MemLp (inducedRestriction K p' l' (ψ q)) 2
      (inducedL2Measure K hK'.isCompact l' μM' e' β'))
    (h : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β)
    (hh : ⇑(h : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β))
      =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l v)
    (x : Fin n → ℝ) :
    (Mop x h : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =
      ∑ q, coeff q (imaginaryParameter F P (e x)) • (hm q).toLp _ :=
  Lp.ext ((hMop v hv m ψ coeff DM hψ hDM hcoeff hR h hh x).trans
    ((sum_smul_toLp_mem_inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β'
      hψ hm _).2.symm))

end Pair

section Parameters

variable {F : Type} [Field F] [NumberField F] {P M Q M' : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- `w(iμ) = i(wμ)`: the complex map `λ ↦ wλ` sends imaginary parameters to imaginary
parameters, through its real form. -/
theorem weylParameter_imaginaryParameter (l : M ⟶ P) (c : M' ⟶ M) (π' : Q ⟶ M')
    (mu : RealCharacterParameter F P) :
    weylParameter l c π' (imaginaryParameter F P mu) =
      imaginaryParameter F Q (realWeylParameter l c π' mu) := by
  induction mu using TensorProduct.inductionOn with
  | tmul s χ => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end Parameters

section Flatten

variable {X Y : Type*} [AddCommGroup X] [Module ℂ X]

omit [AddCommGroup X] [Module ℂ X] in
/-- Flattening of finitely many expansions `Mv q mu g = ∑ j, b q j mu * χ q j g` of one length
into expansions in one family `χf` indexed by `Fin (ms * m)`, with coefficients that vanish
outside the block of `q`. -/
theorem exists_flat_expansions {ms m : ℕ} (χ : Fin ms → Fin m → Y → ℂ)
    (b : Fin ms → Fin m → X → ℂ) :
    ∃ (χf : Fin (ms * m) → Y → ℂ) (bf : Fin ms → Fin (ms * m) → X → ℂ),
      (∀ k, ∃ q j, χf k = χ q j) ∧
      (∀ q k, bf q k = 0 ∨ ∃ j, bf q k = b q j) ∧
      ∀ q mu g, ∑ k, bf q k mu * χf k g = ∑ j, b q j mu * χ q j g := by
  classical
  refine ⟨fun k => χ (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2,
    fun q k => if (finProdFinEquiv.symm k).1 = q then b q (finProdFinEquiv.symm k).2 else 0,
    fun k => ⟨_, _, rfl⟩, fun q k => ?_, fun q mu g => ?_⟩
  · by_cases h : (finProdFinEquiv.symm k).1 = q
    · exact Or.inr ⟨(finProdFinEquiv.symm k).2, by simp only [h, ↓reduceIte]⟩
    · exact Or.inl (by simp only [h, ↓reduceIte])
  · rw [← finProdFinEquiv.sum_comp]
    simp only [Equiv.symm_apply_apply, Fintype.sum_prod_type]
    rw [Finset.sum_eq_single q]
    · simp
    · intro q' _ hq'
      simp [hq']
    · simp

end Flatten

section Triple

variable {F : Type} [Field F] [NumberField F]
  {G P M U P' M' U' P'' M'' U'' : GroupScheme (Spec (CommRingCat.of F))}
  {A A' A'' : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine P'.X.left] [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine U'.X.left]
  [IsAffine P''.X.left] [IsAffine M''.X.left] [LocallyOfFiniteType M''.X.hom]
  [IsAffine U''.X.left]
  [LocallyOfFiniteType P.X.hom] [LocallyOfFiniteType P'.X.hom] [LocallyOfFiniteType P''.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {a : A.toGrp ⟶ M} {r : ParabolicRootPresentation p l a}
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  {hA : IsSplitTorus A.toGrp} {hT : IsSplitTorus r.data.T.toGrp}
  {p' : P' ⟶ G} [IsClosedImmersion p'.hom.hom.left] {iU' : U' ⟶ P'} {l' : M' ⟶ P'}
  [IsClosedImmersion (iU' ≫ p').hom.hom.left]
  {a' : A'.toGrp ⟶ M'} {r' : ParabolicRootPresentation p' l' a'}
  [Mono r'.data.i.hom.hom.left] [Fintype (relativeWeylGroup r'.data.i)]
  [Mono (CommGroupScheme.groupHom r'.data.f).hom.hom.left]
  {hA' : IsSplitTorus A'.toGrp} {hT' : IsSplitTorus r'.data.T.toGrp} {π' : P' ⟶ M'}
  {p'' : P'' ⟶ G} [IsClosedImmersion p''.hom.hom.left] {iU'' : U'' ⟶ P''} {l'' : M'' ⟶ P''}
  [IsClosedImmersion (iU'' ≫ p'').hom.hom.left]
  {a'' : A''.toGrp ⟶ M''} {r'' : ParabolicRootPresentation p'' l'' a''}
  [Mono r''.data.i.hom.hom.left] [Fintype (relativeWeylGroup r''.data.i)]
  [Mono (CommGroupScheme.groupHom r''.data.f).hom.hom.left]
  {hA'' : IsSplitTorus A''.toGrp} {hT'' : IsSplitTorus r''.data.T.toGrp} {π'' : P'' ⟶ M''}
  {K : Subgroup (AdelicGroupPoints F G)} {hK : IsIwasawaCompact p K}
  {hK' : IsIwasawaCompact p' K} {hK'' : IsIwasawaCompact p'' K} {N d : ℕ}
  {rho : MatrixRepresentation G (Fin N)} {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {μM : Measure (AdelicGroupPoints F M)} {μM' : Measure (AdelicGroupPoints F M')}
  {μM'' : Measure (AdelicGroupPoints F M'')} [μM'.IsHaarMeasure] [μM''.IsHaarMeasure]
  {n n' n'' : ℕ} {e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P}
  {e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P'}
  {e'' : (Fin n'' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P''}
  {β : (Fin n → ℝ) → ℝ} {β' : (Fin n' → ℝ) → ℝ} {β'' : (Fin n'' → ℝ) → ℝ}
  {ws wr wu : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X}
  {cs : M' ⟶ M} {cr : M'' ⟶ M'} {cu : M'' ⟶ M}

include hA'' hT'' in
set_option maxHeartbeats 4000000 in
/-- The cocycle relation for the operators on the imaginary axis: if `(ws, cs) ∈ W(P, P')`,
`(wr, cr) ∈ W(P', P'')` and `(wu, cu) ∈ W(P, P'')` with `u = r ∘ s` on parameters, then
`Mop_u(x) = Mop_r(s x) ∘ Mop_s(x)` on classes of elements of `A^2_P`, where `s x` is the
coordinate change `x ↦ e'⁻¹(s(e x))`. This combines the cocycle statement (Bernstein–Lapid,
Theorem 2.3 (5)) at `λ = i e(x)` with the finite expansions in `A^2` and the independence of the
operator from the representative of `u`. -/
theorem map_comp_of_isImaginaryIntertwiningOperator
    (hE : IntertwiningSquareIntegrableExpansionStatement)
    (hC : IntertwiningCocycleStatement.{0})
    (hI : IntertwiningRepresentativeIndependenceStatement)
    (hL : InducedRestrictionMemLpStatement) (hG : IsConnectedReductive G)
    (hUR : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (hUR' : LeviSubgroup.IsGeometricUnipotentRadical iU')
    (hUR'' : LeviSubgroup.IsGeometricUnipotentRadical iU'')
    (hMul : IsIso (subgroupMultiplication l iU)) (hMul' : IsIso (subgroupMultiplication l' iU'))
    (hMul'' : IsIso (subgroupMultiplication l'' iU'')) (hπ' : l' ≫ π' = 𝟙 M')
    (hπ'' : l'' ≫ π'' = 𝟙 M'')
    (hKmax : IsMaximalCompactSubgroup F G K) (hrho : IsClosedSubgroup rho)
    (hμM' : IsIwasawaCompatibleMeasure K hK'.isCompact p' iU' l' μM')
    (hμM'' : IsIwasawaCompatibleMeasure K hK''.isCompact p'' iU'' l'' μM'')
    (hβ' : Continuous β' ∧ HasCompactSupport β' ∧ (∀ y, 0 ≤ β' y) ∧ ∫ y, β' y = 1)
    (hβ'' : Continuous β'' ∧ HasCompactSupport β'' ∧ (∀ y, 0 ≤ β'' y) ∧ ∫ y, β'' y = 1)
    (hws : IsWeylConjugation p l p' l' ws cs) (hwr : IsWeylConjugation p' l' p'' l'' wr cr)
    (hwu : IsWeylConjugation p l p'' l'' wu cu)
    (huv : weylParameter l cu π'' = weylParameter l (cr ≫ cs) π'')
    (Ms : (Fin n → ℝ) →
      inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
        inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β')
    (hMs : IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT iU' l' π' ws cs
      μM μM' e e' β β' Ms)
    (Mr : (Fin n' → ℝ) →
      inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β' →L[ℂ]
        inducedHilbertSpace K hK''.isCompact rho hsmooth hcalc p'' iU'' l'' μM'' e'' β'')
    (hMr : IsImaginaryIntertwiningOperator hK' hK'' rho hsmooth hcalc iU' l' a' r' hA' hT' iU''
      l'' π'' wr cr μM' μM'' e' e'' β' β'' Mr)
    (Mu : (Fin n → ℝ) →
      inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β →L[ℂ]
        inducedHilbertSpace K hK''.isCompact rho hsmooth hcalc p'' iU'' l'' μM'' e'' β'')
    (hMu : IsImaginaryIntertwiningOperator hK hK'' rho hsmooth hcalc iU l a r hA hT iU'' l''
      π'' wu cu μM μM'' e e'' β β'' Mu)
    {v : AdelicGroupPoints F G → ℂ}
    (hv : IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v)
    (h : inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β)
    (hh : ⇑(h : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β))
      =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l v)
    (x : Fin n → ℝ) :
    Mu x h = Mr (e'.symm (realWeylParameter l cs π' (e x))) (Ms x h) := by
  set y := e'.symm (realWeylParameter l cs π' (e x)) with hy
  set lam0 := imaginaryParameter F P (e x) with hlam0
  have hwlam : weylParameter l cs π' lam0 = imaginaryParameter F P' (e' y) := by
    rw [hlam0, weylParameter_imaginaryParameter, hy, LinearEquiv.apply_symm_apply]
  -- square integrability on the `P'` and `P''` sides
  have hL' : ∀ φ, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' φ →
      MemLp (inducedRestriction K p' l' φ) 2 (inducedL2Measure K hK'.isCompact l' μM' e' β') :=
    fun φ hφ => hL F G P' M' U' A' p' iU' l' a' r' hA' hT' π' hG hUR' hMul' hπ' K hK' rho hsmooth
      hcalc hKmax hrho μM' hμM' e' β' hβ'.1 hβ'.2.1 hβ'.2.2.1 φ hφ
  have hL'' : ∀ φ, IsSquareIntegrableInducedForm K hK''.isCompact rho hsmooth hcalc p'' iU''
      l'' φ → MemLp (inducedRestriction K p'' l'' φ) 2
        (inducedL2Measure K hK''.isCompact l'' μM'' e'' β'') :=
    fun φ hφ => hL F G P'' M'' U'' A'' p'' iU'' l'' a'' r'' hA'' hT'' π'' hG hUR'' hMul'' hπ''
      K hK'' rho hsmooth hcalc hKmax hrho μM'' hμM'' e'' β'' hβ''.1 hβ''.2.1 hβ''.2.2.1 φ hφ
  -- the expansion of `M(ws, λ) v`
  obtain ⟨ms, ψs, cos, Ds, hψs, hDs, hcos, Rs, hRs⟩ := hE F G P M U P' M' U' A A' p iU l a r hA
    hT p' iU' l' a' r' π' ws cs hG hUR hUR' hMul' hπ' hws K hK hK' rho hsmooth hcalc v hKmax
    hrho hv
  -- expansions of the `M(wr, μ) ψs q`, of one length and one domain, then flattened
  obtain ⟨m, χ, b, D', hχ, hD', hb, hbR⟩ := exists_uniform_expansions (S := Fin ms)
    (Set.range (imaginaryParameter F P'))
    (IsSquareIntegrableInducedForm K hK''.isCompact rho hsmooth hcalc p'' iU'' l'')
    (fun q mu g => hK'.intertwiningOperator hK'' iU' l' iU'' cr π'' wr (ψs q) mu g)
    (fun R mu => r'.IsRegularParameter hA' hT' R mu)
    (fun q => hE F G P' M' U' P'' M'' U'' A' A'' p' iU' l' a' r' hA' hT' p'' iU'' l'' a'' r''
      π'' wr cr hG hUR' hUR'' hMul'' hπ'' hwr K hK' hK'' rho hsmooth hcalc (ψs q) hKmax hrho
      (hψs q))
  obtain ⟨χf, bf, hχf, hbf, hbfsum⟩ := exists_flat_expansions χ b
  have hχf' : ∀ k, IsSquareIntegrableInducedForm K hK''.isCompact rho hsmooth hcalc p'' iU''
      l'' (χf k) := fun k => by
    obtain ⟨q, j, hk⟩ := hχf k
    rw [hk]
    exact hχ q j
  have hbf' : ∀ q k, IsMeromorphicInCoordinatesOn (bf q k) D' := fun q k => by
    rcases hbf q k with h0 | ⟨j, hj⟩
    · rw [h0]
      exact isMeromorphicInCoordinatesOn_zero_of (hb q (finProdFinEquiv.symm k).2)
    · rw [hj]
      exact hb q j
  have hbfR : ∀ q, ∃ R : ℝ, ∀ mu, r'.IsRegularParameter hA' hT' R mu → ∀ g,
      hK'.intertwiningOperator hK'' iU' l' iU'' cr π'' wr (ψs q) mu g =
        ∑ k, bf q k mu * χf k g := fun q => by
    obtain ⟨R, hR⟩ := hbR q
    exact ⟨R, fun mu hmu g => (hR mu hmu g).trans (hbfsum q mu g).symm⟩
  -- the expansion of `M(wu, λ) v`, transported to `(wr * ws, cr ≫ cs)`
  obtain ⟨mu', χ'', d'', D'', hχ'', hD'', hd'', Ru, hRu⟩ := hE F G P M U P'' M'' U'' A A'' p iU l
    a r hA hT p'' iU'' l'' a'' r'' π'' wu cu hG hUR hUR'' hMul'' hπ'' hwu K hK hK'' rho hsmooth
    hcalc v hKmax hrho hv
  have hRc : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK'' iU l iU'' (cr ≫ cs) π'' (wr * ws) v lam g =
        ∑ j, d'' j lam * χ'' j g := by
    refine ⟨Ru, fun lam hlam g => ?_⟩
    rw [← hRu lam hlam g]
    exact (hI F G P M U P'' M'' U'' p iU l p'' iU'' l'' π'' wu (wr * ws) cu (cr ≫ cs) hG
      r.isCompatible.parabolic hUR r.isCompatible.levi hMul r''.isCompatible.parabolic hUR''
      r''.isCompatible.levi hMul'' hπ'' hwu (hws.comp hwr) huv K hK hK'' rho hsmooth hcalc v
      hKmax hrho hv.1 lam g).symm
  -- the cocycle relation at `λ = i e(x)`
  have hcoc : ∀ g, ∑ j, d'' j lam0 * χ'' j g =
      ∑ q, cos q lam0 * ∑ k, bf q k (weylParameter l cs π' lam0) * χf k g :=
    hC F G P M U P' M' U' P'' M'' U'' A A' p iU l a r hA hT p' iU' l' a' r' hA' hT' π' p'' iU''
      l'' π'' ws wr cs cr hG hUR hUR' r''.isCompatible.parabolic hUR'' r''.isCompatible.levi
      hMul'' hπ' hπ'' hws hwr K hK hK' hK'' rho hsmooth hcalc v hKmax hrho hv.1 ms ψs cos Ds
      (fun q => (hψs q).1) hcos ⟨Rs, hRs⟩ (ms * m) χf bf D' hbf' hbfR mu' χ'' d'' D'' hd''
      hRc lam0 ⟨hDs ⟨e x, rfl⟩, hD'' ⟨e x, rfl⟩⟩ (by rw [hwlam]; exact hD' ⟨e' y, rfl⟩)
  -- classes of the expansion functions
  have hms : ∀ q, MemLp (inducedRestriction K p' l' (ψs q)) 2
      (inducedL2Measure K hK'.isCompact l' μM' e' β') := fun q => hL' _ (hψs q)
  have hmf : ∀ k, MemLp (inducedRestriction K p'' l'' (χf k)) 2
      (inducedL2Measure K hK''.isCompact l'' μM'' e'' β'') := fun k => hL'' _ (hχf' k)
  have hm'' : ∀ j, MemLp (inducedRestriction K p'' l'' (χ'' j)) 2
      (inducedL2Measure K hK''.isCompact l'' μM'' e'' β'') := fun j => hL'' _ (hχ'' j)
  set hq : Fin ms → inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β' :=
    fun q => ⟨(hms q).toLp _, toLp_mem_inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p'
      iU' l' μM' e' β' (hψs q) (hms q)⟩ with hqdef
  have hMsx : Ms x h = ∑ q, cos q lam0 • hq q := by
    apply Subtype.ext
    rw [map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator Ms hMs hv hψs hDs hcos
      ⟨Rs, hRs⟩ hms h hh x]
    simp [hq, hlam0]
  have hMrq : ∀ q, (Mr y (hq q) : Lp ℂ 2 (inducedL2Measure K hK''.isCompact l'' μM'' e'' β'')) =
      ∑ k, bf q k (imaginaryParameter F P' (e' y)) • (hmf k).toLp _ := fun q =>
    map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator Mr hMr (hψs q) hχf' hD' (hbf' q)
      (hbfR q) hmf (hq q) (hms q).coeFn_toLp y
  have hMux : (Mu x h : Lp ℂ 2 (inducedL2Measure K hK''.isCompact l'' μM'' e'' β'')) =
      ∑ j, d'' j lam0 • (hm'' j).toLp _ :=
    map_eq_sum_smul_toLp_of_isImaginaryIntertwiningOperator Mu hMu hv hχ'' hD'' hd''
      ⟨Ru, hRu⟩ hm'' h hh x
  apply Subtype.ext
  rw [hMsx, map_sum, Submodule.coe_sum, hMux]
  simp only [map_smul, Submodule.coe_smul, hMrq]
  have hrw : ∑ q, cos q lam0 • ∑ k, bf q k (imaginaryParameter F P' (e' y)) • (hmf k).toLp _ =
      ∑ k, (∑ q, cos q lam0 * bf q k (imaginaryParameter F P' (e' y))) • (hmf k).toLp _ := by
    simp only [Finset.smul_sum, smul_smul, Finset.sum_smul]
    exact Finset.sum_comm
  rw [hrw]
  refine Lp.ext ?_
  have h1 := (sum_smul_toLp_mem_inducedHilbertSpace K hK''.isCompact rho hsmooth hcalc p'' iU''
    l'' μM'' e'' β'' hχ'' hm'' (fun j => d'' j lam0)).2
  have h2 := (sum_smul_toLp_mem_inducedHilbertSpace K hK''.isCompact rho hsmooth hcalc p'' iU''
    l'' μM'' e'' β'' hχf' hmf
    (fun k => ∑ q, cos q lam0 * bf q k (imaginaryParameter F P' (e' y)))).2
  refine h1.trans (Filter.EventuallyEq.trans ?_ h2.symm)
  refine Filter.Eventually.of_forall fun z => ?_
  simp only [inducedRestriction]
  rw [hcoc, hwlam]
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

end Triple

end Langlands.Global

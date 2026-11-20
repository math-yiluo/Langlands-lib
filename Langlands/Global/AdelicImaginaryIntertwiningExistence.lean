import Langlands.Global.AdelicSpectralTransformInputs
import Langlands.Global.AdelicIntertwiningImaginaryUnitarityStatement
import Langlands.Global.AdelicInducedRestrictionMemLpStatement
import Langlands.Global.AdelicInducedL2Inner
import Langlands.Global.AdelicGroupPolish
import Langlands.Analysis.InnerProductGraphExtension
import Langlands.Analysis.MeasurePreservingLinearCoordinates

/-! # The operators `M(w, λ) : H_P → H_{P'}` from their unitarity on `A^2_P`

The unitarity of the intertwining operators on the imaginary axis
(`IntertwiningImaginaryUnitarityStatement`; Lapid 2011, p.312; Mœglin–Waldspurger IV.1.11 (b),
VI.2.1 (i)) and the square integrability of restrictions of elements of `A^2_P`
(`InducedRestrictionMemLpStatement`) imply `ImaginaryIntertwiningExistenceStatement`: for each
`λ ∈ i𝔞_P^*` there is a continuous complex-linear map `H_P → H_{P'}` that sends the class of
`v ∈ A^2_P` to the class of the value at `λ` of every supplied admissible finite expansion of
`M(w, λ) v` (compare Arthur 2005, Theorem 7.2 (a)). The map is an isometry on the closed span
of the classes that have such expansions and zero on its orthogonal complement; the proof does
not show that this closed span is all of `H_P`. -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct
open scoped CategoryTheory.MonObj TensorProduct InnerProductSpace Manifold

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
  Langlands.Analysis.Meromorphic

section Meromorphic

/-- A meromorphic function on `ℂⁿ` with domain of holomorphy `U` is meromorphic with domain of
holomorphy `U ∩ V` for every open dense `V`. -/
theorem isMeromorphicOn_inter {n : ℕ} {f : (Fin n → ℂ) → ℂ} {U V : Set (Fin n → ℂ)}
    (hf : IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f U) (hVo : IsOpen V) (hVd : Dense V) :
    IsMeromorphicOn 𝓘(ℂ, Fin n → ℂ) f (U ∩ V) := by
  obtain ⟨hUo, hUd, hhol, hloc⟩ := hf
  refine ⟨hUo.inter hVo, hUd.inter_of_isOpen_left hVd hUo,
    fun mu => (hhol mu).mono Set.inter_subset_left, fun s₀ => ?_⟩
  obtain ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, hgh⟩ := hloc s₀
  exact ⟨W, hWo, hWc, hsW, g, h, hg, hg0, hh, fun s hs => hgh s ⟨hs.1.1, hs.2⟩⟩

variable {X : Type*} [AddCommGroup X] [Module ℂ X]

/-- Meromorphy in coordinates with domain `U` gives meromorphy with domain `U ∩ V` when some
function is meromorphic in coordinates with domain `V`. -/
theorem isMeromorphicInCoordinatesOn_inter_of {f g : X → ℂ}
    {U V : Set X} (hf : IsMeromorphicInCoordinatesOn f U)
    (hg : IsMeromorphicInCoordinatesOn g V) : IsMeromorphicInCoordinatesOn f (U ∩ V) :=
  ⟨hf.1, fun n e => by
    rw [Set.preimage_inter]
    exact isMeromorphicOn_inter (hf.2 n e) (hg.2 n e).1 (hg.2 n e).2.1⟩

/-- The zero function is meromorphic in coordinates on every domain of holomorphy of a
meromorphic function. -/
theorem isMeromorphicInCoordinatesOn_zero_of {g : X → ℂ} {V : Set X}
    (hg : IsMeromorphicInCoordinatesOn g V) :
    IsMeromorphicInCoordinatesOn (fun _ => (0 : ℂ)) V := by
  refine ⟨hg.1, fun n e => ⟨(hg.2 n e).1, (hg.2 n e).2.1, fun mu => ?_, fun s₀ => ?_⟩⟩
  · simp only [Function.comp_def, map_zero]
    exact mdifferentiableOn_const
  · refine ⟨Set.univ, isOpen_univ, isConnected_univ, Set.mem_univ _, fun _ => 1, fun _ => 0,
      mdifferentiableOn_const, ⟨s₀, Set.mem_univ _, one_ne_zero⟩, fun mu => ?_, fun s _ => ?_⟩
    · simp only [map_zero]
      exact mdifferentiableOn_const
    · simp

/-- A finite family of functions meromorphic in coordinates with domain `DM` is meromorphic with
some domain `D ⊇ DM` such that intersecting with `D` preserves meromorphy in coordinates
(`D = DM` for a nonempty family, `D` the whole space for an empty one). -/
theorem exists_domain_of_isMeromorphicInCoordinatesOn {m : ℕ} {c : Fin m → X → ℂ} {DM : Set X}
    (hc : ∀ q, IsMeromorphicInCoordinatesOn (c q) DM) :
    ∃ D : Set X, DM ⊆ D ∧ (∀ q, IsMeromorphicInCoordinatesOn (c q) D) ∧
      ∀ (f : X → ℂ) (U : Set X), IsMeromorphicInCoordinatesOn f U →
        IsMeromorphicInCoordinatesOn f (U ∩ D) := by
  rcases Nat.eq_zero_or_pos m with rfl | hm
  · exact ⟨Set.univ, Set.subset_univ _, fun q => q.elim0, fun f U hf => by rwa [Set.inter_univ]⟩
  · exact ⟨DM, subset_rfl, hc, fun f U hf => isMeromorphicInCoordinatesOn_inter_of hf (hc ⟨0, hm⟩)⟩

end Meromorphic

section Coordinates

variable {F : Type} [Field F] [NumberField F] {P P' : GroupScheme (Spec (CommRingCat.of F))}

omit [NumberField F] in
/-- Transport of coordinates along a Lebesgue-measure-preserving coordinate change: if
`x ↦ e'⁻¹(L(e x))` preserves Lebesgue measure, then `e'' = L ∘ e` are coordinates on
`X^*(P') ⊗ ℝ`, and the weight `β'` in the coordinates `e'` is a weight `β''` in the coordinates
`e''` with the same properties and the same values at every `H ∈ Hom(X^*(P'), ℝ)`. -/
theorem exists_transported_coordinates {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (e' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P')
    (L : RealCharacterParameter F P →ₗ[ℝ] RealCharacterParameter F P') (β' : (Fin n → ℝ) → ℝ)
    (hβ' : Continuous β' ∧ HasCompactSupport β' ∧ (∀ y, 0 ≤ β' y) ∧ ∫ y, β' y = 1)
    (hmp : MeasurePreserving (fun x => e'.symm (L (e x))) volume volume) :
    ∃ (e'' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P') (β'' : (Fin n → ℝ) → ℝ),
      (∀ x, e'' x = L (e x)) ∧ Continuous β'' ∧ HasCompactSupport β'' ∧ (∀ y, 0 ≤ β'' y) ∧
      ∫ y, β'' y = 1 ∧
      ∀ H, β'' (parameterCoordinates F P' e'' H) = β' (parameterCoordinates F P' e' H) := by
  set τ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) := e'.symm.toLinearMap ∘ₗ L ∘ₗ e.toLinearMap with hτdef
  have hτ : MeasurePreserving τ volume volume := hmp
  have hsurj := Langlands.Analysis.surjective_of_measurePreserving_linearMap τ hτ
  have hinj : Function.Injective τ := LinearMap.injective_iff_surjective.2 hsurj
  set τe : (Fin n → ℝ) ≃ₗ[ℝ] (Fin n → ℝ) := LinearEquiv.ofBijective τ ⟨hinj, hsurj⟩ with hτe
  set e'' : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P' := τe.trans e' with he''def
  have he'' : ∀ x, e'' x = L (e x) := fun x => by
    show e' (e'.symm (L (e x))) = _
    exact e'.apply_symm_apply _
  set ρ : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ) :=
    Matrix.toLin' (LinearMap.toMatrix' (τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))).transpose
    with hρdef
  have hτeτ : (τe : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) = τ := by
    ext x : 1
    rfl
  have hdetρ : |LinearMap.det ρ| = 1 := by
    rw [hρdef, Langlands.Analysis.det_toLin'_transpose_toMatrix', LinearEquiv.det_coe_symm,
      abs_inv, hτeτ, Langlands.Analysis.abs_det_eq_one_of_measurePreserving τ hτ, inv_one]
  have hdet0 : LinearMap.det ρ ≠ 0 := by
    intro h
    rw [h, abs_zero] at hdetρ
    exact zero_ne_one hdetρ
  have hpc : ∀ H, parameterCoordinates F P' e' H = ρ (parameterCoordinates F P' e'' H) := by
    intro H
    have key := Langlands.Analysis.linearForm_comp_single_eq_transpose
      ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
      (τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ))
    have h1 : (fun j => ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
        ((τe.symm : (Fin n → ℝ) →ₗ[ℝ] (Fin n → ℝ)) (Pi.single j 1))) =
        parameterCoordinates F P' e' H := by
      funext j
      simp [parameterCoordinates, e'']
    have h2 : (fun i => ((realParameterPairing F P').flip H ∘ₗ e''.toLinearMap)
        (Pi.single i 1)) = parameterCoordinates F P' e'' H := by
      funext i
      simp [parameterCoordinates]
    rw [← h1, key, h2]
  set ρc : (Fin n → ℝ) ≃L[ℝ] (Fin n → ℝ) :=
    (LinearMap.equivOfDetNeZero ρ hdet0).toContinuousLinearEquiv with hρc
  have hρcρ : (ρc : (Fin n → ℝ) → (Fin n → ℝ)) = ρ := by
    ext x : 1
    simp [ρc, LinearMap.equivOfDetNeZero]
  refine ⟨e'', fun y => β' (ρ y), he'', hβ'.1.comp ρ.continuous_of_finiteDimensional, ?_,
    fun y => hβ'.2.2.1 _, ?_, fun H => by rw [hpc H]⟩
  · have := hβ'.2.1.comp_isClosedEmbedding ρc.toHomeomorph.isClosedEmbedding
    rwa [ContinuousLinearEquiv.coe_toHomeomorph, hρcρ] at this
  · rw [Langlands.Analysis.integral_comp_linearMap_of_abs_det_eq_one ρ hdetρ
      hβ'.1.aestronglyMeasurable, hβ'.2.2.2]

end Coordinates

/-- The unitarity of the intertwining operators on `A^2_P` at imaginary parameters and the
square integrability of restrictions of elements of `A^2_P` imply the existence of the operators
`M(w, λ) : H_P → H_{P'}` on the imaginary axis. -/
def ImaginaryIntertwiningExistenceBridgeStatement : Prop :=
  IntertwiningImaginaryUnitarityStatement → InducedRestrictionMemLpStatement →
    ImaginaryIntertwiningExistenceStatement

set_option maxHeartbeats 1000000 in
/-- Proof of `ImaginaryIntertwiningExistenceBridgeStatement`. For each `x`, the pairs
`([v], [∑ q, coeff q (i e(x)) • ψ q])` given by expansions of `M(w, λ) v` relate elements of
`H_P` and `H_{P'}` with equal inner products (the Gram identity of the unitarity statement at
`λ = i e(x)`, for the two expansions put side by side), so they lie in the graph of a continuous
linear operator. -/
theorem imaginaryIntertwiningExistenceBridge : ImaginaryIntertwiningExistenceBridgeStatement := by
  intro hU hL F _ _ G P M U P' M' U' A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    p' _ iU' l' _ a' r' _ _ _ hA' hT' π' hG hUR hUR' hMul hMul' hπ hπ' K hK hK' N d rho hsmooth
    hcalc hKmax hrho μM _ μM' _ hμM hμM' n n' e e' β β' hβ hβ' w cw hw hmp
  have : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  have : LocallyOfFiniteType P'.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p') ‹IsClosedImmersion p'.hom.hom.left›
  -- the coordinate change is a linear map `ℝⁿ → ℝ^{n'}` preserving Lebesgue measure: `n = n'`
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
  -- square integrability on the `P'` side
  have hL' : ∀ φ, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' φ →
      MemLp (inducedRestriction K p' l' φ) 2 (inducedL2Measure K hK'.isCompact l' μM' e' β') :=
    fun φ hφ => hL F G P' M' U' A' p' iU' l' a' r' hA' hT' π' hG hUR' hMul' hπ' K hK' rho hsmooth
      hcalc hKmax hrho μM' hμM' e' β' hβ'.1 hβ'.2.1 hβ'.2.2.1 φ hφ
  -- the relation at `x`
  let Rel : (Fin n → ℝ) →
      Set (inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β ×
        inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β') :=
    fun x => {s | ∃ v, IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l v ∧
      ∃ (m : ℕ) (ψ : Fin m → AdelicGroupPoints F G → ℂ)
        (coeff : Fin m → ComplexCharacterParameter F P → ℂ)
        (DM : Set (ComplexCharacterParameter F P)),
        (∀ q, IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc p' iU' l' (ψ q)) ∧
        Set.range (imaginaryParameter F P) ⊆ DM ∧
        (∀ q, IsMeromorphicInCoordinatesOn (coeff q) DM) ∧
        (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
          hK.intertwiningOperator hK' iU l iU' cw π' w v lam g = ∑ q, coeff q lam * ψ q g) ∧
        ⇑(s.1 : Lp ℂ 2 (inducedL2Measure K hK.isCompact l μM e β))
          =ᵐ[inducedL2Measure K hK.isCompact l μM e β] inducedRestriction K p l v ∧
        ⇑(s.2 : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β'))
          =ᵐ[inducedL2Measure K hK'.isCompact l' μM' e' β']
          inducedRestriction K p' l' fun g => ∑ q, coeff q (imaginaryParameter F P (e x)) * ψ q g}
  have hRel : ∀ x, ∀ s ∈ Rel x, ∀ t ∈ Rel x, ⟪s.2, t.2⟫_ℂ = ⟪s.1, t.1⟫_ℂ := by
    intro x s hs t ht
    obtain ⟨vs, hvs, ms, ψs, cs, DMs, hψs, hDMs, hcs, hRs, hs1, hs2⟩ := hs
    obtain ⟨vt, hvt, mt, ψt, ct, DMt, hψt, hDMt, hct, hRt, ht1, ht2⟩ := ht
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
    -- the classes of the restrictions of the `ψ2 i`
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
    have hs2' : (s.2 : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =
        ∑ i, co' 0 i lam0 • (hm2 i).toLp _ := by
      refine hZ 0 _ (hs2.trans (Filter.Eventually.of_forall fun y => ?_))
      simp only [inducedRestriction]
      rw [Fin.sum_univ_add]
      simp [co, ψ2]
    have ht2' : (t.2 : Lp ℂ 2 (inducedL2Measure K hK'.isCompact l' μM' e' β')) =
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
  have : CompleteSpace (inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β) := by
    unfold inducedHilbertSpace; infer_instance
  have : CompleteSpace
      (inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc p' iU' l' μM' e' β') := by
    unfold inducedHilbertSpace; infer_instance
  choose Mop hMop using fun x =>
    Langlands.Analysis.exists_continuousLinearMap_of_inner_eq (Rel x) (hRel x)
  refine ⟨Mop, ?_⟩
  intro v hv m ψ coeff DM hψ hDM hmero hagree h hh x
  have hm : ∀ q, MemLp (inducedRestriction K p' l' (ψ q)) 2
      (inducedL2Measure K hK'.isCompact l' μM' e' β') := fun q => hL' _ (hψ q)
  obtain ⟨hmemH, hae⟩ := sum_smul_toLp_mem_inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc
    p' iU' l' μM' e' β' hψ hm (fun q => coeff q (imaginaryParameter F P (e x)))
  have hrel := hMop x (h, ⟨_, hmemH⟩) ⟨v, hv, m, ψ, coeff, DM, hψ, hDM, hmero, hagree, hh, hae⟩
  rw [hrel]
  exact hae

end Langlands.Global

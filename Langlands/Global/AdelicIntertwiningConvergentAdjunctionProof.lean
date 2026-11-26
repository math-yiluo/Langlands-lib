import Langlands.Global.AdelicAdjunctionCutoffComparison
import Langlands.Global.AdelicIntertwiningScalarKernel
import Langlands.Representation.Plancherel.ParabolicRepresentedComparison

/-! # Adjunction of intertwining integrals in the region of convergence -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions AdelicGroupPoints
open ParabolicIwasawaMeasure LeftCosetSpace

private theorem integrate_conjugate_transport {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (T : X ≃ᵐ Y) {μX : Measure X} {μY : Measure Y} (hT : MeasurePreserving T μX μY)
    {f : X → ℂ} {g : Y → ℂ} (hf : Integrable f μX)
    (h : ∀ x, (starRingEnd ℂ) (g (T x)) = f x) :
    Integrable g μY ∧ (∫ x, f x ∂μX) = (starRingEnd ℂ) (∫ y, g y ∂μY) := by
  have heq := funext h
  have hComp : Integrable (g ∘ T) μX := Complex.conjCLE.integrable_comp_iff.mp (heq.symm ▸ hf)
  refine ⟨(hT.integrable_comp_emb T.measurableEmbedding).mp hComp, ?_⟩
  rw [← hT.integral_comp T.measurableEmbedding g, ← integral_conj, heq]

section Symmetry

variable {F : Type} [Field F] [NumberField F]
  {G P M : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  (p : P ⟶ G) (l : M ⟶ P) (K : Subgroup (AdelicGroupPoints F G)) (hKc : IsCompact (K : Set (AdelicGroupPoints F G)))
  (μM : Measure (AdelicGroupPoints F M)) [μM.IsHaarMeasure]
  {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (β : (Fin n → ℝ) → ℝ)
  {φ ψ : AdelicGroupPoints F G → ℂ}

private theorem inducedInnerProduct_conj_swap
    (h : Integrable (inducedInnerProductIntegrand K p l e β φ ψ)
      ((compactHaarProbability F G K hKc).prod
        (discreteQuotientMeasure (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) μM))) :
    Integrable (inducedInnerProductIntegrand K p l e β ψ φ)
      ((compactHaarProbability F G K hKc).prod
        (discreteQuotientMeasure (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) μM)) ∧
    (starRingEnd ℂ) (inducedInnerProduct K hKc p l μM e β φ ψ) =
      inducedInnerProduct K hKc p l μM e β ψ φ := by
  have hEq : (fun z => (starRingEnd ℂ) (inducedInnerProductIntegrand K p l e β φ ψ z)) =
      inducedInnerProductIntegrand K p l e β ψ φ := by
    funext z
    unfold inducedInnerProductIntegrand
    rw [← ofReal_inverseModulus l]
    simp only [map_mul, Complex.conj_ofReal, starRingEnd_self_apply]
    ring
  have h' : Integrable (inducedInnerProductIntegrand K p l e β ψ φ)
      ((compactHaarProbability F G K hKc).prod
        (discreteQuotientMeasure (rationalSubgroup F M) (isDiscrete_rationalSubgroup F M) μM)) :=
    hEq ▸ Complex.conjCLE.integrable_comp_iff.mpr h
  refine ⟨h', ?_⟩
  rw [inducedInnerProduct_eq_integral_prod _ _ _ _ _ _ _ h,
    inducedInnerProduct_eq_integral_prod _ _ _ _ _ _ _ h', ← integral_conj, hEq]

end Symmetry

set_option maxHeartbeats 2300000 in
/-- The two prescribed pairing integrands are integrable and their pairings agree throughout
some sufficiently source-regular region. -/
theorem intertwiningConvergentAdjunction : IntertwiningConvergentAdjunctionStatement := by
  classical
  intro F _ _ G P M U Q M' V A A' _ _ _ _ _ _ _ _ _ _ _ p _ iU l _ a r _ _ _ hA hT π
    q _ iV l' _ a' r' _ _ _ hA' hT' π' w c c' hG hU hV hπ hπ' hw hw'
    K hK hK' N d rho hsmooth hcalc hKmax hrho μM _ μM' _ hμM hμM' n e e' he
    β β' hβc hβs hβ hβ'c hβ's hβ' φ ψ hφ hψ
  let : LocallyOfFiniteType P.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := p) ‹IsClosedImmersion p.hom.hom.left›
  let : LocallyOfFiniteType Q.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := q) ‹IsClosedImmersion q.hom.hom.left›
  let : LocallyOfFiniteType V.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := iV ≫ q) ‹IsClosedImmersion (iV ≫ q).hom.hom.left›
  let : LocallyOfFiniteType U.X.hom := IsClosedSubgroup.locallyOfFiniteType
    (j := iU ≫ p) ‹IsClosedImmersion (iU ≫ p).hom.hom.left›
  let : IsAffineHom V.X.hom := isAffineHom_of_isAffine _
  let : IsIso (subgroupMultiplication l iU) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r hG hU
  let hmul' : IsIso (subgroupMultiplication l' iV) :=
    Langlands.Plancherel.parabolicRadical_isIso_subgroupMultiplication r' hG hV
  let : IsIso (subgroupMultiplication l' iV) := hmul'
  obtain ⟨R, hR⟩ := intertwiningScalarKernelIntegrable r hA hT hG hU r'.isCompatible.parabolic hV
    r'.isCompatible.levi hmul' hw hK rho hsmooth hcalc hKmax hrho
  refine ⟨R, fun s hs => ?_⟩
  let lam := realChart e s
  let nu := weylParameter l c π' (realChart e (fun t => -(starRingEnd ℂ) (s t)))
  have hφc : Continuous φ := hφ.1.2.1.1
  have hψc : Continuous ψ := hψ.1.2.1.1
  have hbal := intertwiningLeviHaarBalance F G P M U Q M' V A A' p iU l a r q iV l' a' r' w c hG hU hV hw
  obtain ⟨hJm, hJi⟩ := integrable_normalizedAdjunctionKernel iU l iV l' hK c w lam hU hφ.1.1 hψ.1.1
    hφ.2.1 hψ.2.1 hw r.isCompatible.levi.isConnectedReductive r'.isCompatible.levi.isConnectedReductive
    hφc hψc (by simpa only [sq_norm_normalizedLeviValue] using hφ.2.2)
    (by simpa only [sq_norm_normalizedLeviValue] using hψ.2.2) (hR lam hs)
  obtain ⟨hT, hS, hTS⟩ := integrate_adjunction_cutoffs iU l iV l' r hK hK' π' w hw lam hU hV
    hφ.1.1 hψ.1.1 hφ.2.1 hψ.2.1 e e' hG r'.isCompatible.parabolic r'.isCompatible.levi
    r'.isCompatible.levi.isConnectedReductive hπ' he hφc hψc μM' hμM' β β' hβc hβs hβ hβ'c hβ's hβ' hbal hJm hJi
  obtain ⟨hFint, hFeq⟩ := refoldAdjunctionKernel iU l iV l' hK hK' π' w hw φ ψ lam hU hV
    hφ.1.1 hψ.1.1 (r := r) hG r'.isCompatible.parabolic hφc hψc μM' hμM' e' β' hβ'c hT
  let Gₐ := AdelicGroupPoints F G
  let wA := innerAdelicPoint F G w
  let Γ := adjunctionRationalSubgroup (p := p) (q := q) wA
  let Γ' := adjunctionRationalSubgroup (p := q) (q := p) (innerAdelicPoint F G w⁻¹)
  let Bs : Gₐ → ℂ := fun g => (β (hK.heightCoordinates e (wA⁻¹ * g)) : ℂ) * adjunctionKernel l hK hK' c π' w φ ψ lam g
  let Br : Gₐ → ℂ := fun g => (β (hK.heightCoordinates e g) : ℂ) * adjunctionKernel l' hK' hK c' π w⁻¹ ψ φ nu g
  let μΓ := discreteQuotientMeasure Γ ((isDiscrete_rationalSubgroup F G).mono inf_le_left) (Measure.haar : Measure Gₐ)
  let μΓ' := discreteQuotientMeasure Γ' ((isDiscrete_rationalSubgroup F G).mono inf_le_left) (Measure.haar : Measure Gₐ)
  obtain ⟨T, hTval, hTmeasure⟩ := exists_measurePreserving_adjunctionTranslate (p := p) (q := q) w
  have hBs : ∀ d ∈ Γ, ∀ g, Bs (d * g) = Bs g :=
    sourceAdjunctionCutoff_invariant iU l iV l' hK hK' π' w lam hU hV hφ.1.1 hψ.1.1 e β
  have hBr : ∀ d ∈ Γ', ∀ g, Br (d * g) = Br g :=
    targetAdjunctionCutoff_invariant iV l' iU l hK' hK π w⁻¹ nu hV hU hψ.1.1 hφ.1.1 e β
  have hReflect (u : LeftCosetSpace Γ) : (starRingEnd ℂ) (Br (T u).out) = Bs u.out := by
    obtain ⟨g, rfl⟩ := mk_surjective Γ u
    rw [hTval, out_mk_of_invariant Γ' Br hBr, out_mk_of_invariant Γ Bs hBs]
    unfold Br Bs
    rw [map_mul, Complex.conj_ofReal, conj_adjunctionKernel_reverse l l' hK hK' c π' w φ ψ r e s π hπ hπ' c' hw hw']
  have hS' : Integrable (fun u : LeftCosetSpace Γ => Bs u.out) μΓ := hS
  obtain ⟨hRint, hReq⟩ := integrate_conjugate_transport T hTmeasure (g := fun z : LeftCosetSpace Γ' => Br z.out) hS' hReflect
  have hRint' : Integrable (fun u : LeftCosetSpace Γ' => Br u.out) μΓ' := hRint
  obtain ⟨hBint, hBeq⟩ := refoldAdjunctionKernel iV l' iU l hK' hK π w⁻¹ hw' ψ φ nu hV hU
    hψ.1.1 hφ.1.1 (r := r') hG r.isCompatible.parabolic hψc hφc μM hμM e β hβc hRint'
  obtain ⟨hI, hEq⟩ := inducedInnerProduct_conj_swap p l K hK.isCompact μM e β hBint
  exact ⟨hFint, hI, hFeq.trans (hTS.trans (hReq.trans ((congrArg (starRingEnd ℂ) hBeq.symm).trans hEq)))⟩

end Langlands.Global

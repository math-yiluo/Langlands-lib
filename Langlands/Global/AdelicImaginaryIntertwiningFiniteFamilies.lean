import Langlands.Global.AdelicInducedRestrictionFaithful

/-! # Application of the supplied imaginary intertwiner to a finite family -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F]
  {G P M U Q M' V : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom] [IsAffine U.X.left]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom] [IsAffine V.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)}
  (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
  (hsmooth : SmoothOfRelativeDimension d G.X.hom)
  (hcalc : AdelicDifferentialCommutator F G hsmooth)
  (iU : U ⟶ P) (l : M ⟶ P) [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)
  (iV : V ⟶ Q) (l' : M' ⟶ Q) [IsClosedImmersion (iV ≫ q).hom.hom.left]
  (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X) (cw : M' ⟶ M)
  (μM : Measure (AdelicGroupPoints F M)) (μM' : Measure (AdelicGroupPoints F M'))
  {n n' : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
  (e' : (Fin n' → ℝ) ≃ₗ[ℝ] RealCharacterParameter F Q)
  (β : (Fin n → ℝ) → ℝ) (β' : (Fin n' → ℝ) → ℝ)

local notation "Functions" => AdelicGroupPoints F G → ℂ
local notation "A₂" => IsSquareIntegrableInducedForm K hK.isCompact rho hsmooth hcalc p iU l
local notation "A₂'" => IsSquareIntegrableInducedForm K hK'.isCompact rho hsmooth hcalc q iV l'
local notation "μ" => inducedL2Measure K hK.isCompact l μM e β
local notation "μ'" => inducedL2Measure K hK'.isCompact l' μM' e' β'
local notation "H" => inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β
local notation "H'" => inducedHilbertSpace K hK'.isCompact rho hsmooth hcalc q iV l' μM' e' β'

/-- A finite expansion of the regular-region `intertwiningOperator` in square-integrable target
forms, with coefficients holomorphic on the imaginary axis. The operator untwists the integral
by the inverse target height factor at the Weyl-transported parameter. -/
def IsRegularIntertwiningExpansion (v : Functions) {m : ℕ} (ψ : Fin m → Functions)
    (coeff : Fin m → ComplexCharacterParameter F P → ℂ)
    (D : Set (ComplexCharacterParameter F P)) : Prop :=
  (∀ j, A₂' (ψ j)) ∧ Set.range (imaginaryParameter F P) ⊆ D ∧
    (∀ j, IsMeromorphicInCoordinatesOn (coeff j) D) ∧
    ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → ∀ g,
      hK.intertwiningOperator hK' iU l iV cw π' w v lam g = ∑ j, coeff j lam * ψ j g

omit [IsAffine U.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- On a finite linear combination the supplied Hilbert operator has the representative obtained
by combining the pointwise expansions. The coefficients of the combination are fixed at this
parameter and need no analytic regularity. -/
theorem IsImaginaryIntertwiningOperator.ae_apply_finite_sum
    {Mop : (Fin n → ℝ) → H →L[ℂ] H'}
    (hMop : IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT
      iV l' π' w cw μM μM' e e' β β' Mop)
    {k : ℕ} {v : Fin k → Functions} (hv : ∀ j, A₂ (v j))
    (hL : ∀ j, MemLp (inducedRestriction K p l (v j)) 2 μ)
    {m : Fin k → ℕ} {ψ : ∀ j, Fin (m j) → Functions}
    {coeff : ∀ j, Fin (m j) → ComplexCharacterParameter F P → ℂ}
    {D : Fin k → Set (ComplexCharacterParameter F P)}
    (hExp : ∀ j, IsRegularIntertwiningExpansion hK hK' rho hsmooth hcalc iU l r hA hT iV l' π' w cw
      (v j) (ψ j) (coeff j) (D j))
    (x : Fin n → ℝ) (b : Fin k → ℂ) (u : H)
    (hu : ⇑(u : Lp ℂ 2 μ) =ᵐ[μ] inducedRestriction K p l (fun g => ∑ j, b j * v j g)) :
    ⇑(Mop x u : Lp ℂ 2 μ') =ᵐ[μ'] inducedRestriction K q l'
      (fun g => ∑ j, b j * ∑ t, coeff j t (imaginaryParameter F P (e x)) * ψ j t g) := by
  let z (j : Fin k) : H :=
    ⟨(hL j).toLp _, toLp_mem_inducedHilbertSpace K hK.isCompact rho hsmooth hcalc p iU l μM e β
      (hv j) (hL j)⟩
  have huz : u = ∑ j, b j • z j := by
    apply Subtype.ext
    simp only [Submodule.coe_sum, Submodule.coe_smul]
    exact Lp.ext (hu.trans (sum_smul_toLp_mem_inducedHilbertSpace K hK.isCompact rho hsmooth
      hcalc p iU l μM e β hv hL b).2.symm)
  rw [huz, map_sum]
  simp only [map_smul, Submodule.coe_sum, Submodule.coe_smul]
  have hterms : ∀ j ∈ (Finset.univ : Finset (Fin k)),
      ⇑(b j • (Mop x (z j) : Lp ℂ 2 μ')) =ᵐ[μ'] b j • inducedRestriction K q l'
        (fun g => ∑ t, coeff j t (imaginaryParameter F P (e x)) * ψ j t g) := by
    intro j _
    obtain ⟨hψ, hD, hm, hreg⟩ := hExp j
    exact (Lp.coeFn_smul _ _).trans ((hMop (v j) (hv j) (m j) (ψ j) (coeff j) (D j)
      hψ hD hm hreg (z j) (hL j).coeFn_toLp x).const_smul (b j))
  refine (Lp.coeFn_finsetSum _ _).trans ((eventuallyEq_sum hterms).trans ?_)
  exact Filter.Eventually.of_forall fun g => by simp [inducedRestriction, Finset.sum_apply]

omit [IsAffine U.X.left] [IsClosedImmersion p.hom.hom.left] in
/-- The Hilbert-space Weyl relation between two finite presentations gives an equality of actual
adelic functions at the given imaginary parameter. -/
theorem IsImaginaryIntertwiningOperator.pointwise_eq_of_finite_sum
    [μM'.IsHaarMeasure] (hG : IsConnectedReductive G) (hq : IsParabolicSubgroup q)
    (hV : LeviSubgroup.IsGeometricUnipotentRadical iV) (hl' : IsRationalLeviSubgroup l')
    (hmul : IsIso (subgroupMultiplication l' iV))
    (hβc : Continuous β') (hβs : HasCompactSupport β') (hβ0 : ∀ y, 0 ≤ β' y)
    (hβint : ∫ y, β' y = 1)
    {Mop : (Fin n → ℝ) → H →L[ℂ] H'}
    (hMop : IsImaginaryIntertwiningOperator hK hK' rho hsmooth hcalc iU l a r hA hT
      iV l' π' w cw μM μM' e e' β β' Mop)
    {k k' : ℕ} {v : Fin k → Functions} {v' : Fin k' → Functions}
    (hv : ∀ j, A₂ (v j)) (hv' : ∀ j, A₂' (v' j))
    (hL : ∀ j, MemLp (inducedRestriction K p l (v j)) 2 μ)
    {m : Fin k → ℕ} {ψ : ∀ j, Fin (m j) → Functions}
    {coeff : ∀ j, Fin (m j) → ComplexCharacterParameter F P → ℂ}
    {D : Fin k → Set (ComplexCharacterParameter F P)}
    (hExp : ∀ j, IsRegularIntertwiningExpansion hK hK' rho hsmooth hcalc iU l r hA hT iV l' π' w cw
      (v j) (ψ j) (coeff j) (D j))
    (x : Fin n → ℝ) (b : Fin k → ℂ) (b' : Fin k' → ℂ) (u : H)
    (hu : ⇑(u : Lp ℂ 2 μ) =ᵐ[μ] inducedRestriction K p l (fun g => ∑ j, b j * v j g))
    (hu' : ⇑(Mop x u : Lp ℂ 2 μ') =ᵐ[μ'] inducedRestriction K q l'
      (fun g => ∑ j, b' j * v' j g)) :
    (fun g => ∑ j, b' j * v' j g) =
      fun g => ∑ j, b j * ∑ t, coeff j t (imaginaryParameter F P (e x)) * ψ j t g := by
  let V' := squareIntegrableInducedForms q l' hK'.isCompact rho hsmooth hcalc iV
  have hsum : ∀ {len : ℕ} {f : Fin len → Functions}, (∀ j, f j ∈ V') →
      ∀ s : Fin len → ℂ, (fun g => ∑ j, s j * f j g) ∈ V' := by
    intro len f hf s
    have heq : (fun g => ∑ j, s j * f j g) = ∑ j, s j • f j := by
      funext g
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [heq]
    exact V'.sum_mem fun j _ => V'.smul_mem (s j) (hf j)
  apply eq_of_ae_inducedRestriction (μM := μM') (e := e') hK' hG hq hV hl' hmul hβc hβs hβ0 hβint
    (hsum hv' b') (hsum (fun j => hsum (hExp j).1
      (fun t => coeff j t (imaginaryParameter F P (e x)))) b)
  exact hu'.symm.trans (IsImaginaryIntertwiningOperator.ae_apply_finite_sum
    hK hK' rho hsmooth hcalc iU l r hA hT iV l' π' w cw μM μM' e e' β β'
      hMop hv hL hExp x b u hu)

end Langlands.Global.AdelicGroupPoints

import Langlands.Global.AdelicAdjunctionIwasawaUnfold
import Langlands.Global.AdelicEisensteinCompactBounds
import Langlands.Global.AdelicWeylPositiveTransport

/-! # Twisted products for the convergence-region adjunction -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Topology
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Langlands.Global.AdelicGroupPoints

open Langlands.GroupScheme Langlands.Automorphic.GroupSchemeFunctions
open InducedInnerProductIntegrable ParabolicIwasawaMeasure

variable {F : Type} [Field F] [NumberField F]
  {G P U M Q V M' : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  [IsAffine P.X.left] [LocallyOfFiniteType P.X.hom] [IsAffine U.X.left]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  [IsAffine Q.X.left] [LocallyOfFiniteType Q.X.hom] [IsAffine V.X.left]
  [IsAffine M'.X.left] [LocallyOfFiniteType M'.X.hom]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] (iU : U ⟶ P) (l : M ⟶ P)
  [IsClosedImmersion (iU ≫ p).hom.hom.left]
  {q : Q ⟶ G} [IsClosedImmersion q.hom.hom.left] (iV : V ⟶ Q) (l' : M' ⟶ Q)
  [IsClosedImmersion (iV ≫ q).hom.hom.left]
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K) (hK' : IsIwasawaCompact q K)
  (c : M' ⟶ M) (π' : Q ⟶ M') (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
  (φ ψ : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F P)

local notation "Gₐ" => (AdelicGroupPoints F G)
local notation "wA" => (innerAdelicPoint F G w)
local notation "mP" => (fun m => map F P G p (map F M P l m))
local notation "mQ" => (fun m => map F Q G q (map F M' Q l' m))
local notation "heightCoords" => (fun h e g => parameterCoordinates _ _ e (IsIwasawaCompact.height h g))

/-- The twisted product on the common quotient, before inserting a split-component weight. -/
def adjunctionKernel (g : Gₐ) : ℂ :=
  hK.parameterTwist φ lam (wA⁻¹ * g) * hK'.heightPower (-weylParameter l c π' lam) g *
    (starRingEnd ℂ) (ψ g)

theorem continuous_adjunctionKernel (hφc : Continuous φ) (hψc : Continuous ψ) :
    Continuous (adjunctionKernel l hK hK' c π' w φ ψ lam) :=
  (((hK.continuous_parameterTwist hφc lam).comp (continuous_const.mul continuous_id)).mul
    (hK'.continuous_heightPower _)).mul (continuous_star.comp hψc)

/-- The Iwasawa height is left invariant under the inducing subgroup. -/
theorem IsIwasawaCompact.height_leftInvariant_parabolic
    (hU : IsUnipotent U) :
    ∀ d ∈ parabolicQuotientSubgroup F p iU l, ∀ g, hK.height (d * g) = hK.height g := by
  apply LeftCosetSpace.invariant_sup _ hK.height
  · rintro d ⟨x, rfl⟩ g
    exact hK.height_unipotent_mul hU iU x g
  · rintro d ⟨x, rfl⟩ g
    change hK.height (map F M G (l ≫ p) (rational F M x) * g) = _
    rw [map_comp_apply_of_hom l, map_rational, hK.height_rational_mul]

include hK hK' in
/-- Any simultaneous left translation by the two inducing subgroups preserves the product. -/
theorem adjunctionKernel_leftInvariant (hU : IsUnipotent U) (hV : IsUnipotent V)
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hψ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F q iV l') ψ)
    {d : Gₐ} (hd : d ∈ parabolicQuotientSubgroup F q iV l')
    (hd' : wA⁻¹ * d * wA ∈ parabolicQuotientSubgroup F p iU l) (g : Gₐ) :
    adjunctionKernel l hK hK' c π' w φ ψ lam (d * g) =
      adjunctionKernel l hK hK' c π' w φ ψ lam g := by
  unfold adjunctionKernel IsIwasawaCompact.parameterTwist IsIwasawaCompact.heightPower
  rw [show wA⁻¹ * (d * g) = (wA⁻¹ * d * wA) * (wA⁻¹ * g) by group,
    hφ _ hd', hψ _ hd, hK.height_leftInvariant_parabolic iU l hU _ hd',
    hK'.height_leftInvariant_parabolic iV l' hV _ hd]

private theorem pairing_realToComplex (x : RealCharacterParameter F P) (H : RealCharacterDual F P) :
    complexParameterPairing F P (realToComplexParameter P x) H =
      (realParameterPairing F P x H : ℂ) := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ => rw [realToComplexParameter_tmul, complexParameterPairing_tmul,
      realParameterPairing_tmul, Complex.ofReal_mul]
  | add u v hu hv => simp only [map_add, LinearMap.add_apply, hu, hv, Complex.ofReal_add]

private theorem conj_pairing_realChart {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P)
    (s : Fin n → ℂ) (H : RealCharacterDual F P) :
    (starRingEnd ℂ) (complexParameterPairing F P (realChart e (fun j => -(starRingEnd ℂ) (s j))) H) =
      -(complexParameterPairing F P (realChart e s) H) := by
  simp only [realChart_apply, map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply,
    pairing_realToComplex, smul_eq_mul, neg_mul, map_neg, map_mul,
    Complex.conj_ofReal, starRingEnd_self_apply, Finset.sum_neg_distrib]

variable {A : CommGroupScheme (Spec (CommRingCat.of F))} {a : A.toGrp ⟶ M}
  [IsAffineHom G.X.hom] (r : ParabolicRootPresentation p l a)

include r in
/-- Reflection conjugates the product after translating by the inverse Weyl representative. -/
theorem conj_adjunctionKernel_reverse {n : ℕ}
    (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F P) (s : Fin n → ℂ)
    (π : P ⟶ M) (hπ : l ≫ π = 𝟙 M) (hπ' : l' ≫ π' = 𝟙 M')
    (c' : M ⟶ M') (hw : IsWeylConjugation p l q l' w c)
    (hw' : IsWeylConjugation q l' p l w⁻¹ c') (g : Gₐ) :
    (starRingEnd ℂ) (adjunctionKernel l' hK' hK c' π w⁻¹ ψ φ
      (weylParameter l c π' (realChart e (fun j => -(starRingEnd ℂ) (s j)))) (wA⁻¹ * g)) =
      adjunctionKernel l hK hK' c π' w φ ψ (realChart e s) g := by
  let t : Fin n → ℂ := fun j => -(starRingEnd ℂ) (s j)
  let ν := weylParameter l c π' (realChart e t)
  have hp : Mono p.hom.hom := Over.mono_of_mono_left _
  have : Mono p := (Grp.forget _).mono_of_mono_map (f := p) hp
  have hInv : weylParameter l' c' π ν = realChart e t :=
    weylParameter_weylParameter_of_inv r hπ hπ' hw hw' (realChart e t)
  have h1 : (starRingEnd ℂ) (hK'.heightPower ν g) =
      hK'.heightPower (-weylParameter l c π' (realChart e s)) g := by
    unfold IsIwasawaCompact.heightPower ν
    rw [map_neg, LinearMap.neg_apply, weylParameter_pairing, weylParameter_pairing,
      ← Complex.exp_conj, conj_pairing_realChart]
  have h2 : (starRingEnd ℂ) (hK.heightPower (-realChart e t) (wA⁻¹ * g)) =
      hK.heightPower (realChart e s) (wA⁻¹ * g) := by
    unfold IsIwasawaCompact.heightPower
    rw [map_neg, LinearMap.neg_apply, ← Complex.exp_conj, map_neg]
    change Complex.exp (-((starRingEnd ℂ) (complexParameterPairing F P (realChart e t)
      (hK.height (wA⁻¹ * g))))) = _
    rw [conj_pairing_realChart, neg_neg]
  change (starRingEnd ℂ) (adjunctionKernel l' hK' hK c' π w⁻¹ ψ φ ν (wA⁻¹ * g)) = _
  unfold adjunctionKernel IsIwasawaCompact.parameterTwist
  rw [innerPoint_inv, inv_inv, mul_inv_cancel_left, hInv]
  simp only [map_mul, h1, h2, starRingEnd_self_apply]
  ring

end Langlands.Global.AdelicGroupPoints

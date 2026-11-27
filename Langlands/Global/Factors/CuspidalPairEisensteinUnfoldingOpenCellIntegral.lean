import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingLeviIntegral
import Langlands.Global.Factors.CuspidalPairEisensteinUnfoldingRadicalHaar

/-! # The open cell contributes the open-cell integral

For the open cell `J₀`, the unfolded integral of `φ_s(w n) conj(ψ_N(n))` over a fundamental domain
of `Λ_(J₀)(F)` in `N₀(𝔸)`, for the normalized Haar measure, is `κ` times the open-cell integral
`openCellIntegral ψ φ s`, where `κ > 0` compares the normalized Haar measure of the radical with
`openCellHaar`. See the paired Markdown. -/

noncomputable section

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

universe u

open NumberField MeasureTheory Set
open scoped NNReal ENNReal

namespace Langlands.Global.CuspidalPairEisenstein.Unfolding

open RankinSelbergGlobal RowEchelon LeftCosetSpace

attribute [local instance] radicalMatrixMeasurableSpace radicalMatrixBorelSpace

variable {F : Type u} [Field F] [NumberField F] [CompactSpace (AdeleQuotient F)] {r t : ℕ}
  {T : Automorphic.CuspidalOperatorRealization F r}
  {T' : Automorphic.CuspidalOperatorRealization F t} {φ : AdelicGL F (r + t + 2) → ℂ}

/-- The open cell `J₀ = {0, …, t}` as a pivot index. -/
abbrev openIndex (r t : ℕ) : PivotIndex (r + t + 2) (r + 1) :=
  ⟨openPivots r t, card_openPivots⟩

omit [CompactSpace (AdeleQuotient F)] in
theorem toMat_radicalHom_eq (n : Radical F r t) :
    toMat F _ (radicalHom F r t n) = openCellUnipotent F r t n.toAdd :=
  Units.ext (toMat_radicalHom F r t n)

omit [CompactSpace (AdeleQuotient F)] in
/-- The open-cell integrand in the coordinates `n = diag(m) u'(Y)`. -/
theorem cellIntegrand_openIndex (ψ : AddChar (Adeles F) ℂ) (s : ℂ) (m : LeviPart F r t)
    (n : Radical F r t) :
    cellIntegrand φ s ψ (openIndex r t) (leviHom F r t m * radicalHom F r t n) =
      leviIntegrand (twisted φ s) ψ (openCellWeyl F r t * openCellUnipotent F r t n.toAdd) m *
        starRingEnd ℂ (ψ (n.toAdd (Fin.last t) 0)) := by
  rw [cellIntegrand, leviIntegrand, genericChar_mul, genericChar_leviHom, genericChar_radicalHom,
    map_mul (toMat F _), toMat_radicalHom_eq, map_mul, map_mul]
  have h : AdelicGL.rational F (r + t + 2) (cellRep r t F (openIndex r t).1) =
      openCellWeyl F r t :=
    rational_cellRep_openPivots r t F
  rw [h, ← mul_assoc (openCellWeyl F r t), openCellWeyl_mul_leviHom, mul_assoc]
  ring

/-- The inner integral over the block diagonal group of the open-cell integrand. -/
theorem setIntegral_fdM_cellIntegrand (hφ : IsSection T T' φ) (s : ℂ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) (n : Radical F r t)
    (hint : Integrable (fun m => cellIntegrand φ s ψ (openIndex r t)
      (leviHom F r t m * radicalHom F r t n)) ((haarM F r t).restrict (fdM F r t))) :
    ∫ m in fdM F r t, cellIntegrand φ s ψ (openIndex r t)
        (leviHom F r t m * radicalHom F r t n) ∂haarM F r t =
      leviWhittaker F r t ψ (fun g => φ g * heightPower F r t s g)
          (openCellWeyl F r t * openCellUnipotent F r t n.toAdd) *
        starRingEnd ℂ (ψ (n.toAdd (Fin.last t) 0)) := by
  have hunit : starRingEnd ℂ (ψ (n.toAdd (Fin.last t) 0)) * ψ (n.toAdd (Fin.last t) 0) = 1 := by
    rw [Complex.conj_mul', hψ.2.2.2]
    simp
  have hfun : ∀ m, cellIntegrand φ s ψ (openIndex r t) (leviHom F r t m * radicalHom F r t n) *
      ψ (n.toAdd (Fin.last t) 0) =
      leviIntegrand (twisted φ s) ψ (openCellWeyl F r t * openCellUnipotent F r t n.toAdd) m := by
    intro m
    rw [cellIntegrand_openIndex, mul_assoc, hunit, mul_one]
  have hint' : IntegrableOn (leviIntegrand (twisted φ s) ψ
      (openCellWeyl F r t * openCellUnipotent F r t n.toAdd)) (fdM F r t) (haarM F r t) :=
    (hint.mul_const (ψ (n.toAdd (Fin.last t) 0))).congr (ae_of_all _ hfun)
  simp_rw [cellIntegrand_openIndex]
  rw [integral_mul_const]
  exact congrArg (fun z => z * starRingEnd ℂ (ψ (n.toAdd (Fin.last t) 0)))
    (setIntegral_fdM_eq_leviWhittaker (continuous_twisted hφ s)
      (fun c0 hc0 x => twisted_rational_mul hφ s c0 hc0 x) ψ hψ _ hint')

omit [CompactSpace (AdeleQuotient F)] in
theorem openCellIntegral_eq (ψ : AddChar (Adeles F) ℂ) (s : ℂ) :
    openCellIntegral ψ φ s = ∫ Y, leviWhittaker F r t ψ (fun g => φ g * heightPower F r t s g)
        (openCellWeyl F r t * openCellUnipotent F r t Y) *
      starRingEnd ℂ (ψ (Y (Fin.last t) 0)) ∂openCellHaar F r t := by
  unfold openCellIntegral
  simp only [openCellUnipotent_superdiagonal_sum]

/-- **The open cell.** -/
theorem setIntegral_cellDomain_openIndex (hφ : IsSection T T' φ) (s : ℂ)
    (ψ : AddChar (Adeles F) ℂ) (hψ : IsStandardAdditiveCharacter F ψ) {κ : ℝ≥0}
    (hκ : (haarN F r t).map (radicalCoord F r t) = κ • openCellHaar F r t)
    (hint : IntegrableOn (cellIntegrand φ s ψ (openIndex r t)) (cellDomain (openIndex r t))
      (haarH F r t)) :
    ∫ x in cellDomain (openIndex r t), cellIntegrand φ s ψ (openIndex r t) x ∂haarH F r t =
      ((κ : ℝ) : ℂ) * openCellIntegral ψ φ s := by
  have hinv : ∀ l ∈ openLattice F r t, ∀ x, cellIntegrand φ s ψ (openIndex r t) (l * x) =
      cellIntegrand φ s ψ (openIndex r t) x := fun l hl x =>
    cellIntegrand_patternRational_mul hφ s ψ hψ.2.2.1 (openIndex r t) hl x
  have hD : ∀ x, ∃! l : openLattice F r t,
      (l : unipotentAdelic F (r + t + 2)) * x ∈ cellDomain (openIndex r t) := fun x =>
    existsUnique_mem_cellDomain (openIndex r t) x
  obtain ⟨hprod, heq⟩ := setIntegral_eq_iterated_open F r t
    (cellIntegrand φ s ψ (openIndex r t)) hinv (measurableSet_cellDomain _) hD hint
  rw [heq]
  have h2 : ∫ n, ∫ m in fdM F r t, cellIntegrand φ s ψ (openIndex r t)
      (leviHom F r t m * radicalHom F r t n) ∂haarM F r t ∂haarN F r t =
      ∫ n, (fun Y => leviWhittaker F r t ψ (fun g => φ g * heightPower F r t s g)
          (openCellWeyl F r t * openCellUnipotent F r t Y) *
        starRingEnd ℂ (ψ (Y (Fin.last t) 0))) n.toAdd ∂haarN F r t :=
    integral_congr_ae (hprod.prod_right_ae.mono fun n hn =>
      setIntegral_fdM_cellIntegrand hφ s ψ hψ n hn)
  rw [h2, openCellIntegral_eq]
  exact integral_haarN_eq F r t hκ (fun Y => leviWhittaker F r t ψ
    (fun g => φ g * heightPower F r t s g) (openCellWeyl F r t * openCellUnipotent F r t Y) *
      starRingEnd ℂ (ψ (Y (Fin.last t) 0)))

end Langlands.Global.CuspidalPairEisenstein.Unfolding

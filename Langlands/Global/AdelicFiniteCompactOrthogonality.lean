import Langlands.Global.AdelicFiniteCompactPairingComparisonStatement
import Langlands.Global.AdelicStandardPositiveLog

/-! # Transport of Levi orthogonality across a finite change of compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions

section Transfer

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
  [IsClosedImmersion (fam.p J).hom.hom.left]
  {K₁ K₂ : Subgroup (AdelicGroupPoints F G)}
  (hK₁ : IsIwasawaCompact (fam.p J) K₁) (hK₂ : IsIwasawaCompact (fam.p J) K₂)
  (hmax₁ : IsMaximalCompactSubgroup F G K₁) (hmax₂ : IsMaximalCompactSubgroup F G K₂)
  (hinf : K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom)
  {N d : ℕ} {rho : MatrixRepresentation G (Fin N)}
  {hsmooth : SmoothOfRelativeDimension d G.X.hom}
  {hcalc : AdelicDifferentialCommutator F G hsmooth}
  {ψ : AdelicGroupPoints F G → ℂ}

include hmax₁ hmax₂ hinf in
private theorem squareIntegrableOrthogonal_of_finiteCompactComparison
    (hcmp : FiniteCompactPairingComparisonStatement)
    (hψcont : Continuous ψ)
    (hψinv : IsLeftInvariantUnder F G
      (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)) ψ)
    (horth : fam.IsSquareIntegrableOrthogonal K₂ hK₂.isCompact rho hsmooth hcalc J ψ) :
    fam.IsSquareIntegrableOrthogonal K₁ hK₁.isCompact rho hsmooth hcalc J ψ := by
  classical
  obtain ⟨⟨S, hS⟩, _, hcut, ⟨c, _, hpair⟩⟩ :=
    hcmp F G fam J K₁ K₂ hK₁ hK₂ hmax₁ hmax₂ hinf
  intro φ hφ x hx
  let Δ (g : AdelicGroupPoints F G) := hK₁.height g - hK₂.height g
  let cut (v : RealCharacterDual F (fam.P J)) : AdelicGroupPoints F G → ℂ :=
    {g | Δ g = v}.indicator φ
  let pairMeasure := fam.squareIntegrablePairingMeasure K₁ hK₁.isCompact J
  let I (v : RealCharacterDual F (fam.P J)) :=
    fam.squareIntegrablePairingIntegrand K₁ J x (cut v) ψ
  obtain ⟨_, e, he⟩ := fam.standardPositiveLog J
  have hpieces (v : RealCharacterDual F (fam.P J)) :
      Integrable (I v) pairMeasure ∧ (∫ z, I v z ∂pairMeasure) = 0 := by
    obtain ⟨x', hx'⟩ := e.surjective (Multiplicative.ofAdd (characterLog F (fam.P J) x - v))
    have hlog : characterLog F (fam.P J) x'.val = characterLog F (fam.P J) x - v :=
      (he x').symm.trans (congrArg Multiplicative.toAdd hx')
    obtain ⟨hint, hzero⟩ :=
      horth (cut v) (hcut rho hsmooth hcalc φ hφ v) x'.val x'.property
    obtain ⟨hiff, hvalue⟩ :=
      hpair φ ψ hφ.1.2.1.1 hφ.1.1 hψcont hψinv v x x'.val hx x'.property hlog
    refine ⟨hiff.mpr hint, ?_⟩
    have hscaled := hvalue.trans (by rw [hzero, mul_zero, mul_zero])
    exact (mul_eq_zero.mp hscaled).resolve_left (Complex.exp_ne_zero _)
  have hsum (g : AdelicGroupPoints F G) : (∑ v ∈ S, cut v g) = φ g := by
    rw [Finset.sum_eq_single (Δ g)]
    · simp [cut]
    · intro v _ hv
      simp [cut, Ne.symm hv]
    · exact fun h => (h (hS g)).elim
  have hI : fam.squareIntegrablePairingIntegrand K₁ J x φ ψ =
      fun z => ∑ v ∈ S, I v z := by
    funext z
    simp only [I, StandardParabolicFamily.squareIntegrablePairingIntegrand,
      ← Finset.sum_mul, hsum]
  rw [hI]
  refine ⟨integrable_finsetSum S (fun v _ => (hpieces v).1), ?_⟩
  rw [integral_finsetSum S (fun v _ => (hpieces v).1)]
  simp only [(hpieces _).2, Finset.sum_const_zero]

end Transfer

/-- The normalized Levi pairing comparison makes square-integrable orthogonality
independent of the finite part of the Iwasawa compact at fixed infinite projection. -/
def FiniteCompactLeviOrthogonalityTransferStatement : Prop :=
  FiniteCompactPairingComparisonStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p J).hom.hom.left]
    (K₁ K₂ : Subgroup (AdelicGroupPoints F G))
    (hK₁ : IsIwasawaCompact (fam.p J) K₁) (hK₂ : IsIwasawaCompact (fam.p J) K₂),
    IsMaximalCompactSubgroup F G K₁ → IsMaximalCompactSubgroup F G K₂ →
    K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (ψ : AdelicGroupPoints F G → ℂ),
    Continuous ψ →
    IsLeftInvariantUnder F G (parabolicQuotientSubgroup F (fam.p J) (fam.iU J) (fam.l J)) ψ →
    (fam.IsSquareIntegrableOrthogonal K₁ hK₁.isCompact rho hsmooth hcalc J ψ ↔
      fam.IsSquareIntegrableOrthogonal K₂ hK₂.isCompact rho hsmooth hcalc J ψ)

theorem finiteCompactLeviOrthogonalityTransfer : FiniteCompactLeviOrthogonalityTransferStatement := by
  intro hcmp F _ _ G _ _ _ fam J _ K₁ K₂ hK₁ hK₂ hmax₁ hmax₂ hinf N d rho hsmooth hcalc ψ hcont hinv
  exact ⟨squareIntegrableOrthogonal_of_finiteCompactComparison fam J hK₂ hK₁ hmax₂ hmax₁ hinf.symm
      hcmp hcont hinv,
    squareIntegrableOrthogonal_of_finiteCompactComparison fam J hK₁ hK₂ hmax₁ hmax₂ hinf
      hcmp hcont hinv⟩

end Langlands.Global

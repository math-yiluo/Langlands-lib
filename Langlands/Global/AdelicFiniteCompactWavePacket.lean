import Langlands.Global.AdelicEisensteinCompactContinuationComparison
import Langlands.Global.AdelicEisensteinFiniteCompactOperatorComparison
import Langlands.Global.AdelicEisensteinImaginaryContinuation
import Langlands.Global.AdelicEisensteinRegularRegion
import Langlands.Global.AdelicFiniteCompactPairingComparisonStatement

/-! # A single standard inducing form under a finite change of compact -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory Set
open scoped CategoryTheory.MonObj Manifold

set_option autoImplicit false

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

/-- A packet of one square-integrable inducing form for a standard parabolic
is a packet for any maximal Iwasawa compact with the same infinite projection,
given the inducing-form cutoff comparison and imaginary-axis continuations. -/
def FiniteCompactStandardWavePacketTransferStatement : Prop :=
  FiniteCompactPairingComparisonStatement → EisensteinImaginaryContinuationStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G) (J : StandardIndex F G fam.i fam.ν)
    [IsClosedImmersion (fam.p J).hom.hom.left]
    (r : ParabolicRootPresentation (fam.p J) (fam.l J) (fam.a J))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A J).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    (K₁ K₂ : Subgroup (AdelicGroupPoints F G))
    (hK₁ : IsIwasawaCompact (fam.p J) K₁) (_hK₂ : IsIwasawaCompact (fam.p J) K₂),
    IsMaximalCompactSubgroup F G K₁ → IsMaximalCompactSubgroup F G K₂ →
    K₁.map (infinite F G).toMonoidHom = K₂.map (infinite F G).toMonoidHom →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom)
      (hcalc : AdelicDifferentialCommutator F G hsmooth) (φ : AdelicGroupPoints F G → ℂ),
    IsClosedSubgroup rho →
    IsSquareIntegrableInducedForm K₁ hK₁.isCompact rho hsmooth hcalc
      (fam.p J) (fam.iU J) (fam.l J) φ →
    ∀ (E : ComplexCharacterParameter F (fam.P J) → AdelicGroupPoints F G → ℂ)
      (D : Set (ComplexCharacterParameter F (fam.P J))),
    Set.range (imaginaryParameter F (fam.P J)) ⊆ D →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hK₁.eisensteinSeries φ lam) →
    ∀ {n : ℕ} (e : (Fin n → ℝ) ≃ₗ[ℝ] RealCharacterParameter F (fam.P J)) (a : (Fin n → ℝ) → ℂ),
    ContDiff ℝ (⊤ : ℕ∞) a → HasCompactSupport a →
    IsWavePacket F G K₂ rho hsmooth hcalc
      (fun g => ∫ z, a z * E (imaginaryParameter F (fam.P J) (e z)) g ∂(spectralMeasure n))

theorem finiteCompactStandardWavePacketTransfer : FiniteCompactStandardWavePacketTransferStatement := by
  classical
  intro hcmp hcont F _ _ G _ _ _ fam J _ r _ _ _ hA hT K₁ K₂ hK₁ hK₂ hmax₁ hmax₂ hinf N d
    rho hsmooth hcalc φ hclosed hφ E D hDimag hEm hEreg n e a ha hac
  let P := fam.P J
  let Δ (g : AdelicGroupPoints F G) := hK₁.height g - hK₂.height g
  obtain ⟨_, _, hcut, _⟩ := hcmp F G fam J K₁ K₂ hK₁ hK₂ hmax₁ hmax₂ hinf
  have hopen := IsMaximalCompactSubgroup.isOpen_intersection_of_infinite_eq F G K₁ K₂ hmax₂ hinf
  obtain ⟨S, _, htwist⟩ := hK₁.exists_parameterTwist_clopen_decomposition hK₂ hopen
  have hS : S.Nonempty := by
    by_contra hs
    have hempty := Finset.not_nonempty_iff_eq_empty.mp hs
    have h := htwist (fun _ => (1 : ℂ)) 0 1
    simp [hempty, IsIwasawaCompact.parameterTwist, IsIwasawaCompact.heightPower] at h
  let k := Fintype.card ↥S
  let ix := (Fintype.equivFin ↥S).symm
  let value (j : Fin k) : RealCharacterDual F P := (ix j).val
  let v (j : Fin k) (g : AdelicGroupPoints F G) := if Δ g = value j then φ g else 0
  let w (j : Fin k) (lam : ComplexCharacterParameter F P) :=
    Complex.exp (complexParameterPairing F P lam (value j))
  have hv (j : Fin k) :
      IsSquareIntegrableInducedForm K₂ hK₂.isCompact rho hsmooth hcalc
        (fam.p J) (fam.iU J) (fam.l J) (v j) := by
    have hEq : v j = {g | Δ g = value j}.indicator φ := by
      funext g
      simp [v, Set.indicator]
    rw [hEq]
    exact hcut rho hsmooth hcalc φ hφ (value j)
  have htwist' (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
      hK₁.parameterTwist φ lam g = ∑ j, w j lam * hK₂.parameterTwist (v j) lam g := by
    let term (t : RealCharacterDual F P) :=
      Complex.exp (complexParameterPairing F P lam t) *
        hK₂.parameterTwist (fun z => if Δ z = t then φ z else 0) lam g
    calc
      _ = ∑ t ∈ S, term t := htwist φ lam g
      _ = ∑ t : S, term t := (Finset.sum_coe_sort S term).symm
      _ = _ := Fintype.sum_equiv (Fintype.equivFin ↥S) _ _
        (fun t => by simp [term, w, v, value, ix])
  obtain ⟨E₂, D₂, hD₂imag, hE₂m, hE₂reg⟩ := hcont F G P (fam.M J) (fam.U J) (fam.A J)
    (fam.p J) (fam.iU J) (fam.l J) (fam.a J) r hA hT fam.connectedReductive
    (fam.isUnipotentRadical J) K₂ hK₂ rho hsmooth hcalc hmax₂ hclosed k v hv
  have hterm (j : Fin k) : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam →
      E₂ j lam = hK₂.eisensteinSeries (v j) lam ∧
        ∀ g, Summable (hK₂.eisensteinTerm (v j) lam g) := by
    obtain ⟨R₁, hR₁⟩ := hE₂reg j
    obtain ⟨R₂, hR₂⟩ := eisensteinAbsoluteConvergence.exists_summable_eisensteinTerm r hA hT
      fam.connectedReductive (fam.isUnipotentRadical J) hK₂ rho hsmooth hcalc hmax₂ hclosed (hv j).1
    exact ⟨max R₁ R₂, fun lam hreg =>
      ⟨hR₁ lam (isRegularParameter_mono r hA hT (le_max_left _ _) hreg),
        hR₂ lam (isRegularParameter_mono r hA hT (le_max_right _ _) hreg)⟩⟩
  choose R₂ hR₂ using hterm
  obtain ⟨R₁, hR₁⟩ := hEreg
  let R := max R₁ (∑ j, max (R₂ j) 0)
  have hR (j : Fin k) : R₂ j ≤ R :=
    (le_max_left _ _).trans ((Finset.single_le_sum
      (f := fun i => max (R₂ i) 0) (fun i _ => le_max_right _ _) (Finset.mem_univ j)).trans
      (le_max_right _ _))
  have hagree (lam : ComplexCharacterParameter F P) (hlam : r.IsRegularParameter hA hT R lam)
      (g : AdelicGroupPoints F G) : E lam g = ∑ j, w j lam * E₂ j lam g := by
    have hlocal (j : Fin k) := hR₂ j lam (isRegularParameter_mono r hA hT (hR j) hlam)
    rw [hR₁ lam (isRegularParameter_mono r hA hT (le_max_left _ _) hlam)]
    simp_rw [fun j => (hlocal j).1]
    exact hK₁.eisensteinSeries_eq_finset_sum_of_twist hK₂ Finset.univ
      (fun j => w j lam) φ v lam (htwist' lam) g (fun j _ => (hlocal j).2 g)
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) :=
    finiteDimensional_complexCharacterParameter r fam.connectedReductive
  let j₀ : Fin k := (Fintype.equivFin ↥S) ⟨hS.choose, hS.choose_spec⟩
  have hDomain := (hE₂m j₀ 1).isOpenDenseInCoordinates
  have hm (j : Fin k) : IsMeromorphicInCoordinatesOn (w j) D₂ :=
    ⟨inferInstance, fun m chart =>
      isMeromorphicOn_exp_parameterPairing chart.toLinearMap (value j)
        (hDomain m chart).1 (hDomain m chart).2⟩
  have hsum (g : AdelicGroupPoints F G) :
      IsMeromorphicInCoordinatesOn (fun lam => ∑ j, w j lam * E₂ j lam g) D₂ := by
    convert IsMeromorphicInCoordinatesOn.sum Finset.univ hDomain
      (h := fun j : Fin k => w j * (fun lam => E₂ j lam g)) (fun j _ => ?_) using 1
    · funext lam
      simp only [Finset.sum_apply, Pi.mul_apply]
    · simpa only [inter_self] using (hm j).mul (hE₂m j g)
  obtain ⟨q, ⟨chart⟩⟩ := exists_complexParameterEquiv fam.connectedReductive r.isCompatible.parabolic
  have hImAgree (x : Fin n → ℝ) (g : AdelicGroupPoints F G) :
      E (imaginaryParameter F P (e x)) g =
        ∑ j, w j (imaginaryParameter F P (e x)) * E₂ j (imaginaryParameter F P (e x)) g := by
    apply (hEm g).eqOn_of_eqOn_open (hsum g) chart
      (r.isOpen_regularParameter_inCoordinates hA hT R chart)
      (r.nonempty_regularParameter_inCoordinates hA hT R chart)
    · exact fun z hz => hagree (chart z) hz.1 g
    · exact ⟨hDimag ⟨e x, rfl⟩, hD₂imag ⟨e x, rfl⟩⟩
  let a₂ (j : Fin k) (x : Fin n → ℝ) := a x * w j (imaginaryParameter F P (e x))
  have ha₂ (j : Fin k) : ContDiff ℝ (⊤ : ℕ∞) (a₂ j) ∧ HasCompactSupport (a₂ j) := by
    let L : (Fin n → ℝ) →ₗ[ℝ] ℂ :=
      (((complexParameterPairing F P).flip (value j)).restrictScalars ℝ).comp
        ((imaginaryParameter F P).comp e.toLinearMap)
    exact ⟨ha.mul L.toContinuousLinearMap.contDiff.cexp, hac.mul_right⟩
  refine ⟨P, fam.M J, fam.U J, fam.A J, fam.affineP J, fam.affineM J, fam.finiteTypeM J,
    fam.affineU J, fam.p J, inferInstance, fam.iU J, fam.l J, fam.closedU J, fam.a J, r,
    inferInstance, inferInstance, inferInstance, hA, hT, fam.isUnipotentRadical J,
    hK₂, n, e, k, v, a₂, E₂, D₂, hv, ha₂, hD₂imag, hE₂m, hE₂reg, ?_⟩
  funext g
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun z => by
    change a z * E (imaginaryParameter F P (e z)) g =
      ∑ j, a₂ j z * E₂ j (imaginaryParameter F P (e z)) g
    rw [hImAgree z g, Finset.mul_sum]
    simp only [a₂, mul_assoc]

end Langlands.Global

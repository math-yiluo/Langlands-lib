import Langlands.Global.AdelicTruncationCentralCovariance
import Langlands.Global.AdelicWeylPositiveTransport

/-! # Central translates of the square-integrable Weyl twists -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  Automorphic.GroupSchemeFunctions

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Param[" J "]" => ComplexCharacterParameter F (fam.P J)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Z" => fam.positiveSplitComponent fam.top
set_option quotPrecheck false in
local notation "lift[" P "," z "]" => fam.splitLift (show P ≤ fam.top from (P).property) z

attribute [local instance] isClosedImmersion_p

/-- The two Weyl-related parameters give the same character at the actual lift of a central
point, since the conjugation relation fixes its ambient image. -/
theorem truncationCentralFactor_weylParameter (P Q : Idx)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (c : fam.M Q ⟶ fam.M P) (r : fam.P Q ⟶ fam.M Q)
    (hw : IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) w c)
    (hr : fam.l Q ≫ r = 𝟙 (fam.M Q)) (z : Z) (lam : Param[P]) :
    fam.truncationCentralFactor Q z (weylParameter (fam.l P) c r lam) =
      fam.truncationCentralFactor P z lam := by
  let x := lift[Q,z]
  obtain ⟨y, hy, he⟩ := x.property
  let y' : intrinsicSubgroup F (fam.A Q) := ⟨y, hy⟩
  have hx : positivePointMap F (fam.P Q) (fam.A Q) (fam.a Q ≫ fam.l Q) y' = x.val := he
  have hmap : map F (fam.P Q) (fam.P P) (r ≫ c ≫ fam.l P) x.val = (lift[P,z]).val := by
    apply (isClosedEmbedding_map F (fam.P P) G (fam.p P)).injective
    rw [fam.map_splitLift P.property z, ← hx, weylMap_positive_conjugation hw hr, hx,
      fam.map_splitLift Q.property z]
    let y := innerAdelicPoint F G w
    change y⁻¹ * fam.centralPoint z * y = fam.centralPoint z
    rw [mul_assoc, (fam.centralPoint_commute z y).eq, ← mul_assoc, inv_mul_cancel, one_mul]
  change parameterPower F (fam.P Q) (weylParameter (fam.l P) c r lam) x.val = _
  rw [weylParameter_power, hmap]
  rfl

private theorem halfModulus_centralLift (Q : Idx) (z : Z) : fam.halfModulus Q (lift[Q,z]).val = 1 := by
  have h := standardNestedHalfModulusCompatibility F G fam Q fam.top Q.property z (lift[Q,z])
    (fam.map_splitLift Q.property z)
  let : IsIso (fam.p fam.top) := fam.isIso_topParabolic
  have hred : IsConnectedReductive (fam.P fam.top) :=
    fam.connectedReductive.of_iso (asIso (fam.p fam.top))
  have hδ : halfModulusParameter F (fam.P fam.top) = 0 := by
    rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F _ hred, TensorProduct.tmul_zero]
  rw [h, halfModulus, hδ, InducedInnerProductIntegrable.parameterPower_zero]

/-- The central translate of a normalized inducing vector's height twist is its central
parameter power times the twist. -/
theorem centralTranslate_parameterTwist (Q : Idx) {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p Q) K) {f : Fun}
    (hf : IsSplitComponentEquivariant (fam.p Q) (fam.l Q) f) (eta : Param[Q]) (z : Z) :
    fam.centralTranslate z (hK.parameterTwist f eta) =
      fam.truncationCentralFactor Q z eta • hK.parameterTwist f eta := by
  funext g
  let x := lift[Q,z]
  change hK.parameterTwist f eta (g * fam.centralPoint z) =
    fam.truncationCentralFactor Q z eta * hK.parameterTwist f eta g
  have hz : map F (fam.P Q) G (fam.p Q) x.val = fam.centralPoint z := fam.map_splitLift Q.property z
  rw [← (fam.centralPoint_commute z g).eq, ← hz]
  unfold IsIwasawaCompact.parameterTwist
  rw [fam.splitComponentEquivariant_apply Q hf x.property g, fam.halfModulus_centralLift Q z,
    one_mul, hK.heightPower_map_mul]
  change f g * (parameterPower F (fam.P Q) eta x.val * hK.heightPower eta g) =
    parameterPower F (fam.P Q) eta x.val * (f g * hK.heightPower eta g)
  ac_rfl

/-- A height twist with a Weyl-conjugate label has the original source central character. -/
def WeylCentralTwistStatement : Prop :=
  ∀ (P Q : Idx) {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact (fam.p Q) K)
    (w : Over.mk (𝟙 (Spec (CommRingCat.of F))) ⟶ G.X)
    (c : fam.M Q ⟶ fam.M P) (r : fam.P Q ⟶ fam.M Q),
    IsWeylConjugation (fam.p P) (fam.l P) (fam.p Q) (fam.l Q) w c →
    fam.l Q ≫ r = 𝟙 (fam.M Q) →
    ∀ f : Fun, IsSplitComponentEquivariant (fam.p Q) (fam.l Q) f →
      ∀ (lam : Param[P]) (z : Z),
        let g := hK.parameterTwist f (weylParameter (fam.l P) c r lam)
        fam.centralTranslate z g = fam.truncationCentralFactor P z lam • g

theorem weylCentralTwist : fam.WeylCentralTwistStatement := by
  intro P Q K hK w c r hw hr f hf lam z g
  dsimp only [g]
  rw [fam.centralTranslate_parameterTwist Q hK hf, fam.truncationCentralFactor_weylParameter P Q w c r hw hr]

variable {fam}

/-- Multiply the polynomial coefficients of a unitary pairing by a scalar. -/
def UnitaryPairingExpansion.scale {Q : Idx} (e : fam.UnitaryPairingExpansion Q) (b : ℂ) :
    fam.UnitaryPairingExpansion Q :=
  ⟨e.exponents, fun a => b • e.coefficient a, e.unitary⟩

omit [NumberField F] in
theorem UnitaryPairingExpansion.eval_scale {Q : Idx} (e : fam.UnitaryPairingExpansion Q) (b : ℂ)
    (x : fam.relativeSimpleRoots Q → ℝ) : (e.scale b).eval x = b * e.eval x := by
  simp only [UnitaryPairingExpansion.scale, UnitaryPairingExpansion.eval, MvPolynomial.smul_eq_C_mul,
    map_mul, MvPolynomial.eval_C, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

private theorem negativeOrthantRegularizedIntegral_smul {α : Type*} [Fintype α]
    (a : α → ℂ) (b : ℂ) (q : MvPolynomial α ℂ) :
    negativeOrthantRegularizedIntegral a (b • q) = b * negativeOrthantRegularizedIntegral a q := by
  by_cases h : b = 0
  · simp [h, negativeOrthantRegularizedIntegral]
  simp only [negativeOrthantRegularizedIntegral, MvPolynomial.support_smul_eq h,
    MvPolynomial.coeff_smul, smul_eq_mul, Finset.mul_sum, mul_assoc]

omit [NumberField F] in
theorem UnitaryPairingExpansion.regularizedConeIntegral_scale {Q : Idx}
    (e : fam.UnitaryPairingExpansion Q) (b : ℂ) (T : V fam.T) :
    (e.scale b).regularizedConeIntegral T = b * e.regularizedConeIntegral T := by
  have hshift (q : MvPolynomial (fam.relativeSimpleRoots Q) ℂ) :
      polynomialShift (fam.weightCoordinate Q T) (b • q) = b • polynomialShift (fam.weightCoordinate Q T) q :=
    map_smul (MvPolynomial.aeval (R := ℂ) (fun a =>
      MvPolynomial.X a + MvPolynomial.C (fam.weightCoordinate Q T a : ℂ))) _ _
  simp only [UnitaryPairingExpansion.scale, UnitaryPairingExpansion.regularizedConeIntegral,
    hshift, negativeOrthantRegularizedIntegral_smul, Finset.mul_sum]
  exact Finset.sum_congr rfl fun _ _ => by ring

omit [NumberField F] in
theorem regularizedPairing_scale (vol : Idx → ℝ) (e : ∀ Q, fam.UnitaryPairingExpansion Q)
    (b : ℂ) (T : V fam.T) :
    fam.regularizedPairing vol (fun Q => (e Q).scale b) T = b * fam.regularizedPairing vol e T := by
  simp only [regularizedPairing, UnitaryPairingExpansion.regularizedConeIntegral_scale, mul_finsum]
  exact congrArg finsum (funext fun _ => by ring)

variable (fam)

/-- An integrable normalized pairing expansion scales by the product of the scalar on its
first argument and the conjugate scalar on its second argument. -/
theorem isNormalizedPairingExpansion_scale (Q : Idx) (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {I : Type*} (s : Finset I)
    (u : I → Fun) (g : Fun) (e : fam.UnitaryPairingExpansion Q)
    (he : fam.IsNormalizedPairingExpansion K hKc Q s u g e) (a b : ℂ) :
    fam.IsNormalizedPairingExpansion K hKc Q s (fun i => a • u i) (b • g) (e.scale (a * starRingEnd ℂ b)) := by
  intro x hx c hc
  obtain ⟨hint, hval⟩ := he x hx c hc
  let d := a * starRingEnd ℂ b
  have hi (i : I) : fam.squareIntegrablePairingIntegrand K Q x (a • u i) (b • g) =
      fun z => d * fam.squareIntegrablePairingIntegrand K Q x (u i) g z := by
    funext z
    simp only [squareIntegrablePairingIntegrand, Pi.smul_apply, smul_eq_mul, map_mul, d]
    ring
  refine ⟨fun i hi' => hi i ▸ (hint i hi').const_mul d, ?_⟩
  have hv (i : I) : fam.normalizedPairing K hKc Q x (a • u i) (b • g) =
      d * fam.normalizedPairing K hKc Q x (u i) g := by
    rw [normalizedPairing, hi, integral_const_mul]
    simp only [normalizedPairing]
    ring
  simp_rw [hv, ← Finset.mul_sum, hval, UnitaryPairingExpansion.eval_scale]
  rfl

/-- Central eigencharacters for the actual pieces give the scaled expansion for the translated
pairing, using the same set of labels and the same slice measure. -/
theorem isNormalizedPairingExpansion_centralTranslate (Q : Idx) (K : Subgroup (AdelicGroupPoints F G))
    (hKc : IsCompact (K : Set (AdelicGroupPoints F G))) {I : Type*} (s : Finset I)
    (u : I → Fun) (g : Fun) (e : fam.UnitaryPairingExpansion Q)
    (he : fam.IsNormalizedPairingExpansion K hKc Q s u g e) (a b : ℂ) (z : Z)
    (hu : ∀ i ∈ s, fam.centralTranslate z (u i) = a • u i)
    (hg : fam.centralTranslate z g = b • g) :
    fam.IsNormalizedPairingExpansion K hKc Q s (fun i => fam.centralTranslate z (u i))
      (fam.centralTranslate z g) (e.scale (a * starRingEnd ℂ b)) := by
  intro x hx c hc
  obtain ⟨hI, hs⟩ := fam.isNormalizedPairingExpansion_scale Q K hKc s u g e he a b x hx c hc
  rw [hg]
  refine ⟨fun i hi => ?_, ?_⟩
  · change Integrable (fam.squareIntegrablePairingIntegrand K Q x (fam.centralTranslate z (u i)) (b • g)) _
    rw [hu i hi]
    exact hI i hi
  · rw [← hs]
    refine Finset.sum_congr rfl fun i hi => ?_
    change fam.normalizedPairing K hKc Q x (fam.centralTranslate z (u i)) (b • g) = _
    rw [hu i hi]

end Langlands.Global.StandardParabolicFamily

import Langlands.Global.AdelicTopEisensteinContinuation
import Langlands.Global.AdelicWeakConstantTermHalfModulusProof
import Langlands.Global.AdelicWeakConstantTermComponentExtraction
import Langlands.Global.AdelicSplitComponentShifts
import Langlands.Global.AdelicTruncatedEisensteinPairing

/-! # Central covariance of the characteristic pairing and weak constant terms -/

noncomputable section

open CategoryTheory AlgebraicGeometry MeasureTheory
open scoped CategoryTheory.MonObj

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme GroupScheme.RealTorusSpace AdelicGroupPoints PositiveRealTorus
  ArthurTruncation AdelicSiegelFactors Automorphic.GroupSchemeFunctions Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Z" => fam.positiveSplitComponent fam.top
local notation "Param[" J "]" => ComplexCharacterParameter F (fam.P J)
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Ltop" => fam.l fam.top ≫ fam.p fam.top
set_option quotPrecheck false in
local notation "zLift[" P "," z "]" => fam.splitLift (show P ≤ fam.top from (P).property) z

omit [NumberField F] in
private theorem topSplitComponent_isSplitComponent : IsSplitComponent (fam.a fam.top ≫ Ltop) := by
  let : IsIso Ltop := fam.isIso_topLevi
  let e := asIso (Ltop)
  let a := fam.a fam.top
  have ha : IsSplitComponent a := (fam.isCompatible fam.top).splitComponent
  change IsSplitComponent (a ≫ e.hom)
  refine ⟨⟨(IsSplitSubtorus.comp_iso_iff a e).mpr ha.1.1, ha.1.2.comp_iso e⟩, ?_⟩
  intro B b hb s hs
  apply ha.2 B (b ≫ e.inv)
    ⟨(IsSplitSubtorus.comp_iso_iff b e.symm).mpr hb.1, hb.2.comp_iso e.symm⟩ s
  simpa only [Category.assoc, Iso.hom_inv_id, Category.comp_id] using
    congrArg (fun x => x ≫ e.inv) hs

/-- A central point in the truncation definition is a point of the canonical split centre. -/
theorem centralPoint_mem_canonical (z : Z) :
    fam.centralPoint z ∈ RestrictionSplitCentre.canonicalSubgroup F G := by
  rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup fam.topSplitComponent_isSplitComponent]
  obtain ⟨x, hx, hz⟩ := z.property
  change map F (fam.A fam.top).toGrp (fam.P fam.top) (fam.a fam.top ≫ fam.l fam.top) x = z.val at hz
  refine ⟨x, hx, ?_⟩
  change map F (fam.A fam.top).toGrp G (fam.a fam.top ≫ Ltop) x =
    map F (fam.P fam.top) G (fam.p fam.top) z.val
  rw [← Category.assoc, map_comp_apply_of_hom, hz]

/-- The ambient image of a top split point commutes with every adelic point. -/
theorem centralPoint_commute (z : Z) (g : AdelicGroupPoints F G) :
    Commute (fam.centralPoint z) g := by
  obtain ⟨x, hx, hz⟩ := z.property
  change map F (fam.A fam.top).toGrp (fam.P fam.top) (fam.a fam.top ≫ fam.l fam.top) x = z.val at hz
  have he : fam.centralPoint z = positivePointMap F G (fam.A fam.top) (fam.a fam.top ≫ Ltop) ⟨x, hx⟩ := by
    change map F (fam.P fam.top) G (fam.p fam.top) z.val =
      map F (fam.A fam.top).toGrp G (fam.a fam.top ≫ Ltop) x
    rw [← Category.assoc, map_comp_apply_of_hom, hz]
  rw [he]
  exact positivePointMap_commute F G _ _ fam.topSplitComponent_isSplitComponent.1.2 _ _

private theorem centralTranslate_eq_unnormalizedAction (z : Z) (f : Fun) :
    fam.centralTranslate z f = fam.unnormalizedAction fam.top z.val f := by
  funext g
  change f (g * fam.centralPoint z) = f (fam.centralPoint z * g)
  rw [(fam.centralPoint_commute z g).eq]

private theorem halfModulus_centralLift_eq_one (P : Idx) (z : Z) :
    fam.halfModulus P (zLift[P,z]).val = 1 := by
  have h := standardNestedHalfModulusCompatibility F G fam P fam.top P.property z (zLift[P,z])
    (fam.map_splitLift P.property z)
  let : IsIso (fam.p fam.top) := fam.isIso_topParabolic
  have hred : IsConnectedReductive (fam.P fam.top) :=
    fam.connectedReductive.of_iso (asIso (fam.p fam.top))
  have hδ : halfModulusParameter F (fam.P fam.top) = 0 := by
    rw [halfModulusParameter, Lie.connectedReductiveAdjointDeterminant F _ hred, TensorProduct.tmul_zero]
  rw [h, halfModulus, hδ, InducedInnerProductIntegrable.parameterPower_zero]

/-- The inducing parameter evaluated on the actual lift of the ambient central point. -/
def truncationCentralFactor (P : Idx) (z : Z) (lam : Param[P]) : ℂ :=
  parameterPower F (fam.P P) lam (zLift[P,z]).val

/-- The central factor is an entire function in complex spectral coordinates. -/
theorem differentiable_truncationCentralFactor (P : Idx) (z : Z) {n : ℕ}
    (e : (Fin n → ℂ) ≃ₗ[ℂ] Param[P]) : Differentiable ℂ (fun s => fam.truncationCentralFactor P z (e s)) := by
  simpa only [truncationCentralFactor, add_zero, LinearEquiv.coe_coe] using
    differentiable_parameterPower_affine e.toLinearMap 0 (zLift[P,z]).val

private theorem norm_parameterPower_imaginary {P : GroupScheme (Spec (CommRingCat.of F))}
    [IsAffine P.X.left] (x : RealCharacterParameter F P) (a : AdelicGroupPoints F P) :
    ‖parameterPower F P (imaginaryParameter F P x) a‖ = 1 := by
  rw [parameterPower, Complex.norm_exp, complexParameterPairing_re, parameterRealPart_imaginaryParameter]
  simp

theorem norm_truncationCentralFactor_imaginary (P : Idx) (z : Z) (x : RealCharacterParameter F (fam.P P)) :
    ‖fam.truncationCentralFactor P z (imaginaryParameter F (fam.P P) x)‖ = 1 :=
  norm_parameterPower_imaginary x (zLift[P,z]).val

attribute [local instance] isClosedImmersion_p

/-- At a point of the continuation domain, the actual central translate of the series is
multiplication by the entire central factor. -/
theorem centralTranslate_eisensteinContinuation {P : Idx} {K : Subgroup (AdelicGroupPoints F G)}
    (hKP : IsIwasawaCompact (fam.p P) K)
    (r : ParabolicRootPresentation (fam.p P) (fam.l P) (fam.a P))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A P).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {φ : Fun} (hφ : IsSplitComponentEquivariant (fam.p P) (fam.l P) φ)
    (E : Param[P] → Fun) (D : Set (Param[P]))
    (hE : ∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D)
    (hreg : ∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKP.eisensteinSeries φ lam)
    (z : Z) {lam : Param[P]} (hlam : lam ∈ D) :
    fam.centralTranslate z (E lam) = fam.truncationCentralFactor P z lam • E lam := by
  let x := zLift[P,z]
  have he : map F (fam.P P) G (fam.p P) x.val = fam.centralPoint z := fam.map_splitLift P.property z
  have hc (g : AdelicGroupPoints F G) :
      map F (fam.P P) G (fam.p P) x.val * g = g * map F (fam.P P) G (fam.p P) x.val := by
    rw [he]
    exact (fam.centralPoint_commute z g).eq
  have hφ' (g : AdelicGroupPoints F G) : φ (map F (fam.P P) G (fam.p P) x.val * g) = 1 * φ g := by
    rw [← fam.halfModulus_centralLift_eq_one P z]
    exact fam.splitComponentEquivariant_apply P hφ x.property g
  funext g
  change E lam (g * fam.centralPoint z) = fam.truncationCentralFactor P z lam * E lam g
  rw [← he, ← hc g]
  simpa only [truncationCentralFactor, one_mul] using
    eisensteinContinuation_central_mul hKP r hA hT fam.connectedReductive hE hreg hc hφ' hlam g

/-- The central character in the tested form hypothesis gives the corresponding right translate. -/
theorem centralTranslate_of_unitary_centralCharacter (ν : RealCharacterParameter F G) {Φ : Fun}
    (hΦ : ∀ a ∈ RestrictionSplitCentre.canonicalSubgroup F G, ∀ g,
      Φ (a * g) = parameterPower F G (imaginaryParameter F G ν) a * Φ g) (z : Z) :
    fam.centralTranslate z Φ = parameterPower F G (imaginaryParameter F G ν) (fam.centralPoint z) • Φ := by
  funext g
  change Φ (g * fam.centralPoint z) = parameterPower F G (imaginaryParameter F G ν) (fam.centralPoint z) * Φ g
  rw [← (fam.centralPoint_commute z g).eq]
  exact hΦ _ (fam.centralPoint_mem_canonical z) g

private theorem centralTranslate_one (f : Fun) : fam.centralTranslate (1 : Z) f = f := by
  funext g
  change f (g * map F (fam.P fam.top) G (fam.p fam.top) 1) = f g
  rw [map_one, mul_one]

/-- With two central eigencharacters the characteristic integrand is multiplied by their
sesquilinear product. The cutoff and the quotient measure are identical. -/
theorem truncatedPairingIntegrand_central_factor {f g : Fun} {z : Z} {s t : ℂ}
    (hf : fam.centralTranslate z f = s • f) (hg : fam.centralTranslate z g = t • g) :
    fam.truncatedPairingIntegrand z f g = (s * starRingEnd ℂ t) • fam.truncatedPairingIntegrand 1 f g := by
  funext x
  simp only [truncatedPairingIntegrand, hf, hg, fam.centralTranslate_one, Pi.smul_apply, smul_eq_mul,
    map_mul]
  ring

/-- The same central factor may be taken outside the characteristic pairing. -/
theorem truncatedPairing_central_factor {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p fam.bot) K)
    (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
      (Standard.leviScheme fam.i fam.ν ∅)) (T₀ Tp : V fam.T) {f g : Fun} {z : Z} {s t : ℂ}
    (hf : fam.centralTranslate z f = s • f) (hg : fam.centralTranslate z g = t • g) :
    fam.truncatedPairing hK C T₀ Tp z f g =
      (s * starRingEnd ℂ t) * fam.truncatedPairing hK C T₀ Tp 1 f g := by
  unfold truncatedPairing
  rw [fam.truncatedPairingIntegrand_central_factor hf hg]
  simp only [Pi.smul_apply, smul_eq_mul, integral_const_mul]

private theorem centralTranslate_constantTerm_of_eigenvalue (Q : Idx) (z : Z) {f : Fun} {s : ℂ}
    (hf : fam.centralTranslate z f = s • f) :
    fam.centralTranslate z (fam.constantTerm Q f) = s • fam.constantTerm Q f := by
  funext g
  unfold centralTranslate constantTerm subgroupConstantTerm
  simp_rw [← mul_assoc]
  have h (g' : AdelicGroupPoints F G) : f (g' * fam.centralPoint z) = s * f g' := congrFun hf g'
  simp_rw [h, integral_const_mul, Pi.smul_apply, smul_eq_mul]

set_option maxHeartbeats 1500000 in
/-- Distinct normalized exponent components of the constant term inherit the scalar
under a central translate of the original function. -/
theorem centralTranslate_exponentComponent (Q : Idx) (z : Z) {f : Fun} {s : ℂ}
    (hf : fam.centralTranslate z f = s • f)
    (t : Finset (Param[Q])) (c : Param[Q] → Fun)
    (hsum : fam.constantTerm Q f = ∑ lam ∈ t, c lam)
    (hexp : ∀ lam ∈ t, fam.HasExponent Q lam (c lam)) :
    ∀ lam ∈ t, fam.centralTranslate z (c lam) = s • c lam := by
  classical
  let D : MonoidAlgebra ℂ Z := MonoidAlgebra.of ℂ _ z - algebraMap ℂ _ s
  let T := fam.shiftAlgHom fam.top D
  have hT (g : Fun) : T g = fam.centralTranslate z g - s • g := by
    simp only [T, D, map_sub, AlgHom.commutes, LinearMap.sub_apply, fam.shiftAlgHom_of,
      Module.algebraMap_end_apply, ← fam.centralTranslate_eq_unnormalizedAction z]
  have hz : ∑ lam ∈ t, T (c lam) = 0 := by
    rw [← map_sum, ← hsum, hT, fam.centralTranslate_constantTerm_of_eigenvalue Q z hf, sub_self]
  have he (lam : Param[Q]) (hlam : lam ∈ t) : fam.HasExponent Q lam (T (c lam)) :=
    (fam.hasExponent_iff Q lam _).mpr (((fam.hasExponent_iff Q lam _).mp (hexp lam hlam)).shiftAlgHom
      fam Q.property D)
  intro lam hlam
  have hzero := fam.eq_zero_of_sum_eq_zero_of_hasExponent Q t (fun u => T (c u)) he hz lam hlam
  rw [hT, sub_eq_zero] at hzero
  exact hzero

/-- The weak constant term retains the central character of the original function. -/
theorem centralTranslate_weakConstantTerm (Q : Idx) (z : Z) {f g : Fun} {s : ℂ} {N d : ℕ}
    {hsmooth : SmoothOfRelativeDimension d G.X.hom}
    {Kinf : Subgroup (InfiniteAdelicGroupPoints F G)} {rho : MatrixRepresentation G (Fin N)}
    (hf : fam.centralTranslate z f = s • f) (hg : fam.IsWeakConstantTerm hsmooth Kinf rho Q f g) :
    fam.centralTranslate z g = s • g := by
  classical
  obtain ⟨t, c, hd, rfl⟩ := hg
  have h := fam.centralTranslate_exponentComponent Q z hf t c hd.sum_eq hd.exponent
  funext x
  simp only [centralTranslate, unitaryExponentSum, Finset.sum_apply, Pi.smul_apply, Finset.smul_sum]
  refine Finset.sum_congr rfl fun lam hlam => ?_
  exact congrFun (h lam (Finset.mem_filter.mp hlam).1) x

/-- On the imaginary axis the characteristic pairing at a central translate is the
pairing at the identity times a scalar of absolute value one. The scalar depends holomorphically
on the complex inducing parameter in every linear chart. -/
def TruncationCentralCovarianceStatement : Prop :=
  ∀ {P : Idx} {K : Subgroup (AdelicGroupPoints F G)}
    (hK : IsIwasawaCompact (fam.p fam.bot) K) (hKP : IsIwasawaCompact (fam.p P) K)
    (r : ParabolicRootPresentation (fam.p P) (fam.l P) (fam.a P))
    [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
    [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
    (hA : IsSplitTorus (fam.A P).toGrp) (hT : IsSplitTorus r.data.T.toGrp)
    {φ : Fun}, IsSplitComponentEquivariant (fam.p P) (fam.l P) φ →
    ∀ (E : Param[P] → Fun) (D : Set (Param[P])),
    Set.range (imaginaryParameter F (fam.P P)) ⊆ D →
    (∀ g, IsMeromorphicInCoordinatesOn (fun lam => E lam g) D) →
    (∃ R : ℝ, ∀ lam, r.IsRegularParameter hA hT R lam → E lam = hKP.eisensteinSeries φ lam) →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom) (hcalc : AdelicDifferentialCommutator F G hsmooth)
      {Φ : Fun}, IsLogSquareIntegrableAutomorphicForm F G K rho hsmooth hcalc Φ →
    ∀ (z : Z), ∃ b : Param[P] → ℂ,
      (∀ n (e : (Fin n → ℂ) ≃ₗ[ℂ] Param[P]), Differentiable ℂ (b ∘ e)) ∧
      ∀ x : RealCharacterParameter F (fam.P P),
        let lam := imaginaryParameter F (fam.P P) x
        ‖b lam‖ = 1 ∧
        fam.truncatedPairingIntegrand z (E lam) Φ = b lam • fam.truncatedPairingIntegrand 1 (E lam) Φ ∧
        ∀ (C : CompactFactors F G (Standard.unipotentScheme fam.i fam.ν ∅)
          (Standard.leviScheme fam.i fam.ν ∅)) (T₀ Tp : V fam.T),
          fam.truncatedPairing hK C T₀ Tp z (E lam) Φ = b lam * fam.truncatedPairing hK C T₀ Tp 1 (E lam) Φ

set_option maxHeartbeats 2200000 in
theorem truncationCentralCovariance : fam.TruncationCentralCovarianceStatement := by
  intro P K hK hKP r _ _ _ hA hT φ hφ E D hD hE hreg N d rho hsmooth hcalc Φ hΦ z
  obtain ⟨ν, hν⟩ := hΦ.2.1
  let t := parameterPower F G (imaginaryParameter F G ν) (fam.centralPoint z)
  let b := fun lam => fam.truncationCentralFactor P z lam * starRingEnd ℂ t
  refine ⟨b, ?_, fun x => ?_⟩
  · intro n e
    exact (fam.differentiable_truncationCentralFactor P z e).mul_const _
  · let lam := imaginaryParameter F (fam.P P) x
    have hE' := fam.centralTranslate_eisensteinContinuation hKP r hA hT hφ E D hE hreg z
      (lam := lam) (hD ⟨x, rfl⟩)
    have hΦ' := fam.centralTranslate_of_unitary_centralCharacter ν hν z
    refine ⟨?_, fam.truncatedPairingIntegrand_central_factor hE' hΦ',
      fun C T₀ Tp => fam.truncatedPairing_central_factor hK C T₀ Tp hE' hΦ'⟩
    simp only [b, norm_mul, Complex.norm_conj, fam.norm_truncationCentralFactor_imaginary,
      t, norm_parameterPower_imaginary, mul_one]

end Langlands.Global.StandardParabolicFamily

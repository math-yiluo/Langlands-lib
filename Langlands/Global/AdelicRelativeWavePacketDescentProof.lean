import Langlands.Global.AdelicRelativeWavePacketDescentStatement
import Langlands.Global.AdelicEisensteinRegularParameterProof
import Langlands.Global.AdelicEisensteinContinuationReduction
import Langlands.Global.AdelicEisensteinRationalCosets
import Langlands.Global.AdelicInducedInnerProductIntegrable
import Langlands.GroupScheme.Rational.NestedSplitComponentFactorization
import Langlands.GroupScheme.Rational.SplitComponentLeviPoints
import Langlands.GroupScheme.Lie.AdjointDeterminantReductiveStatement
import Langlands.Analysis.Meromorphic.ScalarIdentity

/-! # Pointwise descent for actual relative Eisenstein wave packets -/

noncomputable section
set_option autoImplicit false

open CategoryTheory AlgebraicGeometry MeasureTheory TensorProduct Set
open scoped CategoryTheory.MonObj TensorProduct Manifold

namespace Langlands.Global

open GroupScheme AdelicGroupPoints Langlands.Automorphic.GroupSchemeFunctions
  Langlands.Analysis.Meromorphic

variable {F : Type} [Field F] [NumberField F]
  {G P M U : GroupScheme (Spec (CommRingCat.of F))}
  {A : CommGroupScheme (Spec (CommRingCat.of F))}
  [IsAffine G.X.left] [IsAffine P.X.left]
  {p : P ⟶ G} [IsClosedImmersion p.hom.hom.left] {iU : U ⟶ P} {l : M ⟶ P}
  {K : Subgroup (AdelicGroupPoints F G)} (hK : IsIwasawaCompact p K)

private theorem eisensteinSeries_principal_mul {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsLeftInvariantUnder F G (parabolicQuotientSubgroup F p iU l) φ)
    (hl : IsRationalLeviSubgroup l) (hU : LeviSubgroup.IsGeometricUnipotentRadical iU)
    (lam : ComplexCharacterParameter F P) (x : rationalSubgroup F G) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ lam ((x : AdelicGroupPoints F G) * g) = hK.eisensteinSeries φ lam g := by
  let Γ := parabolicRationalSubgroup F p
  let e : ParabolicRationalCosets F p ≃ ParabolicRationalCosets F p :=
    { toFun := LeftCosetSpace.rightTranslate Γ x
      invFun := LeftCosetSpace.rightTranslate Γ x⁻¹
      left_inv := fun y => by rw [LeftCosetSpace.rightTranslate_mul, mul_inv_cancel,
        LeftCosetSpace.rightTranslate_one]
      right_inv := fun y => by rw [LeftCosetSpace.rightTranslate_mul, inv_mul_cancel,
        LeftCosetSpace.rightTranslate_one] }
  unfold IsIwasawaCompact.eisensteinSeries
  calc
    _ = ∑' c, hK.eisensteinTerm φ lam g (e c) := by
      apply tsum_congr
      intro c
      have hc : Quotient.mk _ (Quotient.out c * x) = e c := by
        change LeftCosetSpace.mk Γ (Quotient.out c * x) = LeftCosetSpace.rightTranslate Γ x c
        rw [← LeftCosetSpace.rightTranslate_mk, show LeftCosetSpace.mk Γ (Quotient.out c) = c
          from Quotient.out_eq c]
      rw [hK.eisensteinTerm_eq_of_representative hφ hl hU lam g (e c) _ hc]
      simp only [IsIwasawaCompact.eisensteinTerm, Subgroup.coe_mul, mul_assoc]
    _ = _ := e.tsum_eq _

private theorem eisensteinSeries_central_mul {φ : AdelicGroupPoints F G → ℂ}
    (q : AdelicGroupPoints F P)
    (hc : map F P G p q ∈ Subgroup.center (AdelicGroupPoints F G))
    (hφ : ∀ g, φ (map F P G p q * g) = φ g)
    (lam : ComplexCharacterParameter F P) (g : AdelicGroupPoints F G) :
    hK.eisensteinSeries φ lam (map F P G p q * g) =
      parameterPower F P lam q * hK.eisensteinSeries φ lam g := by
  have hterm (c : ParabolicRationalCosets F p) :
      hK.eisensteinTerm φ lam (map F P G p q * g) c =
        parameterPower F P lam q * hK.eisensteinTerm φ lam g c := by
    let x := (Quotient.out c : rationalSubgroup F G).val
    have hx : x * (map F P G p q * g) = map F P G p q * (x * g) := calc
      _ = (x * map F P G p q) * g := (mul_assoc _ _ _).symm
      _ = (map F P G p q * x) * g := congrArg (· * g) ((Subgroup.mem_center_iff.mp hc) x)
      _ = _ := mul_assoc _ _ _
    change hK.parameterTwist φ lam (x * (map F P G p q * g)) =
      parameterPower F P lam q * hK.parameterTwist φ lam (x * g)
    simp only [hx, IsIwasawaCompact.parameterTwist, hφ, IsIwasawaCompact.heightPower,
      hK.height_map_mul, parameterPower, map_add, Complex.exp_add]
    ring
  unfold IsIwasawaCompact.eisensteinSeries
  rw [tsum_congr hterm, tsum_mul_left]

section Centre

variable [IsAffineHom G.X.hom] [LocallyOfFiniteType G.X.hom] [LocallyOfFiniteType P.X.hom]
  [IsAffine M.X.left] [LocallyOfFiniteType M.X.hom]
  {a : A.toGrp ⟶ M}

private theorem halfModulus_of_centralMap {S : CommGroupScheme (Spec (CommRingCat.of F))}
    [IsAffine S.toGrp.X.left] (j : S.toGrp ⟶ P) (hj : IsCentral j) (s : AdelicGroupPoints F S.toGrp) :
    parameterPower F P (halfModulusParameter F P) (map F S.toGrp P j s) = 1 := by
  rw [parameterPower, halfModulusParameter, complexParameterPairing_tmul, characterLog_map]
  change Complex.exp ((1 / 2 : ℂ) * ((characterLog F S.toGrp s)
    (characterRestrict j (Lie.adjointDeterminantCharacter P)) : ℂ)) = 1
  have hzero : characterLog F S.toGrp s 0 = 0 :=
    (show rationalCharacters S.toGrp →+ ℝ from characterLog F S.toGrp s).map_zero
  rw [Lie.adjointDeterminantCharacter_restrict_eq_zero_of_isCentral P j hj, hzero]
  simp

private theorem exists_splitCentre_preimage (r : ParabolicRootPresentation p l a)
    {φ : AdelicGroupPoints F G → ℂ}
    (hφ : IsSplitComponentEquivariant p l φ) {z : AdelicGroupPoints F G}
    (hz : z ∈ RestrictionSplitCentre.canonicalSubgroup F G) :
    ∃ q : AdelicGroupPoints F P, map F P G p q = z ∧ ∀ g, φ (z * g) = φ g := by
  let S := RestrictionSplitCentre.canonicalTorus F G
  let j := RestrictionSplitCentre.canonicalComponent F G
  have hj : IsSplitComponent j := RestrictionSplitCentre.isSplitComponent_canonicalComponent F G
  have hj0 : IsClosedSubgroup (𝟙 G) := by
    change IsClosedImmersion (𝟙 G.X.left)
    infer_instance
  obtain ⟨f, hf⟩ := r.exists_intermediateSplitComponentFactor (𝟙 G) hj0 (l ≫ p)
    (Category.comp_id _) j hj.isCentralSplitTorus.isCentral hj.isCentralSplitTorus.isSplitSubtorus.1
  have hf' : f ≫ a ≫ l ≫ p = j := by simpa only [Category.assoc] using hf
  rw [RestrictionSplitCentre.canonicalSubgroup_eq_imageSubgroup] at hz
  obtain ⟨s, hs, hsz⟩ := hz
  change AdelicGroupPoints F S.toGrp at s
  change map F S.toGrp G j s = z at hsz
  let y := map F A.toGrp M a (map F S.toGrp A.toGrp f s)
  have hy : y ∈ RestrictionSplitCentre.canonicalSubgroup F M := by
    rw [← RestrictionSplitCentre.imageSubgroup_eq_canonicalSubgroup r.isCompatible.splitComponent]
    refine ⟨map F S.toGrp A.toGrp f s, ?_, rfl⟩
    exact PositiveRealTorus.map_intrinsicSubgroup_le F S A (Additive.ofMul f) ⟨s, hs, rfl⟩
  let q := map F M P l y
  have hq' : q = map F S.toGrp P (f ≫ a ≫ l) s := by
    simp only [q, y, map_comp_apply_of_hom]
  have hq : map F P G p q = z := by
    rw [hq', ← map_comp_apply_of_hom, Category.assoc, Category.assoc, hf', hsz]
  have hcentral : IsCentral (f ≫ a ≫ l) := by
    have hp : Mono p.hom.hom := Over.mono_of_mono_left _
    apply IsCentral.of_comp (j := p) hp
    rw [Category.assoc, Category.assoc, hf']
    exact hj.isCentralSplitTorus.isCentral
  let : IsAffine S.toGrp.X.left := hj.isAffine
  have hmod : parameterPower F P (halfModulusParameter F P) q = 1 :=
    hq' ▸ halfModulus_of_centralMap (f ≫ a ≫ l) hcentral s
  refine ⟨q, hq, fun g => ?_⟩
  rw [← hq, hφ y hy, show map F M P l y = q from rfl, hmod, one_mul]

end Centre

section Continuation

variable [IsAffineHom G.X.hom] {a : A.toGrp ⟶ M} (r : ParabolicRootPresentation p l a)
  [Mono r.data.i.hom.hom.left] [Fintype (relativeWeylGroup r.data.i)]
  [Mono (CommGroupScheme.groupHom r.data.f).hom.hom.left]
  (hA : IsSplitTorus A.toGrp) (hT : IsSplitTorus r.data.T.toGrp)

omit [IsAffine P.X.left] in
private theorem parameterPower_entire [FiniteDimensional ℂ (ComplexCharacterParameter F P)]
    (q : AdelicGroupPoints F P) :
    IsMeromorphicInCoordinatesOn (fun lam => parameterPower F P lam q) univ := by
  refine ⟨inferInstance, fun n e => ?_⟩
  let L : ComplexCharacterParameter F P →ₗ[ℂ] ℂ :=
    { toFun := fun lam => complexParameterPairing F P lam (characterLog F P q)
      map_add' := fun x y => by rw [map_add, LinearMap.add_apply]
      map_smul' := fun t x => by rw [map_smul, LinearMap.smul_apply, RingHom.id_apply] }
  have hd : DifferentiableOn ℂ ((fun lam => parameterPower F P lam q) ∘ e) univ :=
    (Complex.differentiable_exp.comp
      (L.comp e.toLinearMap).toContinuousLinearMap.differentiable).differentiableOn
  have hhol := isHolomorphicOn_iff_differentiableOn_scalar.mpr hd
  refine ⟨isOpen_univ, dense_univ, hhol, fun x => ?_⟩
  refine ⟨univ, isOpen_univ, isConnected_univ, mem_univ x, 1, _,
    (differentiableOn_const (c := (1 : ℂ))).mdifferentiableOn,
    ⟨x, mem_univ x, one_ne_zero⟩, hhol, fun y _ => one_smul ℂ _⟩

omit [NumberField F] [IsAffine G.X.left] [IsAffine P.X.left]
  [IsClosedImmersion p.hom.hom.left] in
private theorem continuation_eqOn_regular (hG : IsConnectedReductive G) (R : ℝ)
    {f g : ComplexCharacterParameter F P → ℂ} {D : Set (ComplexCharacterParameter F P)}
    (hf : IsMeromorphicInCoordinatesOn f D) (hg : IsMeromorphicInCoordinatesOn g D)
    (hfg : ∀ lam ∈ D, r.IsRegularParameter hA hT R lam → f lam = g lam) : EqOn f g D := by
  let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := hf.1
  let e := (Module.finBasis ℂ (ComplexCharacterParameter F P)).equivFun.symm
  obtain ⟨lam, hlam⟩ := eisensteinRegularParameter F G P M A p l a r hA hT hG R
  have hne : {t | r.IsRegularParameter hA hT R (e t)}.Nonempty :=
    ⟨e.symm lam, by simpa using hlam⟩
  have h := hf.eqOn_of_eqOn_open hg e (isOpen_setOf_isRegularParameter r hA hT hG R e) hne
    (fun t ht => hfg (e t) ht.2.1 ht.1)
  simpa only [inter_self] using h

end Continuation

omit [NumberField F] [IsAffine P.X.left] in
private theorem imaginaryPairing (x : RealCharacterParameter F P) (H : RealCharacterDual F P) :
    complexParameterPairing F P (imaginaryParameter F P x) H =
      (realParameterPairing F P x H : ℂ) * Complex.I := by
  induction x using TensorProduct.inductionOn with
  | tmul t χ =>
    change ((t : ℂ) * Complex.I) * (H χ : ℂ) = ((t * H χ : ℝ) : ℂ) * Complex.I
    simp only [Complex.ofReal_mul]
    ring
  | add x y hx hy =>
    simp only [map_add, LinearMap.add_apply, Complex.ofReal_add, add_mul, hx, hy]

/-- The two left invariances on the holomorphy domain imply descent of the relative packet. -/
theorem relativeWavePacketDescent : RelativeWavePacketDescentStatement := by
  intro F _ _ G P M U A _ _ _ _ _ _ _ p _ iU l a r _ _ _ hA hT hG hU K hK N d rho hsmooth hcalc Θ
  let : LocallyOfFiniteType P.X.hom :=
    IsClosedSubgroup.locallyOfFiniteType (j := p) ‹IsClosedImmersion p.hom.hom.left›
  intro hΘ
  obtain ⟨n, e, k, v, c, E, D, hv, _, hD, hE, hagree, hformula⟩ := hΘ
  have hRel (x : Fin n → ℝ) : imaginaryParameter F P (e x : RealCharacterParameter F P) ∈ D :=
    hD ⟨_, rfl⟩
  have hRat : IsLeftInvariantUnder F G (rationalSubgroup F G) Θ := by
    intro z hz g
    rw [hformula]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨R, hR⟩ := hagree j
    have hEq := continuation_eqOn_regular r hA hT hG R (hE j (z * g)) (hE j g)
      (fun lam _ hlam => by
        rw [hR lam hlam, eisensteinSeries_principal_mul hK (hv j).1.1
          r.isCompatible.levi hU lam ⟨z, hz⟩ g])
    exact congrArg (c j x * ·) (hEq (hRel x))
  have hCentre : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalSubgroup F G) Θ := by
    intro z hz g
    have hj := RestrictionSplitCentre.isSplitComponent_canonicalRestrictionComponent F G
    have hc := RestrictionSplitCentre.subgroup_le_center F G _ _ hj.isCentralSplitTorus.isCentral hz
    rw [hformula]
    apply integral_congr_ae
    apply Filter.Eventually.of_forall
    intro x
    apply Finset.sum_congr rfl
    intro j _
    obtain ⟨q, hq, hφ⟩ := exists_splitCentre_preimage r (hv j).2.1 hz
    have hμ : realParameterPairing F P (e x : RealCharacterParameter F P) (characterLog F P q) = 0 := by
      have hx : (e x : RealCharacterParameter F P) ∈ relativeParameterSpace (F := F) p := (e x).2
      have hqz : map F P G p q ∈ RestrictionSplitCentre.canonicalSubgroup F G := hq ▸ hz
      simp only [relativeParameterSpace, Submodule.mem_iInf, LinearMap.mem_ker,
        LinearMap.flip_apply] at hx
      exact hx q hqz
    have hpow : parameterPower F P (imaginaryParameter F P (e x : RealCharacterParameter F P)) q = 1 := by
      rw [parameterPower, imaginaryPairing, hμ]
      simp
    obtain ⟨R, hR⟩ := hagree j
    let : FiniteDimensional ℂ (ComplexCharacterParameter F P) := (hE j g).1
    have hmer : IsMeromorphicInCoordinatesOn
        (fun lam => parameterPower F P lam q * E j lam g) D := by
      change IsMeromorphicInCoordinatesOn
        ((fun lam => parameterPower F P lam q) * fun lam => E j lam g) D
      simpa only [univ_inter] using (parameterPower_entire q).mul (hE j g)
    have hEq := continuation_eqOn_regular r hA hT hG R (hE j (z * g)) hmer
      (fun lam _ hlam => by
        rw [hR lam hlam, ← hq, eisensteinSeries_central_mul hK q (hq ▸ hc) (by rwa [hq])])
    apply congrArg (c j x * ·)
    calc
      _ = parameterPower F P (imaginaryParameter F P (e x : RealCharacterParameter F P)) q *
        E j (imaginaryParameter F P (e x : RealCharacterParameter F P)) g := hEq (hRel x)
      _ = _ := by rw [hpow, one_mul]
  have hinv : IsLeftInvariantUnder F G (RestrictionSplitCentre.canonicalRationalSubgroup F G) Θ :=
    LeftCosetSpace.invariant_sup _ Θ hCentre hRat
  exact ⟨hinv, LeftCosetSpace.out_mk_of_invariant _ Θ hinv⟩

end Langlands.Global

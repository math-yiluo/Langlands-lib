import Langlands.Global.AdelicSiegelExponentSubunitarity
import Langlands.Global.AdelicRelativeExponentAxis
import Langlands.Global.AdelicWeakConstantTermRestriction
import Langlands.Global.AdelicSplitComponentShifts

/-! # Strict subunitarity for a relative constant term with zero weak part -/

noncomputable section

open AlgebraicGeometry CategoryTheory
open scoped CategoryTheory.MonObj NNReal

set_option autoImplicit false

namespace Langlands.Global.StandardParabolicFamily

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

variable {F : Type} [Field F] [NumberField F] {G : GroupScheme (Spec (CommRingCat.of F))}
  [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
  (fam : StandardParabolicFamily F G)

local notation "Idx" => StandardIndex F G fam.i fam.ν
local notation "Fun" => (AdelicGroupPoints F G → ℂ)
local notation "Param(" J ")" => ComplexCharacterParameter F (fam.P J)
local notation "S(" J ")" => fam.positiveSplitComponent J
local notation "g(" J ")" => map F (fam.P J) G (fam.p J)
local notation "χ(" J ")" => parameterPower F (fam.P J)

/-- Ordinary split-component eigencharacters restrict along nested constant terms. The
normalized exponent of a nonzero component of the inner term consequently has unit modulus
on the larger parabolic's split component if the original parameter is unitary. -/
theorem innerExponent_unitary_on_outerSplitComponent
    (hδ : StandardNestedHalfModulusCompatibilityStatement) {Q J : Idx} (hQJ : Q ≤ J)
    {f : Fun} {lam : Param(J)} (hunit : parameterRealPart F (fam.P J) lam = 0)
    (hInv : fam.IsRadicalInvariant J f)
    (hEig : ∀ x : S(J), fam.splitComponentRepresentation J x f =
      χ(J) (lam + halfModulusParameter F (fam.P J)) x.val • f)
    {s : Finset (Param(Q))} {c : Param(Q) → Fun}
    (hSum : fam.constantTerm Q f = ∑ mu ∈ s, c mu)
    (hExp : ∀ mu ∈ s, fam.HasExponent Q mu (c mu))
    {mu : Param(Q)} (hmu : mu ∈ s) (hne : c mu ≠ 0)
    (a : S(J)) (b : S(Q)) (hab : g(Q) b.val = g(J) a.val) :
    ‖χ(Q) mu b.val‖ = 1 := by
  let z := χ(J) (lam + halfModulusParameter F (fam.P J)) a.val
  have ht : fam.splitComponentRepresentation Q b (fam.constantTerm Q f) = z • fam.constantTerm Q f := by
    change fam.unnormalizedAction Q b (fam.constantTerm Q f) = _
    have hshift : fam.unnormalizedAction Q b (fam.constantTerm Q f) =
        fam.unnormalizedAction J a (fam.constantTerm Q f) := by
      funext g
      simp only [unnormalizedAction, hab]
    rw [hshift, ← fam.constantTerm_unnormalizedAction_of_radicalInvariant hQJ a hInv]
    have hAe : fam.unnormalizedAction J a f = z • f := hEig a
    rw [hAe, fam.constantTerm_const_smul]
  have hz : ((fam.splitComponentRepresentation Q b - z • (1 : Module.End ℂ Fun)) ^ (1 : ℕ))
      (∑ p ∈ s, c p) = 0 := by
    rw [← hSum, pow_one, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, ht, sub_self]
  have hVal := fam.exponent_value_eq_of_shift_sub_pow_sum_eq_zero Q s c hExp b z 1 hz hmu hne
  dsimp only [z] at hVal
  rw [parameterPower_add, parameterPower_add] at hVal
  change χ(Q) mu b.val * fam.halfModulus Q b.val = χ(J) lam a.val * fam.halfModulus J a.val at hVal
  rw [hδ F G fam Q J hQJ a b hab] at hVal
  have hEqual := mul_right_cancel₀ (show fam.halfModulus J a.val ≠ 0 from Complex.exp_ne_zero _) hVal
  rw [hEqual, parameterPower, Complex.norm_exp, complexParameterPairing_re, hunit,
    map_zero, LinearMap.zero_apply, Real.exp_zero]

/-- If the smaller weak term is zero, every nonzero component of the next smaller ordinary
constant term is strictly subunitary along a Siegel split ray in the removed root direction. -/
theorem norm_parameterPower_lt_one_on_relativeSiegelRay
    (hδ : StandardNestedHalfModulusCompatibilityStatement)
    {T₀ : CommGroupScheme (Spec (CommRingCat.of F))} (j : T₀ ⟶ fam.T)
    (hsetup : IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j)
    {N d : ℕ} (rho : MatrixRepresentation G (Fin N)) (hN : 0 < N)
    (hsmooth : SmoothOfRelativeDimension d G.X.hom) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
    (J : Idx) (α : J.val)
    (r : intrinsicSubgroup F T₀)
    (hr : ∀ n : ℕ, r ^ n ∈ weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν 1)
    (hroot : characterLog F T₀.toGrp r.val (j ≫ α.val) ≠ 0) :
    let Q := fam.removeSimpleRoot J α.val
    ∀ (b : S(Q)), g(Q) b.val = positiveMap F G fam.T fam.i T₀ j r →
    ∀ {f : Fun} {lam : Param(J)}, parameterRealPart F (fam.P J) lam = 0 →
    fam.IsRadicalInvariant J f →
    (∀ a : S(J), fam.splitComponentRepresentation J a f =
      χ(J) (lam + halfModulusParameter F (fam.P J)) a.val • f) →
    fam.HasSiegelChamberGrowth j rho (fam.constantTerm Q f) →
    ∀ {s : Finset (Param(Q))} {c : Param(Q) → Fun},
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q f) s c →
    fam.unitaryExponentSum Q s c = 0 →
    ∀ mu ∈ s, c mu ≠ 0 → ‖χ(Q) mu b.val‖ < 1 := by
  classical
  let Q := fam.removeSimpleRoot J α.val
  change ∀ (b : S(Q)), _
  intro b hb f lam hunit hInv hEig hGrowth s c hDec hWeak mu hmu hne
  have hle := fam.norm_parameterPower_le_one_on_siegelRay j rho Q hδ hsetup hN hsmooth Kinf
    hDec hGrowth r 1 hr b hb mu hmu hne
  have hnon : parameterRealPart F (fam.P Q) mu ≠ 0 := by
    intro h
    exact hne (fam.eq_zero_of_sum_eq_zero_of_hasExponent Q _ c
      (fun p hp => hDec.exponent p (Finset.mem_filter.mp hp).1) hWeak mu
      (Finset.mem_filter.mpr ⟨hmu, h⟩))
  have hQJ : Q ≤ J := (fam.removeSimpleRoot_lt J α.property).le
  have hU := fam.innerExponent_unitary_on_outerSplitComponent hδ hQJ hunit hInv hEig
    hDec.sum_eq hDec.exponent hmu hne
  obtain ⟨x, hx, hxB⟩ := b.property
  let x' : intrinsicSubgroup F (fam.A Q) := ⟨x, hx⟩
  have hImg : map F (fam.A Q).toGrp G (fam.a Q ≫ fam.l Q ≫ fam.p Q) x =
      map F fam.T.toGrp G fam.i (map F T₀.toGrp fam.T.toGrp (CommGroupScheme.groupHom j) r.val) := by
    rw [← Category.assoc, map_comp_apply_of_hom]
    rw [show map F (fam.A Q).toGrp (fam.P Q) (fam.a Q ≫ fam.l Q) x = b.val from hxB, hb]
    exact map_comp_apply_of_hom _ _
  have hLog := fam.characterLog_splitComponent_restrict_of_same_image Q x _ hImg α.val
  rw [characterLog_map] at hLog
  have hAxis : characterLog F (fam.A Q).toGrp x'.val (fam.f Q ≫ α.val) ≠ 0 := by
    change characterLog F (fam.A Q).toGrp x (fam.f Q ≫ α.val) ≠ 0
    rw [hLog]
    exact hroot
  rw [← show map F (fam.A Q).toGrp (fam.P Q) (fam.a Q ≫ fam.l Q) x = b.val from hxB] at hle ⊢
  exact adelicRelativeExponentAxis F G fam J α mu x' hAxis hU hnon hle

end Langlands.Global.StandardParabolicFamily

namespace Langlands.Global

open GroupScheme AdelicGroupPoints AdelicSiegelFactors PositiveRealTorus

/-- Vanishing of the next smaller weak term forces strict normalized
subunitarity on the corresponding relative Siegel ray. -/
def AdelicSiegelRelativeStrictStatement : Prop :=
  StandardNestedHalfModulusCompatibilityStatement →
  ∀ (F : Type) [Field F] [NumberField F] (G : GroupScheme (Spec (CommRingCat.of F)))
    [IsAffineHom G.X.hom] [IsAffine G.X.left] [LocallyOfFiniteType G.X.hom]
    (fam : StandardParabolicFamily F G)
    (T₀ : CommGroupScheme (Spec (CommRingCat.of F))) (j : T₀ ⟶ fam.T),
    IsSiegelAlgebraicSetup F G fam.T fam.i fam.ν T₀ j →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N)), 0 < N →
    ∀ (hsmooth : SmoothOfRelativeDimension d G.X.hom) (Kinf : Subgroup (InfiniteAdelicGroupPoints F G))
      (J : StandardIndex F G fam.i fam.ν) (α : J.val) (r : intrinsicSubgroup F T₀),
    (∀ n : ℕ, r ^ n ∈ weakSimpleRootChamber F T₀ fam.T j G fam.i fam.ν 1) →
    characterLog F T₀.toGrp r.val (j ≫ α.val) ≠ 0 →
    let Q := fam.removeSimpleRoot J α.val
    ∀ (b : fam.positiveSplitComponent Q),
      map F (fam.P Q) G (fam.p Q) b.val = positiveMap F G fam.T fam.i T₀ j r →
    ∀ (f : AdelicGroupPoints F G → ℂ) (lam : ComplexCharacterParameter F (fam.P J)),
    parameterRealPart F (fam.P J) lam = 0 →
    fam.IsRadicalInvariant J f →
    (∀ a : fam.positiveSplitComponent J, fam.splitComponentRepresentation J a f =
      parameterPower F (fam.P J) (lam + halfModulusParameter F (fam.P J)) a.val • f) →
    fam.HasSiegelChamberGrowth j rho (fam.constantTerm Q f) →
    ∀ (s : Finset (ComplexCharacterParameter F (fam.P Q)))
      (c : ComplexCharacterParameter F (fam.P Q) → AdelicGroupPoints F G → ℂ),
    fam.IsAutomorphicExponentDecomposition hsmooth Kinf rho Q (fam.constantTerm Q f) s c →
    fam.unitaryExponentSum Q s c = 0 →
    ∀ mu ∈ s, c mu ≠ 0 → ‖parameterPower F (fam.P Q) mu b.val‖ < 1

theorem adelicSiegelRelativeStrict : AdelicSiegelRelativeStrictStatement := by
  intro hδ F _ _ G _ _ _ fam T₀ j hsetup N d rho hN hsmooth Kinf J α r hr hroot Q b hb
    f lam hunit hInv hEig hGrowth s c hDec hWeak mu hmu hne
  exact fam.norm_parameterPower_lt_one_on_relativeSiegelRay hδ j hsetup rho hN hsmooth Kinf
    J α r hr hroot b hb hunit hInv hEig hGrowth hDec hWeak mu hmu hne

end Langlands.Global

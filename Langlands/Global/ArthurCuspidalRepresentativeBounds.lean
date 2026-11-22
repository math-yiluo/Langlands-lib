import Langlands.Global.ArthurSiegelSetsStatement
import Langlands.Global.ArthurTruncationCuspidal
import Langlands.Global.AdelicWeylParameterEquivalence
import Langlands.GroupScheme.Rational.StandardLeviTorusFactor
import Langlands.GroupScheme.Rational.CharacterRestrictionProof
import Langlands.GroupScheme.Rational.CharacterRestrictionRational
import Langlands.GroupScheme.Rational.RelativeCharacterRootComplementBaseChange
import Langlands.Representation.LanglandsClassification.StandardParabolicDatum

/-! # Weighted cuspidal bounds on norm-one representatives -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj Pointwise

set_option autoImplicit false

namespace Langlands.Global.ArthurTruncation

open Langlands.GroupScheme Langlands.GroupScheme.RealTorusSpace AdelicGroupPoints
  ArthurParabolicSpaces Langlands.Automorphic.GroupSchemeFunctions RepresentationGrowth

/-- The minimal Levi has the maximal split torus as its split component, so
restriction from the minimal parabolic is a real linear bijection. -/
theorem bijective_restrictToTorus_minimal
    (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    (ν : cocharacterLattice T) (hG : IsConnectedReductive G) (hi : IsMaximalSplitTorus i)
    (hν : IsGenericCocharacter i ν) : Function.Bijective (restrictToTorus F i ν ∅) := by
  let P := Standard.parabolicScheme i ν ∅
  let M := Standard.leviScheme i ν ∅
  let p := Standard.parabolicHom i ν ∅
  let l := Standard.leviToParabolic i ν ∅
  let j := Standard.leviHom i ν ∅
  let hj := Standard.isRepresentedBy_leviHom i ν ∅
  let a := standardLeviTorusFactor i ν ∅ hj
  have ha : a ≫ j = i := standardLeviTorusFactor_comp i ν ∅ hj
  have hiM := hi.isMaximalSplitTorus_standardLeviTorusFactor i ν ∅ hj
    (Standard.isClosedSubgroup_leviHom i ν ∅)
  have hcent : IsCentral a := by
    apply isCentral_of_range_le_torusCentralizer hj.1
    rw [ha, hj.2, (standardParabolicEndpoints F G hG T i hi ν hν).2.1]
  have haSplit : IsSplitComponent a :=
    ⟨⟨hiM.1, hcent⟩, fun A t ht g hg => hiM.2 A t ht.1 g hg⟩
  have hl : IsRationalLeviSubgroup l := (Standard.parabolicStructure i ν hG hi hν ∅
    (Set.empty_subset _)).2.1
  obtain ⟨hinj, hindex⟩ := characterRestriction F M hl.isConnectedReductive T a haSplit
  have hlChar := hl.characterRestrict_bijective
  let incl := torusToParabolic F i ν ∅
  have hcomp : incl = a ≫ l := by
    apply (Standard.isRepresentedBy_parabolicHom i ν ∅).hom_ext
    change incl ≫ p = (a ≫ l) ≫ p
    rw [torusToParabolic_comp, Category.assoc, Standard.leviToParabolic_comp, ha]
  have hChar : characterRestrict incl = (characterRestrict a).comp (characterRestrict l) := by
    rw [hcomp, characterRestrict_comp]
  have hr : (characterRestrict incl).range = (characterRestrict a).range := by
    ext χ
    change (∃ ψ, characterRestrict incl ψ = χ) ↔ ∃ ψ, characterRestrict a ψ = χ
    simp only [hChar, AddMonoidHom.comp_apply]
    exact ⟨fun ⟨ψ, hψ⟩ => ⟨characterRestrict l ψ, hψ⟩, fun ⟨ψ, hψ⟩ => by
      obtain ⟨φ, rfl⟩ := hlChar.2 ψ
      exact ⟨φ, hψ⟩⟩
  have hiIncl : Function.Injective (characterRestrict incl) := hChar.symm ▸ hinj.comp hlChar.1
  let eℚ := rationalCharacterRestrictRatEquiv incl hiIncl (hr.symm ▸ hindex)
  let eℝ := (Langlands.LinearAlgebra.rationalRealTensorEquiv (rationalCharacters P)).symm.trans
    ((LinearEquiv.baseChange ℚ ℝ _ _ eℚ).trans
      (Langlands.LinearAlgebra.rationalRealTensorEquiv (characterLattice T)))
  have he : eℝ.toLinearMap = restrictToTorus F i ν ∅ := by
    apply AlgebraTensorModule.ext
    intro r χ
    change ((1 : ℚ) • r) ⊗ₜ[ℤ] characterRestrict incl χ = r ⊗ₜ[ℤ] characterRestrict incl χ
    rw [one_smul]
  rw [← he]
  exact eℝ.bijective

/-- The covering and rapid decay for Arthur truncation give bounds
of every nonnegative weight on representatives of the actual norm-one quotient. -/
def CuspidalRepresentativeBoundsReductionStatement : Prop :=
  ArthurSiegelSetsStatement.{u} →
  ∀ (F : Type u) [Field F] [NumberField F]
    (G : GroupScheme (Spec (CommRingCat.of F))) [IsAffineHom G.X.hom]
    [LocallyOfFiniteType G.X.hom]
    (T : CommGroupScheme (Spec (CommRingCat.of F))) (i : T.toGrp ⟶ G)
    [Mono i.hom.hom.left] (ν : cocharacterLattice T) (_hG : IsConnectedReductive G)
    (_hi : IsMaximalSplitTorus i), IsGenericCocharacter i ν →
    ∀ {N d : ℕ} (rho : MatrixRepresentation G (Fin N))
      (hsmooth : SmoothOfRelativeDimension d G.X.hom),
      0 < N → IsClosedSubgroup rho → ∀ f : FinitePlotSmoothRationalFunctions F G,
        HasAdelicUniformModerateGrowth F G rho hsmooth
          (adelicDifferentialCommutator_of_smooth F G hsmooth) f →
        HasCuspidalConstantTerms (evaluate F G f.val) →
        ∀ s : ℝ, 0 ≤ s → ∃ b : ℝ, ∀ q : NormOneRationalQuotient F G,
          ∃ x : normOneSubgroup F G, LeftCosetSpace.mk (rationalNormOneSubgroup F G) x = q ∧
            adelicHeight F G rho x.val ^ s * ‖evaluate F G f.val x.val‖ ≤ b

theorem cuspidalRepresentativeBoundsReduction : CuspidalRepresentativeBoundsReductionStatement.{u} := by
  intro hSiegel F _ _ G _ _ T i _ ν hG hi hν N d rho hsmooth hN hrho f hGrowth hCusp s _
  obtain ⟨K, hK, _, _, hArthur⟩ := hSiegel F G T i ν hG hi hν
  let hρ : Function.Bijective (restrictToTorus F i ν ∅) :=
    bijective_restrictToTorus_minimal F G T i ν hG hi hν
  obtain ⟨D, -⟩ := relativeRootReflectionExistence F G hG T i hi
  obtain ⟨⟨C, T₁, hC, hCover⟩, _, _, _, hDecay⟩ := hArthur D hρ
  obtain ⟨c, hc⟩ := hDecay rho hsmooth hN hrho
  let R := max (c + 1) 1
  let Tp : V T := R ⊗ₜ[ℤ] ν
  have hTp (β : characterLattice T) (hβ : β ∈ simpleRelativeRoots i ν) : c < eval T β Tp := by
    have hβ' : 0 < latticePairing T β ν := hβ.1.2
    have hpairInt : (1 : ℤ) ≤ latticePairing T β ν := by omega
    have hpair : 1 ≤ (latticePairing T β ν : ℝ) := by exact_mod_cast hpairInt
    have hR : 0 ≤ R := zero_le_one.trans (le_max_right _ _)
    rw [eval_tmul]
    exact lt_of_lt_of_le (lt_add_of_pos_right _ zero_lt_one)
      ((le_max_left _ _).trans (le_mul_of_one_le_right hR hpair))
  have hinv : IsLeftInvariantUnder F G (rationalSubgroup F G) (evaluate F G f.val) := by
    rintro _ ⟨a, rfl⟩ g
    exact f.val.val.property a g
  have ht := truncationCuspidal hG hi D hK hρ hν (evaluate F G f.val) hinv hCusp Tp
  have hdec := hc Tp hTp f hGrowth
  rw [ht] at hdec
  obtain ⟨n, hn⟩ := exists_nat_ge s
  obtain ⟨B, hB⟩ := hdec C hC T₁ n
  let scale : ℝ := (N : ℝ) ^ (∑ v : NumberField.InfinitePlace F, v.mult)
  refine ⟨B * scale ^ n, ?_⟩
  intro q
  obtain ⟨z, rfl⟩ := LeftCosetSpace.mk_surjective _ q
  let roots := simpleFinset ν hG hi
  obtain ⟨delta, hdelta, y, hy, heq⟩ := Set.mem_mul.mp ((hCover roots (Finset.mem_powerset.mpr le_rfl)).symm ▸
    (Set.mem_univ z.val))
  obtain ⟨r, -, rfl⟩ := hdelta
  obtain ⟨a, ha⟩ := r.property
  let aN := rationalNormOne F G a
  have haN : aN.val = r.val := ha
  have hy' : y = aN.val⁻¹ * z.val := by
    rw [haN, ← heq]
    change y = r.val⁻¹ * (r.val * y)
    rw [inv_mul_cancel_left]
  let x := aN⁻¹ * z
  have hx : x.val = y := hy'.symm
  refine ⟨x, LeftCosetSpace.mk_subgroup_mul _ ⟨aN⁻¹, ?_⟩ z, ?_⟩
  · exact (rationalNormOneSubgroup F G).inv_mem ⟨a, rfl⟩
  rw [hx]
  have hyN : y ∈ normOneSubgroup F G := hx ▸ x.property
  have hSource := adelicSourceNorm_pos F G rho hN y
  have hBound := hB y hy hyN
  have hw : adelicHeight F G rho y ^ s ≤ adelicHeight F G rho y ^ n := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (one_le_adelicHeight F G rho hN y) hn
  calc
    _ ≤ adelicHeight F G rho y ^ n * ‖evaluate F G f.val y‖ :=
      mul_le_mul_of_nonneg_right hw (norm_nonneg _)
    _ ≤ adelicHeight F G rho y ^ n *
        (B * adelicSourceNorm F G rho y ^ (-(n : ℝ))) :=
      mul_le_mul_of_nonneg_left hBound (pow_nonneg (zero_le_one.trans
        (one_le_adelicHeight F G rho hN y)) _)
    _ = B * scale ^ n := by
      rw [adelicHeight_eq_scalar_mul_sourceNorm, mul_pow, Real.rpow_neg hSource.le,
        Real.rpow_natCast]
      change (scale ^ n * adelicSourceNorm F G rho y ^ n) *
        (B * (adelicSourceNorm F G rho y ^ n)⁻¹) = _
      calc
        _ = (B * scale ^ n) *
            (adelicSourceNorm F G rho y ^ n * (adelicSourceNorm F G rho y ^ n)⁻¹) := by ring
        _ = _ := by rw [mul_inv_cancel₀ (pow_ne_zero _ hSource.ne'), mul_one]

end Langlands.Global.ArthurTruncation

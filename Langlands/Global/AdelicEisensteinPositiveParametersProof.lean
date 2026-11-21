import Langlands.Global.AdelicEisensteinPositiveParametersStatement
import Langlands.Global.AdelicEisensteinParameterDecay
import Langlands.Global.AdelicLogSection
import Langlands.GroupScheme.Rational.CharacterRestrictionFiniteIndex
import Langlands.GroupScheme.Rational.LeviRetraction
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.LinearAlgebra.TensorProduct.Basis

/-! # Logarithms and complex parameters of the positive Levi split component -/

noncomputable section

universe u

open CategoryTheory AlgebraicGeometry TensorProduct
open scoped CategoryTheory.MonObj TensorProduct

set_option autoImplicit false

namespace Langlands.Global

open Langlands.GroupScheme AdelicGroupPoints

private theorem complexParameterPairing_injective_of_splitRestriction
    {F : Type u} [Field F] [NumberField F]
    {P : GroupScheme (Spec (CommRingCat.of F))}
    {A : CommGroupScheme (Spec (CommRingCat.of F))}
    (f : A.toGrp ⟶ P) (hf : Function.Injective (characterRestrict f))
    (I : Type u) [Fintype I] (e : A.toGrp ≅ splitTorus (Spec (CommRingCat.of F)) I) :
    Function.Injective (complexParameterPairing F P) := by
  classical
  let b : Module.Basis I ℤ (rationalCharacters A.toGrp) :=
    (Pi.basisFun ℤ I).map (PositiveRealTorus.characterCoordinates F A I e).toIntLinearEquiv.symm
  let H (j : I) : RealCharacterDual F A.toGrp :=
    (Int.castAddHom ℝ).comp (b.coord j).toAddMonoidHom
  have hcoord (x : ComplexCharacterParameter F A.toGrp) (j : I) :
      complexParameterPairing F A.toGrp x (H j) = (b.baseChange ℂ).repr x j := by
    induction x using TensorProduct.inductionOn with
    | tmul s χ =>
      simp only [complexParameterPairing_tmul, Module.Basis.baseChange_repr_tmul]
      change s * (↑(↑(b.repr χ j) : ℝ) : ℂ) = b.repr χ j • s
      rw [Complex.ofReal_intCast, zsmul_eq_mul, mul_comm]
    | add x y hx hy =>
      simp only [map_add, LinearMap.add_apply, Finsupp.add_apply, hx, hy]
  let res := (characterRestrict f).toIntLinearMap.lTensor ℂ
  have hinj : Function.Injective res :=
    Module.Flat.lTensor_preserves_injective_linearMap _ hf
  have hmap (x : ComplexCharacterParameter F P) (h : RealCharacterDual F A.toGrp) :
      complexParameterPairing F A.toGrp (res x) h =
        complexParameterPairing F P x (realCharacterDualMap F A.toGrp P f h) := by
    induction x using TensorProduct.inductionOn with
    | tmul s χ => rfl
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  intro lam mu h
  apply hinj
  apply (b.baseChange ℂ).repr.injective
  ext j
  rw [← hcoord, ← hcoord, hmap, hmap, h]

private theorem parameterPower_injective_of_log_surjective
    {F : Type u} [Field F] [NumberField F]
    {P : GroupScheme (Spec (CommRingCat.of F))}
    (S : Subgroup (AdelicGroupPoints F P))
    (hlog : Function.Surjective (fun x : S => characterLog F P x.val))
    (hpair : Function.Injective (complexParameterPairing F P)) :
    Function.Injective (fun lam : ComplexCharacterParameter F P =>
      fun x : S => parameterPower F P lam x.val) := by
  intro lam mu h
  apply hpair
  ext H
  have heq (t : ℝ) :
      Complex.exp ((t : ℂ) * complexParameterPairing F P lam H) =
        Complex.exp ((t : ℂ) * complexParameterPairing F P mu H) := by
    obtain ⟨x, hx⟩ := hlog (t • H)
    change characterLog F P x.val = t • H at hx
    have hval := congrFun h x
    change Complex.exp (complexParameterPairing F P lam (characterLog F P x.val)) =
      Complex.exp (complexParameterPairing F P mu (characterLog F P x.val)) at hval
    rw [hx, map_smul, map_smul] at hval
    exact hval
  have hderiv (z : ℂ) :
      HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * z)) z (0 : ℝ) := by
    have hc := (Complex.hasDerivAt_exp ((0 : ℂ) * z)).comp (0 : ℂ)
      ((hasDerivAt_id (0 : ℂ)).mul_const z)
    simpa using hc.comp_ofReal (z := 0)
  have hleft := hderiv (complexParameterPairing F P lam H)
  rw [funext heq] at hleft
  exact hleft.unique (hderiv (complexParameterPairing F P mu H))

/-- The actual positive split subgroup detects every complex parabolic parameter. -/
theorem eisensteinPositiveParameters : EisensteinPositiveParametersStatement.{u} := by
  intro F _ _ G P M A _ p l a r
  have hinj := characterRestrict_splitComponent_injective r
  obtain ⟨_, _, proj, -, -, hproj, -⟩ :=
    r.isCompatible.levi.exists_unipotentRadical_retraction
  have hsurj : Function.Surjective (characterRestrict l) := by
    intro χ
    refine ⟨characterRestrict proj χ, ?_⟩
    rw [← AddMonoidHom.comp_apply, ← characterRestrict_comp, hproj, characterRestrict_id]
    rfl
  have hrange : (characterRestrict (a ≫ l)).range = (characterRestrict a).range := by
    ext χ
    change (∃ x, characterRestrict (a ≫ l) x = χ) ↔ ∃ y, characterRestrict a y = χ
    simp only [characterRestrict_comp, AddMonoidHom.comp_apply]
    constructor
    · rintro ⟨x, hx⟩
      exact ⟨characterRestrict l x, hx⟩
    · rintro ⟨y, rfl⟩
      obtain ⟨x, rfl⟩ := hsurj y
      exact ⟨x, rfl⟩
  let : (characterRestrict (a ≫ l)).range.FiniteIndex := hrange.symm ▸
    r.isCompatible.splitComponent.finiteIndex_range_characterRestrict
      r.isCompatible.levi.isConnectedReductive
  obtain ⟨I, hI, ⟨e⟩⟩ := r.isCompatible.splitComponent.isCentralSplitTorus.1.1
  let : Fintype I := Fintype.ofFinite I
  let S := PositiveRealTorus.imageSubgroup F A P (a ≫ l)
  have hlog : Function.Surjective (fun x : S => characterLog F P x.val) := by
    intro H
    let x := (PositiveRealTorus.positiveAmbientLogEquiv F P A (a ≫ l) hinj I e).symm
      (Multiplicative.ofAdd H)
    refine ⟨⟨PositiveRealTorus.positivePointMap F P A (a ≫ l) x, x.val, x.property, rfl⟩, ?_⟩
    change characterLogHom F P (PositiveRealTorus.positivePointMap F P A (a ≫ l) x) =
      Multiplicative.ofAdd H
    rw [PositiveRealTorus.characterLogHom_positivePointMap F P A (a ≫ l) hinj I e]
    exact ContinuousMulEquiv.apply_symm_apply _ _
  exact ⟨hlog, parameterPower_injective_of_log_surjective S hlog
    (complexParameterPairing_injective_of_splitRestriction (a ≫ l) hinj I e)⟩

end Langlands.Global

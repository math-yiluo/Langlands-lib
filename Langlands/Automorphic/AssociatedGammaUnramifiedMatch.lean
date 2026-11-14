import Langlands.Automorphic.AssociatedGammaArithmeticTwist
import Langlands.Automorphic.AssociatedGammaTensorEuler
import Langlands.Global.Factors.HeckeFiniteEpsilon
import Langlands.Global.Factors.RelativeWeilLocalEulerBridge
import Langlands.Correspondence.BaseGeometricResidue
import Langlands.Correspondence.CharacterSumEuler
import Langlands.Correspondence.RankOneArithmeticLFactor
import Langlands.LocalFactor.Euler.Scaling
import Langlands.Automorphic.LocalDeterminantCharacter
import Langlands.Weil.Local.Assembly

/-!
# Arithmetic pair L-factors at unramified places

At a finite place `z` where the local components of `S`, `S'` along `ι` and the Hecke
character `χ` are unramified, the arithmetic pair L-factor of `((χ ∘ τ_F) ⊗ S, S')` is
`1 / ∏_(a, b) (1 - χ_z(ϖ) a b X)` over the Frobenius eigenvalues `a` of `S` and `b` of `S'`.
-/

noncomputable section

set_option autoImplicit false

open Polynomial

universe u uV uE

namespace Langlands.ClassField.Global.RelativeWeilGroup

open Langlands.Global Langlands.Global.CompletionPadic
open Langlands.Global.FunctionalEquationComparison Langlands.Global.AdelicFunctoriality

variable {c : FundamentalClass.ClassFamily.{u}} {F E : Type u} [Field F] [NumberField F]
  [Field E] [NumberField E] [Algebra F E] [IsGalois F E] {z : FinitePlace F}

/-- The multiplicative conductor is unchanged by transport along an equality of topologies. -/
theorem multiplicativeConductor_quasicharacterCongr {p : ℕ} [Fact p.Prime]
    {K : PadicField.{u} p} {T₁ T₂ : K.TopologicalData} (hT : T₁ = T₂)
    (χ : @HarmonicAnalysis.Quasicharacter K.Carrier _ T₁.topology) :
    T₂.multiplicativeConductor (LocalFactor.PadicAbelian.quasicharacterCongr
        (congrArg PadicField.TopologicalData.topology hT) χ) =
      T₁.multiplicativeConductor χ := by
  subst hT
  rfl

/-- The transported local component of an unramified Hecke character is unramified. -/
theorem isUnramifiedCharacter_quasicharacterBase (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z) :
    letI := (padicField z).canonicalTopologicalData.topology
    (padicField z).canonicalTopologicalData.IsUnramifiedCharacter
      (quasicharacterBase z (χ.finiteComponent z)).toMonoidHom := by
  intro _
  apply (Correspondence.isUnramifiedQuasicharacter_iff_isUnramifiedCharacter _ _).mp
  intro u hu
  have hu' : (topologicalData z).discreteValuation (u : FiniteCompletion F z) = 1 := by
    rw [topologicalData_eq_canonicalTopologicalData z]
    exact hu
  apply hχ u
  constructor
  · apply (HeckeFunctionalEquation.mem_localIntegers_iff z _).mp
    exact ((topologicalData z).mem_integers_iff_discreteValuation_le_one
      (u : FiniteCompletion F z)).mpr hu'.le
  · apply (HeckeFunctionalEquation.mem_localIntegers_iff z _).mp
    apply ((topologicalData z).mem_integers_iff_discreteValuation_le_one
      (↑u⁻¹ : FiniteCompletion F z)).mpr
    simpa only [Units.val_inv_eq_inv_val, map_inv₀, hu', inv_one] using
      (le_refl (1 : WithZero (Multiplicative ℤ)))

/-- The local twist character of an unramified Hecke character is trivial on inertia. -/
theorem localTwistCharacter_inertia
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z) :
    ∀ w ∈ Weil.Local.localInertia (padicField z), localTwistCharacter eC χ w = 1 :=
  (Correspondence.weilCharacter_trivial_on_inertia_iff _
    (Correspondence.isGeometricReciprocity_of_isBaseReciprocity _ _ _
      (Correspondence.baseReciprocityCandidate_spec _ eC) heC) _).mpr
    (isUnramifiedCharacter_quasicharacterBase χ hχ)

/-- At the geometric Frobenius, the local twist character of an unramified Hecke character is
its value at a uniformizer. -/
theorem localTwistCharacter_localGeometricFrobenius
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z) :
    localTwistCharacter eC χ (Weil.Local.localGeometricFrobenius (padicField z)) =
      χ.finiteUniformizerValue z := by
  have h := Correspondence.weilCharacter_localGeometricFrobenius
    (Correspondence.isGeometricReciprocity_of_isBaseReciprocity _ _ _
      (Correspondence.baseReciprocityCandidate_spec _ eC) heC)
    (isUnramifiedCharacter_quasicharacterBase χ hχ)
  exact h

/-- Scaling the roots of a product of linear factors. -/
theorem prod_linear_comp_C_mul_X (s : Multiset ℂ) (a : ℂ) :
    ((s.map fun r => 1 - C r * X).prod).comp (C a * X) =
      ((s.map (a * ·)).map fun r => 1 - C r * X).prod := by
  rw [multiset_prod_comp, Multiset.map_map, Multiset.map_map]
  congr 1
  refine Multiset.map_congr rfl fun r _ => ?_
  simp only [Function.comp_apply, sub_comp, one_comp, mul_comp, C_comp, X_comp, C_mul]
  ring

/-- **Unramified arithmetic pair L-factor** of a twisted pair. -/
theorem arithmeticPairLFactor_twist_of_unramified
    {S S' : FiniteRepresentation.{0, u, uV} ℂ (RelativeWeilGroup c F E)}
    {w : FinitePlacesAbove E z} {e : LocalFactor.RankOne.ReciprocityCandidate
      (towerPadicField z w.1)}
    {ι : Weil.Local.localWeilGroup (padicField z) →ₜ* RelativeWeilGroup c F E}
    (hι : IsLocalRelativeWeilMap z w.1 e ι)
    (eC : LocalFactor.CommonClosure.ReciprocityFamily (padicField z))
    (heC : LocalFactor.CommonClosure.NormalizedReciprocity (padicField z) eC)
    (χ : HeckeCharacter F) (hχ : χ.IsUnramifiedAt z)
    (hS : (localComponent S ι).IsUnramified (Weil.Local.localInertia (padicField z)))
    (hS' : (localComponent S' ι).IsUnramified (Weil.Local.localInertia (padicField z)))
    (s t : Multiset ℂ)
    (hs : localEulerPolynomial S ι = (s.map fun r => 1 - C r * X).prod)
    (ht : localEulerPolynomial S' ι = (t.map fun r => 1 - C r * X).prod) :
    Correspondence.arithmeticPairLFactor (padicField z)
        (localPairClass (FiniteRepresentation.twist (reciprocityCharacter c F E χ) S) ι)
        (localPairClass S' ι) =
      (algebraMap ℂ[X] (RatFunc ℂ)
        ((((s.map ((χ.finiteUniformizerValue z : ℂ) * ·)) ×ˢ t).map
          fun x : ℂ × ℂ => 1 - C (x.1 * x.2) * X).prod))⁻¹ := by
  have : (Weil.Local.localInertia (padicField z)).Normal := Weil.Local.localInertia_normal _
  rw [localPairClass_twist_eq S ι _ (localTwistCharacter eC χ).toMonoidHom
    (reciprocityCharacter_apply_localMap hι eC heC χ)]
  set η := localTwistCharacter eC χ
  set A := WeilDeligneRepresentation.zeroMonodromy
    (Weil.Local.localNormCharacter (padicField z)).toMonoidHom
    (FiniteRepresentation.twist η.toMonoidHom (localComponent S ι))
  set A' := WeilDeligneRepresentation.zeroMonodromy
    (Weil.Local.localNormCharacter (padicField z)).toMonoidHom (localComponent S' ι)
  set T := WeilDeligneRepresentation.tensor A A'
  change (algebraMap ℂ[X] (RatFunc ℂ) (LocalFactor.WeilDeligne.eulerPolynomial T
    (Weil.Local.localInertia (padicField z))
    (Weil.Local.localGeometricFrobenius (padicField z))))⁻¹ = _
  have hN : T.monodromy = 0 := by
    change TensorProduct.map (0 : Module.End ℂ _) 1 + TensorProduct.map 1 (0 : Module.End ℂ _) = 0
    simp only [TensorProduct.map_zero_left, TensorProduct.map_zero_right]
    exact add_zero 0
  have hI : ∀ i : Weil.Local.localInertia (padicField z), T.representation i = 1 := by
    intro i
    change TensorProduct.map (((η i : ℂˣ) : ℂ) • (localComponent S ι).representation i)
      ((localComponent S' ι).representation i) = 1
    rw [hS i, hS' i, localTwistCharacter_inertia eC heC χ hχ i i.2, Units.val_one, one_smul,
      TensorProduct.map_one]
  rw [LocalFactor.WeilDeligne.eulerPolynomial_eq_of_monodromy_eq_zero
    (Weil.Local.localInertia (padicField z)) T hN hI]
  congr 2
  change LocalFactor.eulerPolynomial (TensorProduct.map
    (((η (Weil.Local.localGeometricFrobenius (padicField z)) : ℂˣ) : ℂ) •
      (localComponent S ι).representation (Weil.Local.localGeometricFrobenius (padicField z)))
    ((localComponent S' ι).representation
      (Weil.Local.localGeometricFrobenius (padicField z)))) = _
  rw [localTwistCharacter_localGeometricFrobenius eC heC χ hχ]
  refine Automorphic.Unramified.eulerPolynomial_tensorMap _ _ _ t ?_ ht
  rw [Henniart.Extension.eulerPolynomial_smul]
  change (localEulerPolynomial S ι).comp _ = _
  rw [hs, prod_linear_comp_C_mul_X]

end Langlands.ClassField.Global.RelativeWeilGroup

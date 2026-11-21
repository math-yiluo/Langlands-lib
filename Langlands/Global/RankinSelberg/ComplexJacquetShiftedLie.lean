import Langlands.Global.RankinSelberg.ComplexJacquetEvaluation
import Langlands.Representation.Archimedean.ComplexExponentDeformation

/-! # Jacquet evaluation on a Lie derivative along one exponent line -/

noncomputable section

open scoped Classical Matrix.Norms.Operator TensorProduct

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

open Langlands.Archimedean (characterOfParams characterOfParams_weight characterOfParams_exponent
  complexStandardLie unitaryCompact)
open Langlands.Archimedean.ComplexExponentDeformation (shiftAt shiftCharacter shiftEquiv shiftEquiv_apply
  multiplier_unitary transportedDerivative transportedDerivative_affine)
open Langlands.Archimedean.ComplexPrincipalSeriesExtension (eq_of_eqOn_unitary)
open Langlands.HarmonicAnalysis (AdditiveHaarMeasure)
open Langlands.LocalFactor.Archimedean (ComplexCharacterData)
open ComplexCompactProfileFamily (IsCompactProfile characterList compactRestriction
  compactRestriction_isCompactProfile standardSection_unitary)

variable {r : ℕ}
local notation "I" => Fin (r + 1)
local notation "P" => (I → ℂ)
local notation "G" => Langlands.GeneralLinear (r + 1) ℂ
local notation "U" => Matrix.unitaryGroup I ℂ
local notation "M" => Matrix I I ℂ
local notation "Std[" l "," p "]" => Automorphic.complexStandardKFinite (r + 1) (characterList l p)
local notation "KF" => Automorphic.complexStandardKFinite (r + 1)

/-- Vary one radial exponent by a complex increment. -/
def shiftJacquetExponent (p : P) (i : I) (z : ℂ) : P := p + z • Pi.single i 1

theorem differentiable_shiftJacquetExponent (p : P) (i : I) :
    Differentiable ℂ (shiftJacquetExponent p i) :=
  (differentiable_id.smul_const (Pi.single i 1 : P)).const_add p

private theorem shiftAt_characterList (l : I → ℤ) (p : P) (i : I) (z : ℂ) :
    shiftAt (characterList l p) i z = characterList l (shiftJacquetExponent p i z) := by
  apply List.ext_getElem
  · simp [characterList]
  · intro j hj hj'
    let k : I := ⟨j, by simpa only [characterList, List.length_ofFn] using hj'⟩
    simp only [shiftAt, List.getElem_modify, characterList, List.getElem_ofFn]
    change (if (i : ℕ) = (k : ℕ) then shiftCharacter (characterOfParams (l k) (p k)) z
      else characterOfParams (l k) (p k)) = characterOfParams (l k) (shiftJacquetExponent p i z k)
    by_cases hik : k = i
    · rw [hik]
      simp [shiftJacquetExponent, shiftCharacter, Langlands.Archimedean.ComplexBlock.twist]
    · have hne : (i : ℕ) ≠ (k : ℕ) := fun hn => hik (Fin.ext hn.symm)
      simp [shiftJacquetExponent, hne, Pi.single_eq_of_ne hik]

/-- Canonical evaluation of the transferred vector uses the original compact profile. -/
theorem continuedJacquet_eq_of_compactRestriction (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p q : P) (f : Std[l, p]) (v : Std[l, q])
    (h : compactRestriction v.val = compactRestriction f.val) :
    continuedJacquet μ a l q v = continuedJacquetFamilies μ a l p f q := by
  let ξ : {φ : U → ℂ // IsCompactProfile l φ} :=
    ⟨compactRestriction v.val, compactRestriction_isCompactProfile v.2⟩
  let η : {φ : U → ℂ // IsCompactProfile l φ} :=
    ⟨compactRestriction f.val, compactRestriction_isCompactProfile f.2⟩
  exact congrArg (fun ψ : {φ : U → ℂ // IsCompactProfile l φ} =>
    canonicalJacquetFamily μ a l ψ.val ψ.2 q) (show ξ = η from Subtype.ext h)

theorem continuedJacquet_transferProfile (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p q : P) (f : Std[l, p]) :
    continuedJacquet μ a l q (transferProfile l p q f) = continuedJacquetFamilies μ a l p f q :=
  continuedJacquet_eq_of_compactRestriction μ a l p q f _
    (funext (standardSection_unitary q (compactRestriction f.val)))

private theorem compactRestriction_Lie_shift (ds : List ComplexCharacterData) (hds : ds.length = r + 1)
    (i : I) (z : ℂ) (es : List ComplexCharacterData) (he : shiftAt ds i z = es)
    (X : M) (f : KF ds) (fz : KF es) (h : compactRestriction fz.val = compactRestriction f.val) :
    compactRestriction (complexStandardLie (r + 1) es (1 ⊗ₜ X) fz).val =
      compactRestriction (transportedDerivative ds hds i z X f).val := by
  subst es
  let E := shiftEquiv ds hds i z
  have hfz : fz = E f := by
    apply Subtype.ext
    refine eq_of_eqOn_unitary fz.2.1 (E f).2.1 ?_
    intro g hg
    let k : U := ⟨g.val, hg⟩
    have hk : Unitary.toUnits k = g := Units.ext rfl
    have H := congrFun h k
    change fz.val (Unitary.toUnits k) = f.val (Unitary.toUnits k) at H
    rw [hk] at H
    change fz.val g = (shiftEquiv ds hds i z f).val g
    rw [shiftEquiv_apply, multiplier_unitary i z hg, one_mul]
    exact H
  subst fz
  let F := transportedDerivative ds hds i z X f
  have hF : E F = complexStandardLie (r + 1) (shiftAt ds i z) (1 ⊗ₜ X) (E f) := by
    change E (E.symm (complexStandardLie (r + 1) (shiftAt ds i z) (1 ⊗ₜ X) (E f))) = _
    rw [E.apply_symm_apply]
  rw [← hF]
  funext k
  change (shiftEquiv ds hds i z F).val (Unitary.toUnits k) = F.val (Unitary.toUnits k)
  rw [shiftEquiv_apply, multiplier_unitary i z (show Unitary.toUnits k ∈ unitaryCompact ℂ (r + 1) from k.2), one_mul]

/-- At a shifted parameter the evaluated Lie derivative is the sum of two fixed-profile
families, with the second multiplied by the shift. -/
theorem continuedJacquet_shiftedLie_apply (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ)
    (l : I → ℤ) (p : P) (i : I) (X : M) (f : Std[l, p]) (z : ℂ) (g : G) :
    let q := shiftJacquetExponent p i z
    let ds := characterList l p
    let B := continuedJacquetFamilies μ a l p
    let L₀ := complexStandardLie (r + 1) ds (1 ⊗ₜ X)
    let L₁ := transportedDerivative ds (List.length_ofFn : ds.length = r + 1) i 1 X - L₀
    continuedJacquet μ a l q
        (complexStandardLie (r + 1) (characterList l q) (1 ⊗ₜ X) (transferProfile l p q f)) g =
      B (L₀ f) q g + z * B (L₁ f) q g := by
  intro q ds B L₀ L₁
  have hds : ds.length = r + 1 := List.length_ofFn
  have hcomp := compactRestriction_Lie_shift ds hds i z (characterList l q)
    (shiftAt_characterList l p i z) X f (transferProfile l p q f)
    (funext (standardSection_unitary q (compactRestriction f.val)))
  rw [continuedJacquet_eq_of_compactRestriction μ a l p q _ _ hcomp,
    transportedDerivative_affine hds i z X]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, map_add, map_smul, Pi.add_apply,
    Pi.smul_apply, smul_eq_mul, B, L₀, L₁]

/-- The canonical evaluation of the shifted right Lie derivative is holomorphic along
one radial exponent line, with the compact profile of the original vector held fixed. -/
def ComplexJacquetShiftedLieStatement : Prop :=
  ∀ (μ : AdditiveHaarMeasure ℂ) (a : ℂˣ) (l : I → ℤ) (p : P) (i : I)
    (X : M) (f : Std[l, p]) (g : G),
    Differentiable ℂ (fun z : ℂ =>
      let q := shiftJacquetExponent p i z
      continuedJacquet μ a l q
        (complexStandardLie (r + 1) (characterList l q) (1 ⊗ₜ X) (transferProfile l p q f)) g)

theorem complexJacquetShiftedLie : ComplexJacquetShiftedLieStatement (r := r) := by
  intro μ a l p i X f g
  let q := shiftJacquetExponent p i
  let ds := characterList l p
  have hds : ds.length = r + 1 := List.length_ofFn
  let B := continuedJacquetFamilies μ a l p
  let L₀ := complexStandardLie (r + 1) ds (1 ⊗ₜ X)
  let L₁ := transportedDerivative ds hds i 1 X - L₀
  have he (z : ℂ) : continuedJacquet μ a l (q z)
        (complexStandardLie (r + 1) (characterList l (q z)) (1 ⊗ₜ X) (transferProfile l p (q z) f)) g =
      B (L₀ f) (q z) g + z * B (L₁ f) (q z) g :=
    continuedJacquet_shiftedLie_apply μ a l p i X f z g
  have hd (v : Std[l, p]) : Differentiable ℂ (fun z => B v (q z) g) :=
    ((canonicalJacquetFamily_properties μ a l _ (compactRestriction_isCompactProfile v.2)).2.1 g).comp
      (differentiable_shiftJacquetExponent p i)
  change Differentiable ℂ (fun z : ℂ =>
    continuedJacquet μ a l (q z)
      (complexStandardLie (r + 1) (characterList l (q z)) (1 ⊗ₜ X) (transferProfile l p (q z) f)) g)
  simp_rw [he]
  exact (hd (L₀ f)).add (differentiable_id.mul (hd (L₁ f)))

end Langlands.Global.RankinSelbergGlobal.ComplexJacquetContinuation

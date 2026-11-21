import Langlands.Global.RankinSelberg.RealGodementCanonicalColumn
import Langlands.Global.RankinSelberg.RealGodementCanonicalEquivariance
import Langlands.Global.RankinSelberg.RealGodementReflectedPairs

/-! # Uniform canonical real Jacquet maps in the character standard modules -/

noncomputable section

open Langlands.Archimedean Langlands.GeneralLinear Langlands.LocalFactor.Archimedean
open Langlands.Global.RankinSelbergGlobal.ArchimedeanLocal
open Langlands.RankinSelberg (LeftUnipotentQuotient)
open MeasureTheory Set
open scoped Matrix.Norms.Operator

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

namespace Langlands.Global.RankinSelbergGlobal.RealGodement

open GramFormula RealGodementProfiles RealJacquetFrobenius RealUniformWhittakerDual

private local instance (n : ℕ) : MeasurableSpace (Langlands.GeneralLinear n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (Langlands.GeneralLinear n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (GeneralLinear.upperUnipotent n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (GeneralLinear.upperUnipotent n ℝ) := ⟨rfl⟩
private local instance (n : ℕ) : MeasurableSpace (LeftUnipotentQuotient n ℝ) := borel _
private local instance (n : ℕ) : BorelSpace (LeftUnipotentQuotient n ℝ) := ⟨rfl⟩

private def heightBounded (n M : ℕ) : Submodule ℂ (Langlands.GeneralLinear n ℝ → ℂ) where
  carrier := {F | ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖F g‖ ≤ C * realMatrixHeight g ^ M}
  zero_mem' := ⟨0, le_rfl, fun _ => by simp⟩
  add_mem' := by
    rintro F G ⟨C, hC, hF⟩ ⟨D, hD, hG⟩
    refine ⟨C + D, add_nonneg hC hD, fun g => ?_⟩
    rw [Pi.add_apply, add_mul]
    exact (norm_add_le _ _).trans (add_le_add (hF g) (hG g))
  smul_mem' := by
    rintro c F ⟨C, hC, hF⟩
    refine ⟨‖c‖ * C, mul_nonneg (norm_nonneg _) hC, fun g => ?_⟩
    rw [Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    exact mul_le_mul_of_nonneg_left (hF g) (norm_nonneg _)

variable {t : ℕ}
local notation "H" => Langlands.GeneralLinear (t + 2) ℝ
local notation "K" => unitaryCompact ℝ (t + 2)
local notation "P'" => (Fin (t + 2) → ℂ)
local notation "L'" => (Fin (t + 2) → Fin 2)

theorem spectralFrameVector_span_eq_top (D : RealQuotientMeasureData t) (p : L')
    (W : Submodule ℂ (K → ℂ)) [FiniteDimensional ℂ W]
    (hW : ∀ f ∈ W, ∀ k : K, (fun q : K => f (k * q)) ∈ W) (z : P') :
    Submodule.span ℂ (range fun C : SpectralSectionFamily D.groupHaar p W => C.frameVector D hW z) = ⊤ := by
  let : D.groupHaar.IsHaarMeasure := D.groupHaar_isHaar
  let : D.groupHaar.IsMulRightInvariant := (realMatrixHaar_symmetries D.groupHaar).1
  let A := spectralFrameSpace p W
  apply Submodule.map_injective_of_injective A.injective_subtype
  rw [Submodule.map_span, ← Set.range_comp, Submodule.map_top, Submodule.range_subtype]
  exact realGodementSpectralFrame D.groupHaar p W hW z

private theorem spectralFrameKFiniteLift_restrict (p : L') (W : Submodule ℂ (K → ℂ))
    [FiniteDimensional ℂ W] (hW : ∀ f ∈ W, ∀ k : K, (fun q : K => f (k * q)) ∈ W)
    (z : P') (f : Automorphic.realStandardKFinite (t + 2) (characterList p z))
    (hf : compactSectionRestriction f.val ∈ spectralFrameSpace p W) :
    spectralFrameKFiniteLift p W hW z ⟨compactSectionRestriction f.val, hf⟩ = f := by
  apply RealExponentDeformation.ext_of_eqOn
  intro g hg
  exact congrFun (compactSectionRestriction_spectralFrameKFiniteLift p W hW z ⟨_, hf⟩) ⟨g, hg⟩

private theorem exists_commonExponent_canonicalJacquet_step (D : RealQuotientMeasureData t)
    (a : ℝˣ) (p : L') (z : P')
    (hLower : IsRealUniformWhittakerIntertwiner t
      (characterList (fun i => p i.succ) (fun i => z i.succ)) (-a)
      (canonicalJacquetMap a (fun i => p i.succ) (fun i => z i.succ))) :
    ∃ M : ℕ, ∀ f : Automorphic.realStandardKFinite (t + 2) (characterList p z),
      ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖canonicalJacquetMap a p z f g‖ ≤ C * realMatrixHeight g ^ M := by
  let p' (i : Fin (t + 1)) := p i.succ
  let z' (i : Fin (t + 1)) := z i.succ
  obtain ⟨N, hN⟩ := hLower.2
  obtain ⟨M, hM⟩ := realGodementColumnGrowth t D a (p 0) (z 0) N
  refine ⟨M, fun f => ?_⟩
  obtain ⟨W, _, hFW, hW⟩ := exists_finite_leftStable_of_kFinite f.property.2
  let A := spectralFrameSpace p W
  let J := (canonicalJacquetMap a p z).comp (spectralFrameKFiniteLift p W hW z)
  let S := heightBounded (t + 2) M
  have hSpan := spectralFrameVector_span_eq_top D p W hW z
  have hImage : (⊤ : Submodule ℂ A) ≤ S.comap J := by
    rw [← hSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨C, rfl⟩
    let f' : Automorphic.realStandardKFinite (t + 1) (characterList p' z') :=
      ⟨standardSection z' C.lower, standardSection_mem C.lower_profile z'⟩
    let F := canonicalJacquetMap a p' z' f'
    have hF (Xs : List (Matrix (Fin (t + 1)) (Fin (t + 1)) ℝ)) :
        ∃ C : ℝ, 0 ≤ C ∧ ∀ g, ‖RealLocalWhittaker.iteratedRightDerivative t Xs F g‖ ≤
          C * realMatrixHeight g ^ N := by
      obtain ⟨f'', hf''⟩ := RealUniformWhittaker.exists_iteratedRightDerivative_eq_coefficient hLower.1 f' Xs
      rw [show RealLocalWhittaker.iteratedRightDerivative t Xs F = canonicalJacquetMap a p' z' f'' from hf'']
      exact hN f''
    obtain ⟨Q, hQ, hBound⟩ := hM F (canonicalJacquetMap_derivative_mem_regularFunctions a p' z' f') hF C.test
    have hEval := canonicalJacquetMap_standardSection a C.lower_profile z'
    refine ⟨Q, hQ, fun g => ?_⟩
    change ‖canonicalJacquetMap a p z (spectralFrameKFiniteLift p W hW z (C.frameVector D hW z)) g‖ ≤ _
    rw [realGodementCanonicalColumn D a p W hW C z g, ← hEval]
    exact hBound g
  have hfA : compactSectionRestriction f.val ∈ A :=
    mem_spectralFrameSpace_of_principalSeries hW f.property.1.1 hFW
  let x : A := ⟨compactSectionRestriction f.val, hfA⟩
  have hx : J x ∈ S := hImage (Submodule.mem_top : x ∈ ⊤)
  have he := spectralFrameKFiniteLift_restrict p W hW z f hfA
  change canonicalJacquetMap a p z (spectralFrameKFiniteLift p W hW z x) ∈ S at hx
  rw [show spectralFrameKFiniteLift p W hW z x = f from he] at hx
  exact hx

/-- The canonical real Jacquet map is a uniform Whittaker intertwiner in every
positive rank, with one polynomial exponent for every vector at the given exponents. -/
def RealGodementCanonicalModelStatement : Prop :=
  ∀ (r : ℕ) (a : ℝˣ) (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ),
    IsRealUniformWhittakerIntertwiner r (characterList p z) (-a) (canonicalJacquetMap a p z)

theorem realGodementCanonicalModel : RealGodementCanonicalModelStatement := by
  intro r
  induction r with
  | zero =>
    intro a p z
    have hz : z ∈ realSpectralChamber 0 := fun i => Fin.elim0 i
    let hDom := isStrictlyDominant_characterList p hz
    have he : canonicalJacquetMap a p z = additiveJacquetUniformLinear a hDom := by
      ext1 f
      exact (canonicalJacquetMap_agrees a p hz f).trans (additiveJacquetUniformLinear_apply a hDom f).symm
    rw [he]
    exact isRealUniformWhittakerIntertwiner_additiveJacquetUniformLinear a hDom
  | succ t ih =>
    intro a p z
    let D := (nonempty_realQuotientMeasureData t a).some
    exact ⟨realGodementCanonicalEquivariance a p z,
      exists_commonExponent_canonicalJacquet_step D a p z (ih a (fun i => p i.succ) (fun i => z i.succ))⟩

theorem canonicalJacquetMap_mem_uniformModel {r : ℕ} (a : ℝˣ)
    (p : Fin (r + 1) → Fin 2) (z : Fin (r + 1) → ℂ)
    (f : Automorphic.realStandardKFinite (r + 1) (characterList p z)) :
    canonicalJacquetMap a p z f ∈ realUniformWhittakerModel r (characterList p z) (-a) := by
  have h : LinearMap.range (canonicalJacquetMap a p z) ≤
      realUniformWhittakerModel r (characterList p z) (-a) :=
    le_iSup_of_le (canonicalJacquetMap a p z) (le_iSup_of_le (realGodementCanonicalModel r a p z) le_rfl)
  exact h ⟨f, rfl⟩

/-- Canonical upper coefficients and their actual duals are spanned by simultaneous
compact-column pairs at every inducing exponent vector. -/
theorem canonicalJacquetMap_reflectedPair_mem_span (D : RealQuotientMeasureData t) (a : ℝˣ)
    (p : L') (z : P') (f : Automorphic.realStandardKFinite (t + 2) (characterList p z)) :
    let cs := List.ofFn fun i : Fin (t + 1) => charData (p i.succ) (z i.succ)
    reflectedCoefficientPair (canonicalJacquetMap a p z f) ∈
      Submodule.span ℂ (compactReflectedColumnGenerators D a cs (p 0) (z 0)) := by
  intro cs
  obtain ⟨W, _, hFW, hW⟩ := exists_finite_leftStable_of_kFinite f.property.2
  let A := spectralFrameSpace p W
  let J := (canonicalJacquetMap a p z).comp (spectralFrameKFiniteLift p W hW z)
  let E := Submodule.span ℂ (compactReflectedColumnGenerators D a cs (p 0) (z 0))
  have hSpan := spectralFrameVector_span_eq_top D p W hW z
  have hImage : (⊤ : Submodule ℂ A) ≤ E.comap (reflectedCoefficientPair.comp J) := by
    rw [← hSpan]
    apply Submodule.span_le.mpr
    rintro _ ⟨C, rfl⟩
    let U := canonicalJacquetFamily a C.lower_profile (fun i => z i.succ)
    have hU : U ∈ realUniformWhittakerModel t (cs.map RealBlock.character) (-a) := by
      dsimp only [U]
      rw [← canonicalJacquetMap_standardSection a C.lower_profile]
      exact canonicalJacquetMap_mem_uniformModel a (fun i => p i.succ) (fun i => z i.succ) _
    have hUd : ArchimedeanLocal.dualFunction (t + 1) U ∈
        realUniformWhittakerModel t (dualCharacterBlocks cs) a := by
      simpa only [neg_neg] using realUniformWhittakerCharacterDual t cs List.length_ofFn (-a) U hU
    have he := funext (realGodementCanonicalColumn D a p W hW C z)
    apply Submodule.subset_span
    refine ⟨U, C.support, C.test, hU, hUd, C.support_compact, C.support_fullRank, C.test_zero, ?_⟩
    change (J (C.frameVector D hW z), ArchimedeanLocal.dualFunction (t + 2) (J (C.frameVector D hW z))) = _
    change J (C.frameVector D hW z) = _ at he
    rw [he]
    congr 1
    funext g
    exact godementLeadingFamily_reflection D a C.test hU hUd (p 0) g (z 0)
  have hfA : compactSectionRestriction f.val ∈ A :=
    mem_spectralFrameSpace_of_principalSeries hW f.property.1.1 hFW
  let x : A := ⟨compactSectionRestriction f.val, hfA⟩
  have hx : reflectedCoefficientPair (J x) ∈ E := hImage (Submodule.mem_top : x ∈ ⊤)
  have he := spectralFrameKFiniteLift_restrict p W hW z f hfA
  change reflectedCoefficientPair (canonicalJacquetMap a p z (spectralFrameKFiniteLift p W hW z x)) ∈ E at hx
  rw [show spectralFrameKFiniteLift p W hW z x = f from he] at hx
  exact hx

end Langlands.Global.RankinSelbergGlobal.RealGodement

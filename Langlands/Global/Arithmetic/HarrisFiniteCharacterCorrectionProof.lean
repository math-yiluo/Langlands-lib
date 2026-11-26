import Langlands.Automorphic.ConjugateSelfDualCriterion
import Langlands.Global.Arithmetic.HarrisCyclicDescentCorrectionStatement
import Langlands.Automorphic.HeckeTwist.ContragredientTwist
import Langlands.Automorphic.RankOneHeckeConjugateSelfDual
import Langlands.Automorphic.OperatorSubquotientCMDeterminant
import Langlands.Automorphic.OperatorDeterminantUnitary
import Langlands.Automorphic.OperatorLocalUnitaryForm
import Langlands.Automorphic.AssociatedPresentationComparison
import Langlands.Automorphic.CuspidalUnitaryForm
import Langlands.Automorphic.CuspidalSpectralDeterminantTwist
import Langlands.Automorphic.FiniteLocalDeterminantTransport
import Langlands.Automorphic.DeterminantTwistAdmissibility
import Langlands.Automorphic.AssociatedGammaAutomorphicTwist
import Langlands.Correspondence.SupercuspidalOperationRealization
import Langlands.Representation.Classification.UnitarySupercuspidalInductionTempered

/-! # Finite-character correction in Harris's Lemma 1.6: proof -/

noncomputable section

universe uE uV

set_option autoImplicit false

namespace Langlands.Automorphic

open Langlands.Global Langlands.Global.CMConjugation Langlands.Global.AdelicFunctoriality

section Generic

variable {V W Y Z : Type*} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup Y] [Module ℂ Y] [AddCommGroup Z] [Module ℂ Z]

/-- The pairing `B(y, x) = B₀(u⁻¹ y, w⁻¹ (e (u⁻¹ x)))` on `W`, built from a pairing
`B₀` between `V` and `Z` and linear equivalences `u : V ≃ W`, `e : V ≃ Y` and
`w : Z ≃ Y`. -/
def correctedPairing (B₀ : V →ₗ[ℂ] Z →ₗ[ℂ] ℂ) (u : V ≃ₗ[ℂ] W) (e : V ≃ₗ[ℂ] Y)
    (w : Z ≃ₗ[ℂ] Y) : W →ₗ[ℂ] W →ₗ[ℂ] ℂ :=
  (B₀ ∘ₗ u.symm.toLinearMap).compl₂ ((u.symm.trans e).trans w.symm).toLinearMap

variable (B₀ : V →ₗ[ℂ] Z →ₗ[ℂ] ℂ) (u : V ≃ₗ[ℂ] W) (e : V ≃ₗ[ℂ] Y) (w : Z ≃ₗ[ℂ] Y)

theorem correctedPairing_apply (y x : W) :
    correctedPairing B₀ u e w y x = B₀ (u.symm y) (w.symm (e (u.symm x))) := rfl

theorem correctedPairing_flip (x : W) :
    (correctedPairing B₀ u e w).flip x =
      B₀.flip (w.symm (e (u.symm x))) ∘ₗ u.symm.toLinearMap := rfl

/-- Group invariance of the corrected pairing: the operators `τc` and `τ` on `W` act
through `ρc` and `ρ` up to the scalars `b` and `a`, the twist `e` multiplies by
`c = a b`, and `w` intertwines `δc` with `γ`. -/
theorem correctedPairing_invariant (ρc ρ : V →ₗ[ℂ] V) (τc τ : W →ₗ[ℂ] W) (γ : Y →ₗ[ℂ] Y)
    (δc : Z →ₗ[ℂ] Z) (a b c : ℂ) (ha : a ≠ 0) (hb : b ≠ 0) (hc : c = a * b)
    (hτc : ∀ f, τc (u f) = b • u (ρc f)) (hτ : ∀ f, τ (u f) = a • u (ρ f))
    (he : ∀ f, γ (e f) = c • e (ρ f)) (hw : ∀ z, γ (w z) = w (δc z))
    (hB : ∀ y x, B₀ (ρc y) (δc x) = B₀ y x) (y x : W) :
    correctedPairing B₀ u e w (τc y) (τ x) = correctedPairing B₀ u e w y x := by
  have hc0 : c ≠ 0 := hc ▸ mul_ne_zero ha hb
  have h₁ : u.symm (τc y) = b • ρc (u.symm y) :=
    OperatorRealization.twist_symm_apply u ρc τc b hτc y
  have h₂ : u.symm (τ x) = a • ρ (u.symm x) :=
    OperatorRealization.twist_symm_apply u ρ τ a hτ x
  have h₃ : e (ρ (u.symm x)) = c⁻¹ • γ (e (u.symm x)) := by rw [he, inv_smul_smul₀ hc0]
  have h₄ : w.symm (γ (e (u.symm x))) = δc (w.symm (e (u.symm x))) :=
    inverse_operator w δc γ hw _
  have hs : b * (a * c⁻¹) = 1 := by
    rw [hc]
    field_simp
  rw [correctedPairing_apply, correctedPairing_apply]
  calc B₀ (u.symm (τc y)) (w.symm (e (u.symm (τ x))))
      = B₀ (b • ρc (u.symm y)) (w.symm (e (a • ρ (u.symm x)))) := by rw [h₁, h₂]
    _ = B₀ (b • ρc (u.symm y)) ((a * c⁻¹) • δc (w.symm (e (u.symm x)))) := by
        rw [e.map_smul, h₃, smul_smul, w.symm.map_smul, h₄]
    _ = (b * (a * c⁻¹)) • B₀ (ρc (u.symm y)) (δc (w.symm (e (u.symm x)))) := by
        rw [LinearMap.map_smul₂, map_smul, smul_smul]
    _ = B₀ (u.symm y) (w.symm (e (u.symm x))) := by rw [hB, hs, one_smul]

/-- Lie invariance of the corrected pairing, for operators intertwined without
scalars. -/
theorem correctedPairing_lie (σc μ : V →ₗ[ℂ] V) (τc τ : W →ₗ[ℂ] W) (γ : Y →ₗ[ℂ] Y)
    (δc : Z →ₗ[ℂ] Z) (hτc : ∀ f, τc (u f) = u (σc f)) (hτ : ∀ f, τ (u f) = u (μ f))
    (he : ∀ f, γ (e f) = e (μ f)) (hw : ∀ z, γ (w z) = w (δc z))
    (hB : ∀ y x, B₀ (σc y) x + B₀ y (δc x) = 0) (y x : W) :
    correctedPairing B₀ u e w (τc y) x + correctedPairing B₀ u e w y (τ x) = 0 := by
  have h₁ : u.symm (τc y) = σc (u.symm y) := inverse_operator u σc τc hτc y
  have h₂ : u.symm (τ x) = μ (u.symm x) := inverse_operator u μ τ hτ x
  have h₄ : w.symm (γ (e (u.symm x))) = δc (w.symm (e (u.symm x))) :=
    inverse_operator w δc γ hw _
  rw [correctedPairing_apply, correctedPairing_apply, h₁, h₂, ← he, h₄]
  exact hB _ _

theorem correctedPairing_flip_injective (hinj : Function.Injective B₀.flip) :
    Function.Injective (correctedPairing B₀ u e w).flip :=
  OperatorRealization.pairing_flip_injective B₀ u.symm ((u.symm.trans e).trans w.symm).symm
    hinj

theorem correctedPairing_flip_surjective (l : Module.Dual ℂ W) (z : Z)
    (hz : B₀.flip z = l ∘ₗ u.toLinearMap) :
    (correctedPairing B₀ u e w).flip (((u.symm.trans e).trans w.symm).symm z) = l :=
  OperatorRealization.pairing_flip_surjective B₀ u.symm ((u.symm.trans e).trans w.symm).symm
    l z hz

end Generic

section Pairing

open NumberField

variable {E : Type uE} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

local instance finiteCorrectionRationalGroup :
    AddCommGroup (RationalInvariantFunctions E n) := Submodule.addCommGroup _
local instance finiteCorrectionContinuousGroup :
    AddCommGroup (ContinuousRationalFunctions E n) := Submodule.addCommGroup _
local instance finiteCorrectionSmoothGroup :
    AddCommGroup (FiniteSmoothRationalFunctions E n) := Submodule.addCommGroup _
local instance finiteCorrectionFormsGroup :
    AddCommGroup (AutomorphicForms E n) := Submodule.addCommGroup _
local instance finiteCorrectionStableGroup :
    AddCommGroup (StableAutomorphicFunctions E n) := Submodule.addCommGroup _
local instance finiteCorrectionSpaceGroup (S : OperatorRealization E n) :
    AddCommGroup S.Space := Submodule.addCommGroup _

/-- The determinant character of `χ` at the CM conjugate of a finite adelic matrix
is the determinant character of `χᶜ` at the matrix. -/
theorem adelicDeterminant_ofFinite_finiteConj_eq (χ : HeckeCharacter E)
    (d : FiniteAdelicGL E n) :
    χ.adelicDeterminant n (AdelicGL.ofFinite E n (finiteConj E n d)) =
      χ.complexConj.adelicDeterminant n (AdelicGL.ofFinite E n d) := by
  rw [HeckeCharacter.adelicDeterminant_complexConj]
  congr 1
  change AdelicGL.pair E n 1 (finiteConj E n d) = adelicConj E n (AdelicGL.pair E n 1 d)
  rw [RankOneHecke.adelicConj_pair, map_one]

/-- The determinant character of `χ` at the CM conjugate of an element of the
standard compact subgroup at infinity is the determinant character of `χᶜ` there. -/
theorem adelicDeterminant_ofInfinite_compactConj_eq (χ : HeckeCharacter E)
    (k : standardInfiniteCompact E n) :
    χ.adelicDeterminant n (AdelicGL.ofInfinite E n (compactConj E n k).val) =
      χ.complexConj.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) := by
  rw [HeckeCharacter.adelicDeterminant_complexConj, compactConj_val]
  congr 1
  change AdelicGL.pair E n (infiniteConj E n k.val) 1 =
    adelicConj E n (AdelicGL.pair E n k.val 1)
  rw [RankOneHecke.adelicConj_pair, map_one]

namespace OperatorRealization

/-- **Conjugate self-duality of the corrected twist.** Let `D` realize the
contragredient of `S`, and let the CM image of `D` be the twist of `S` by
`(α · αᶜ) ∘ det` for a finite-order `α`. Then the actual twist of `S` by `α ∘ det`
is conjugate self-dual, with the pairing `correctedPairing B₀ u e w` for the
contragredient pairing `B₀`, the multiplication `u` by `α ∘ det`, the supplied
twist `e` and the CM image map `w` of `D`. -/
theorem determinantTwist_isConjugateSelfDual {S D : OperatorRealization E n}
    (α : HeckeCharacter E) (hα : α.HasFiniteOrder) (hD : D.IsContragredientOf S)
    (htw : IsFiniteOrderDeterminantTwist (α * α.complexConj) S D.complexConj) :
    (S.determinantTwist α hα).IsConjugateSelfDual := by
  obtain ⟨B₀, ⟨hd, hk, hX⟩, hB, hinj, hsurj⟩ := hD
  obtain ⟨-, e, he₁, he₂, he₃⟩ := htw
  have hfun_symm {l : Module.Dual ℂ S.Space} (hl : S.IsContragredientFunctional l) :
      (S.determinantTwist α hα).IsContragredientFunctional
        (l ∘ₗ (S.determinantTwistEquiv α hα).toLinearEquiv.symm.toLinearMap) :=
    isContragredientFunctional_comp_of_twisted _
      (fun d => ((α.adelicDeterminant n (AdelicGL.ofFinite E n d) : ℂˣ) : ℂ)⁻¹)
      (heckeDeterminantKernel α)
      (fun _ hd => (congrArg (·⁻¹) (adelicDeterminant_ofFinite_eq_one α hd)).trans inv_one)
      (fun d y => twist_apply_symm (S.determinantTwistEquiv α hα).toLinearEquiv
        (S.finiteRepresentation d) ((S.determinantTwist α hα).finiteRepresentation d) _
        (Units.ne_zero _) (fun f => S.determinantTwistEquiv_finite α hα d f) y)
      (fun k => ((α.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) : ℂˣ) : ℂ)⁻¹)
      (fun _k => inv_ne_zero (Units.ne_zero _))
      (fun k y => twist_apply_symm (S.determinantTwistEquiv α hα).toLinearEquiv
        (S.compactRepresentation k) ((S.determinantTwist α hα).compactRepresentation k) _
        (Units.ne_zero _) (fun f => S.determinantTwistEquiv_compact α hα k f) y) hl
  have hfun {l : Module.Dual ℂ (S.determinantTwist α hα).Space}
      (hl : (S.determinantTwist α hα).IsContragredientFunctional l) :
      S.IsContragredientFunctional
        (l ∘ₗ (S.determinantTwistEquiv α hα).toLinearEquiv.toLinearMap) :=
    isContragredientFunctional_comp_of_twisted _
      (fun d => ((α.adelicDeterminant n (AdelicGL.ofFinite E n d) : ℂˣ) : ℂ))
      (heckeDeterminantKernel α) (fun _ hd => adelicDeterminant_ofFinite_eq_one α hd)
      (fun d y => S.determinantTwistEquiv_finite α hα d y)
      (fun k => ((α.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) : ℂˣ) : ℂ))
      (fun _k => Units.ne_zero _)
      (fun k y => S.determinantTwistEquiv_compact α hα k y) hl
  refine ⟨correctedPairing B₀ (S.determinantTwistEquiv α hα).toLinearEquiv e
    D.complexConjEquiv.toLinearEquiv, ⟨?_, ?_, ?_⟩, ?_, ?_, ?_⟩
  · intro d y x
    exact correctedPairing_invariant B₀ _ e _
      (S.finiteRepresentation (finiteConj E n d)) (S.finiteRepresentation d)
      ((S.determinantTwist α hα).finiteRepresentation (finiteConj E n d))
      ((S.determinantTwist α hα).finiteRepresentation d)
      (D.complexConj.finiteRepresentation d) (D.finiteRepresentation (finiteConj E n d))
      (α.adelicDeterminant n (AdelicGL.ofFinite E n d) : ℂ)
      (α.complexConj.adelicDeterminant n (AdelicGL.ofFinite E n d) : ℂ)
      (determinantTwistScalar (α * α.complexConj) (AdelicGL.ofFinite E n d))
      (Units.ne_zero _) (Units.ne_zero _)
      (determinantTwistScalar_mul α α.complexConj (AdelicGL.ofFinite E n d))
      (fun f => (S.determinantTwistEquiv_finite α hα (finiteConj E n d) f).trans
        (congrArg (· • _) (congrArg Units.val (adelicDeterminant_ofFinite_finiteConj_eq α d))))
      (fun f => S.determinantTwistEquiv_finite α hα d f) (he₁ d)
      (fun z => D.complexConjEquiv_finite d z) (hd (finiteConj E n d)) y x
  · intro k y x
    exact correctedPairing_invariant B₀ _ e _
      (S.compactRepresentation (compactConj E n k)) (S.compactRepresentation k)
      ((S.determinantTwist α hα).compactRepresentation (compactConj E n k))
      ((S.determinantTwist α hα).compactRepresentation k)
      (D.complexConj.compactRepresentation k) (D.compactRepresentation (compactConj E n k))
      (α.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) : ℂ)
      (α.complexConj.adelicDeterminant n (AdelicGL.ofInfinite E n k.val) : ℂ)
      (determinantTwistScalar (α * α.complexConj) (AdelicGL.ofInfinite E n k.val))
      (Units.ne_zero _) (Units.ne_zero _)
      (determinantTwistScalar_mul α α.complexConj (AdelicGL.ofInfinite E n k.val))
      (fun f => (S.determinantTwistEquiv_compact α hα (compactConj E n k) f).trans
        (congrArg (· • _)
          (congrArg Units.val (adelicDeterminant_ofInfinite_compactConj_eq α k))))
      (fun f => S.determinantTwistEquiv_compact α hα k f) (he₂ k)
      (fun z => D.complexConjEquiv_compact k z) (hk (compactConj E n k)) y x
  · intro X y x
    exact correctedPairing_lie B₀ _ e _
      (S.lieAction (lieConj E n X)) (S.lieAction X)
      ((S.determinantTwist α hα).lieAction (lieConj E n X))
      ((S.determinantTwist α hα).lieAction X)
      (D.complexConj.lieAction X) (D.lieAction (lieConj E n X))
      (fun f => S.determinantTwistEquiv_differential α hα _ f)
      (fun f => S.determinantTwistEquiv_differential α hα _ f)
      (fun f => he₃ _ f) (fun z => complexConjEquiv_lieAction D X z)
      (hX (lieConj E n X)) y x
  · intro x
    rw [correctedPairing_flip]
    exact hfun_symm (hB _)
  · exact correctedPairing_flip_injective B₀ _ e _ hinj
  · intro l hl
    obtain ⟨z, hz⟩ := hsurj _ (hfun hl)
    exact ⟨_, correctedPairing_flip_surjective B₀ _ e _ l z hz⟩

end OperatorRealization

end Pairing

section Local

variable {F : Type uE} [Field F] [NumberField F]

local instance finiteCorrectionLocalRationalGroup (n : ℕ) :
    AddCommGroup (RationalInvariantFunctions F n) := Submodule.addCommGroup _
local instance finiteCorrectionLocalContinuousGroup (n : ℕ) :
    AddCommGroup (ContinuousRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteCorrectionLocalSmoothGroup (n : ℕ) :
    AddCommGroup (FiniteSmoothRationalFunctions F n) := Submodule.addCommGroup _
local instance finiteCorrectionLocalFormsGroup (n : ℕ) :
    AddCommGroup (AutomorphicForms F n) := Submodule.addCommGroup _
local instance finiteCorrectionLocalStableGroup (n : ℕ) :
    AddCommGroup (StableAutomorphicFunctions F n) := Submodule.addCommGroup _
local instance finiteCorrectionOperatorSpaceGroup {n : ℕ} (S : OperatorRealization F n) :
    AddCommGroup S.Space := Submodule.addCommGroup _
local instance finiteCorrectionLocalSpaceGroup {n : ℕ} {v : FinitePlace F}
    (L : LocalRealization F n v) : AddCommGroup L.Space := Submodule.addCommGroup _

/-- A finite-order determinant twist keeps every infinitesimal character, and hence
the regular algebraic type. -/
theorem OperatorRealization.determinantTwist_isRegularAlgebraic {n : ℕ}
    {S : OperatorRealization F n} (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder)
    (hS : S.IsRegularAlgebraic) : (S.determinantTwist χ hχ).IsRegularAlgebraic := by
  obtain ⟨c, hc, hSc⟩ := hS
  refine ⟨c, hc, fun z f => ?_⟩
  obtain ⟨g, rfl⟩ := (S.determinantTwistEquiv χ hχ).surjective f
  exact (S.determinantTwistEquiv_differential χ hχ _ g).trans
    ((congrArg (S.determinantTwistEquiv χ hχ) (hSc z g)).trans
      ((S.determinantTwistEquiv χ hχ).map_smul _ _))

/-- A supercuspidal local realization whose action is unitarizable is
square-integrable modulo the center. -/
theorem LocalRealization.isSquareIntegrable_of_isSupercuspidal {r : ℕ} {v : FinitePlace F}
    {A : LocalRealization F (r + 1) v} (hA : A.IsSupercuspidal)
    (hU : Langlands.IsUnitarizable A.representation) : A.IsSquareIntegrable := by
  obtain ⟨hI, hAd, c, hc⟩ := hA
  let K := CompletionPadic.padicField v
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  revert hc
  refine Quotient.inductionOn c ?_
  intro C hC
  change Correspondence.automorphicClassOf K C.toIrreducibleAdmissible =
    Correspondence.automorphicClassOf K (A.padicObject hI hAd) at hC
  obtain ⟨e⟩ := (Correspondence.automorphicClassOf_eq_iff K _ _).mp hC
  have hCU : Langlands.IsUnitarizable C.obj.representation :=
    (Langlands.isUnitarizable_iff_of_equiv e).mpr hU
  have hsq := Classification.unitarizableSupercuspidal_isSquareIntegrable K
    r.succPNat.pos C hCU
  exact ⟨hI, (PadicField.TopologicalData.isSquareIntegrable_iff_of_equiv e).mp hsq⟩

variable [CompactSpace (AdeleQuotient F)] {r : ℕ}

/-- The local components of a presentation of a unitarizable cuspidal realization
are unitarizable. -/
theorem CuspidalSpectralPresentation.localComponent_isUnitarizable
    {S : CuspidalOperatorRealization F r} (P : CuspidalSpectralPresentation.{uE, uV} S)
    (hU : S.realization.IsUnitarizable) (v : FinitePlace F) :
    Langlands.IsUnitarizable (P.localComponent v).representation :=
  (hU.localRestriction v).of_injective
    (S.realization.localSubspaceInclusion v _ (P.localComponent_le_full v))
    (S.realization.localSubspaceInclusion_injective v _ (P.localComponent_le_full v))

/-- The actual finite-order determinant twist of a presentation keeps a supercuspidal
local component supercuspidal. -/
theorem CuspidalSpectralPresentation.determinantTwist_localComponent_isSupercuspidal
    {S : CuspidalOperatorRealization F r} (P : CuspidalSpectralPresentation.{uE, uV} S)
    (χ : HeckeCharacter F) (hχ : χ.HasFiniteOrder) (v : FinitePlace F)
    (h : (P.localComponent v).IsSupercuspidal) :
    ((P.determinantTwist χ hχ).localComponent v).IsSupercuspidal := by
  obtain ⟨hI, hA, σ, hσ⟩ := h
  let L := P.localComponent v
  let L' := (P.determinantTwist χ hχ).localComponent v
  let e := P.determinantTwistLocalComponentEquiv χ hχ v
  have hI' : L'.IsIrreducible :=
    (Langlands.isIrreducible_iff_of_equiv e).mpr
      ((L.determinantTwist_isIrreducible_iff χ hχ).mpr hI)
  have hA' : L'.IsAdmissible :=
    (Langlands.isAdmissible_iff_of_equiv e).mpr
      ((L.determinantTwist_isAdmissible_iff χ hχ).mpr hA)
  let K := CompletionPadic.padicField v
  let ψ := CompletionPadic.quasicharacterBase v (χ.finiteComponent v)
  have htw : Correspondence.IsCharacterTwist K ψ (L.padicClass hI hA)
      (L'.padicClass hI' hA') := by
    refine ⟨L.padicObject hI hA, L'.padicObject hI' hA', rfl, rfl, ?_⟩
    change Nonempty ((Langlands.twist
      (Correspondence.determinantQuasiCharacter K r.succPNat ψ) L.representation).Equiv
        L'.representation)
    rw [CuspidalSpectralPresentation.determinantQuasiCharacter_quasicharacterBase]
    exact ⟨(L.determinantTwistRepresentationEquiv χ hχ).trans e.symm⟩
  have heq := (Correspondence.isCharacterTwist_iff_eq_twist K ψ
    (Correspondence.isOpen_ker_determinantQuasiCharacter K r.succPNat ψ) _ _).mp htw
  refine ⟨hI', hA', Correspondence.supercuspidalTwist K ψ σ, ?_⟩
  rw [heq, ← hσ]
  let : TopologicalSpace K.Carrier := K.canonicalTopologicalData.topology
  exact GeneralLinear.SupercuspidalClass.toSmoothDualClass_twist
    (Correspondence.determinantQuasiCharacter K r.succPNat ψ) _ _ σ

end Local

end Langlands.Automorphic

namespace Langlands.Global.Harris

open Langlands.Automorphic

/-- **Harris 1998, Lemma 1.6, finite determinant correction.** -/
theorem finiteCharacterConjugateDualCorrection :
    FiniteCharacterConjugateDualCorrectionStatement.{uE, uV} := by
  intro E _ _ _ _ r S Sdual v α hα hdual htw hunit hreg hsc
  refine ⟨?_, ?_, ?_⟩
  · rw [CuspidalOperatorRealization.isoClass_isConjugateSelfDual_iff]
    exact OperatorRealization.determinantTwist_isConjugateSelfDual α hα hdual htw
  · rw [CuspidalOperatorRealization.isoClass_isRegularAlgebraic_iff] at hreg ⊢
    exact OperatorRealization.determinantTwist_isRegularAlgebraic α hα hreg
  · obtain ⟨P, hP⟩ :=
      (CuspidalOperatorRealization.IsoClass.hasSupercuspidalComponent_iff S v).mp hsc
    have hU : (S.determinantTwist α hα).realization.IsUnitarizable :=
      (S.isUnitarizable_of_hasUnitaryCentralCharacter hunit).determinantTwist α hα
    refine (CuspidalOperatorRealization.IsoClass.hasSquareIntegrableComponent_iff _ v).mpr
      ⟨P.determinantTwist α hα, ?_⟩
    exact LocalRealization.isSquareIntegrable_of_isSupercuspidal
      (P.determinantTwist_localComponent_isSupercuspidal α hα v hP)
      ((P.determinantTwist α hα).localComponent_isUnitarizable hU v)

end Langlands.Global.Harris
